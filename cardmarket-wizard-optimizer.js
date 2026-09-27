// ==UserScript==
// @name         Cardmarket Shopping Wizard — Single-Seller Optimizer
// @namespace    cm-shopping-wizard-optimizer
// @version      2.1.0
// @description  Re-checks every seller from a Shopping Wizard result individually and tells you which basket to actually buy. Prices every option as a complete order, so fewer parcels can win.
// @author       you
// @match        https://www.cardmarket.com/*/Wants/ShoppingWizard/Results/*
// @run-at       document-idle
// @grant        none
// @noframes
// ==/UserScript==

/*
 * HOW IT WORKS
 * 1. Reads sellers, shipping and offered articles off the wizard results page.
 * 2. Sweeps each seller's offers filtered to your wants list, paging through them:
 *    a few requests per seller instead of one per card, then double-checks the
 *    result against the cards the wizard already proved that seller stocks.
 * 3. Scores line-ups as COMPLETE ORDERS — a basket is extended until it covers
 *    every reachable card, else it looks cheap by omitting expensive ones.
 * 4. Parking a card recalculates instantly from the stored scan.
 *
 * Politeness: randomised delay, backoff on 429/503, a hard stop when blocked, and a
 * local cache so re-runs and re-analysis cost nothing.
 */

(function () {
  'use strict';

  /*
   * Config
   */

  const CFG_KEY = 'cmSSO.cfg.v2';
  const CACHE_KEY = 'cmSSO.cache.v2';
  const SCAN_KEY = 'cmSSO.scan.v2';
  const EXCL_KEY = 'cmSSO.excluded.v1';
  const PARAM_KEY = 'cmSSO.searchParam.v1';

  const DEFAULTS = {
    concurrency: 2,        // parallel requests inside one seller
    minDelay: 350,         // ms, per request, randomised
    maxDelay: 900,
    cacheHours: 24,
    maxPagesPerCard: 2,    // offer pages to walk per seller+card
    minCondition: 'PO',    // PO = accept anything
    languages: ['English'], // [] = any language
    allowFoil: true,
    excludePlayset: true,
    excludeAltered: true,
    excludeSigned: true,
    fastScan: true,        // sweep each seller's wants-filtered offer pages instead of one request per card
    rankMode: 'hybrid',    // 'hybrid' = wizard cards + stock size, 'wizard' = wizard cards only
    maxCombo: 12,          // how many parcels the slider may reach
    defaultShipping: 1.70, // fallback when the wizard didn't show one
  };

  const CONDITIONS = ['MT', 'NM', 'EX', 'GD', 'LP', 'PL', 'PO'];
  const COND_NAMES = {
    'Mint': 'MT', 'Near Mint': 'NM', 'Excellent': 'EX', 'Good': 'GD',
    'Light Played': 'LP', 'Played': 'PL', 'Poor': 'PO',
  };
  const LANGUAGE_NAMES = [
    'English', 'French', 'German', 'Spanish', 'Italian', 'Simplified Chinese',
    'Japanese', 'Portuguese', 'Russian', 'Korean', 'Traditional Chinese',
  ];
  // Candidate query params for the seller offer search; probed once, then cached.
  const SEARCH_PARAM_CANDIDATES = ['name', 'searchString', 'productName', 'cardName'];

  const cfg = Object.assign({}, DEFAULTS, readJSON(CFG_KEY, {}));

  /*
   * Small utilities
   */

  function readJSON(key, fallback) {
    try { return JSON.parse(localStorage.getItem(key)) ?? fallback; }
    catch { return fallback; }
  }
  function writeJSON(key, val) {
    try { localStorage.setItem(key, JSON.stringify(val)); } catch { /* quota */ }
  }
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const jitter = () => cfg.minDelay + Math.random() * (cfg.maxDelay - cfg.minDelay);
  const euro = (n) => (n == null ? '—' : n.toFixed(2).replace('.', ',') + ' €');
  const pct = (n) => (n * 100).toFixed(0) + '%';

  function parsePrice(text) {
    if (!text) return null;
    const s = String(text).replace(/\u00a0/g, ' ');
    const m = s.match(/(\d{1,3}(?:\.\d{3})+|\d+),(\d{1,2})/);
    if (m) return parseFloat(m[0].replace(/\./g, '').replace(',', '.'));
    const m2 = s.match(/(\d+(?:\.\d{1,2})?)\s*€/);
    return m2 ? parseFloat(m2[1]) : null;
  }

  // "Mahadi, Emporium Master (V.1)" -> "mahadi emporium master"
  function normName(s) {
    return String(s || '')
      .toLowerCase()
      .normalize('NFD').replace(/[\u0300-\u036f]/g, '')
      .replace(/\(v\.?\s*\d+\)/g, '')
      .replace(/[^a-z0-9]+/g, ' ')
      .trim();
  }
  function searchableName(s) {
    // "Nissa, Vastwood Seer // Nissa, Sage Animist" finds nothing as one query;
    // search the first face and match the full name against the results.
    return String(s || '').replace(/\(v\.?\s*\d+\)/gi, '').split('//')[0].trim();
  }

  function condOK(code) {
    if (!code) return true;
    const want = CONDITIONS.indexOf(cfg.minCondition);
    const has = CONDITIONS.indexOf(code);
    return has === -1 || want === -1 || has <= want;
  }

  const [LANG_SEG, GAME_SEG] = location.pathname.split('/').filter(Boolean);

  /*
   * Cache
   */

  let cache = readJSON(CACHE_KEY, {});
  function filterHash() {
    // The wants list is part of the key: a sweep filtered to list A never saw
    // the cards on list B, and reusing it would report them as unavailable.
    const list = (typeof document !== 'undefined'
      && document.querySelector('#cmSSO-wantlist')?.value) || '';
    return [cfg.minCondition, cfg.languages.join('|'), cfg.allowFoil,
      cfg.excludePlayset, cfg.excludeAltered, cfg.excludeSigned, list].join('~');
  }
  function cacheGet(seller, cardKey) {
    const e = cache[`${seller}||${cardKey}||${filterHash()}`];
    if (!e) return null;
    if (Date.now() - e.t > cfg.cacheHours * 3600e3) return null;
    return e.units;
  }
  function cacheSet(seller, cardKey, units) {
    cache[`${seller}||${cardKey}||${filterHash()}`] = { t: Date.now(), units };
  }
  function cacheFlush() { writeJSON(CACHE_KEY, cache); }

  /*
   * Networking
   */

  let blockedStreak = 0;
  let aborted = false;

  async function httpGetDoc(url, attempt = 0) {
    if (aborted) throw new Error('aborted');
    let res;
    try {
      res = await fetch(url, {
        credentials: 'same-origin',
        headers: { 'Accept': 'text/html,application/xhtml+xml' },
        redirect: 'follow',
      });
    } catch (e) {
      if (attempt < 3) { await sleep(1500 * (attempt + 1)); return httpGetDoc(url, attempt + 1); }
      throw e;
    }

    if (res.status === 429 || res.status === 503 || res.status === 403) {
      blockedStreak++;
      if (attempt < 3) {
        const wait = 4000 * Math.pow(2, attempt) + Math.random() * 2000;
        ui.note(`Cardmarket asked us to slow down (${res.status}). Waiting ${Math.round(wait / 1000)}s…`, 'warn');
        await sleep(wait);
        return httpGetDoc(url, attempt + 1);
      }
      throw new Error(`blocked:${res.status}`);
    }
    if (!res.ok) throw new Error(`http:${res.status}`);

    const text = await res.text();
    if (text.length < 800 || /captcha|access denied|too many requests/i.test(text.slice(0, 4000))) {
      blockedStreak++;
      throw new Error('blocked:body');
    }
    blockedStreak = 0;
    return new DOMParser().parseFromString(text, 'text/html');
  }

  function sellerSearchUrl(seller, cardName, param, page) {
    const base = `${location.origin}/${LANG_SEG}/${GAME_SEG}/Users/${encodeURIComponent(seller)}/Offers/Singles`;
    const p = new URLSearchParams();
    p.set(param, searchableName(cardName));
    p.set('perSite', '50');
    if (page > 1) p.set('site', String(page));
    return `${base}?${p.toString()}`;
  }

  /*
   * Parsing: offer rows (works on seller offer pages and product pages)
   */

  /*
   * aria-label and data-bs-original-title are written by Bootstrap at runtime.
   * A fetched page ran no scripts, so language and foil markers live in
   * title / data-original-title / the onmouseover call. Read all of them.
   */
  function labelsOf(row) {
    const out = [];
    row.querySelectorAll('[aria-label],[data-bs-original-title],[data-original-title],[title],[onmouseover]')
      .forEach((el) => {
        ['aria-label', 'data-bs-original-title', 'data-original-title', 'title'].forEach((attr) => {
          const v = el.getAttribute(attr);
          if (v) out.push(v.trim());
        });
        const hover = el.getAttribute('onmouseover') || '';
        const m = hover.match(/showMsgBox\s*\(\s*this\s*,\s*[`'"]([^`'"]+)/);
        if (m) out.push(m[1].trim());
      });
    return out;
  }

  function parseOfferRows(doc) {
    let rows = [...doc.querySelectorAll('[id^="articleRow"], [id^="stockRow"]')];
    if (!rows.length) rows = [...doc.querySelectorAll('.article-row')];
    return rows.map((row) => {
      const link = row.querySelector('a[href*="/Products/Singles/"], a[href*="/Products/"]');
      const name = link ? link.textContent.trim() : '';

      const offerCell = row.querySelector('.col-offer, .price-container') || row;
      let price = parsePrice(offerCell.querySelector('.color-primary')?.textContent);
      if (price == null) price = parsePrice(offerCell.textContent);

      const condEl = row.querySelector('a[href*="CardCondition"] .badge, .article-condition .badge');
      const cond = condEl ? condEl.textContent.trim().toUpperCase() : null;

      const labels = labelsOf(row);
      const language = labels.find((l) => LANGUAGE_NAMES.includes(l)) || null;

      const countEl = row.querySelector('.item-count, .amount, [class*="item-count"]');
      const count = countEl ? (parseInt(countEl.textContent.trim(), 10) || 1) : 1;

      const has = (needle) => labels.some((l) => l.toLowerCase().includes(needle));

      // Harvest Cardmarket's own add-to-cart control instead of guessing at one.
      const form = row.querySelector('form[data-ajax-action], form[action]');
      const btn = form ? null : row.querySelector('[data-ajax-action]');
      let add = null;
      if (form || btn) {
        add = {
          action: (form || btn).getAttribute('data-ajax-action'),
          url: form ? form.getAttribute('action') : null,
          fields: {},
        };
        (form || row).querySelectorAll('input[name]').forEach((i) => { add.fields[i.name] = i.value; });
      }

      return {
        name, price, cond, language, count, add,
        foil: has('foil'),
        playset: has('playset'),
        altered: has('altered'),
        signed: has('signed'),
        articleId: ((row.id || '').match(/\d+/) || [null])[0],
        url: link ? link.getAttribute('href') : null,
      };
    }).filter((r) => r.price != null);
  }

  let langUnknown = 0;

  function offerAllowed(o) {
    if (cfg.excludePlayset && o.playset) return false;
    if (cfg.excludeAltered && o.altered) return false;
    if (cfg.excludeSigned && o.signed) return false;
    if (!cfg.allowFoil && o.foil) return false;
    if (!condOK(o.cond)) return false;
    if (cfg.languages.length) {
      // A row whose language we could not read is rejected rather than assumed:
      // guessing here would quietly put a foreign printing in your basket.
      if (!o.language) { langUnknown++; return false; }
      if (!cfg.languages.includes(o.language)) return false;
    }
    return true;
  }

  /*
   * Parsing: the wizard results page
   */

  function parseDl(dl) {
    const out = {};
    if (!dl) return out;
    const dts = [...dl.querySelectorAll('dt')];
    dts.forEach((dt) => {
      const dd = dt.nextElementSibling;
      if (dd && dd.tagName === 'DD') out[dt.textContent.trim().replace(/\s+/g, ' ')] = dd.textContent.trim();
    });
    return out;
  }

  function parseWizard() {
    const sellers = [...document.querySelectorAll('.detailed-result-card')].map((card) => {
      const a = card.querySelector('a[href*="/Users/"]');
      if (!a) return null;
      const username = a.textContent.trim();
      const loc = card.querySelector('[aria-label^="Item location:"]');
      const country = loc ? loc.getAttribute('aria-label').replace('Item location:', '').trim() : '';
      const dl = parseDl(card.querySelector('dl'));

      const shipping = parsePrice(Object.entries(dl).find(([k]) => /Shipping Cost/i.test(k))?.[1]);
      const articlesValue = parsePrice(Object.entries(dl).find(([k]) => /Articles Value/i.test(k))?.[1]);

      let articles = [...card.querySelectorAll('table tbody tr')].map((tr) => {
        const tds = tr.querySelectorAll('td');
        return {
          name: tr.querySelector('.card-name')?.textContent.trim() || '',
          qty: parseInt(tds[2]?.textContent.trim(), 10) || 1,
          price: parsePrice(tds[tds.length - 1]?.textContent),
        };
      }).filter((x) => x.name);

      // A narrow screen may only get the stacked rows instead of the table.
      if (!articles.length) {
        articles = [...card.querySelectorAll('[name^="articleRowMobile"]')].map((row) => {
          const name = row.querySelector('.text-truncate')?.textContent.trim() || '';
          const qty = parseInt((row.textContent.match(/(\d+)\s*x/) || [])[1], 10) || 1;
          const cells = row.querySelectorAll('.text-end');
          return { name, qty, price: parsePrice(cells[cells.length - 1]?.textContent) };
        }).filter((x) => x.name);
      }

      const delivery = card.querySelector('.shippingTime-info')?.textContent.trim();

      // "16342 Sales | 27074 Available items" — inventory size predicts coverage
      // better than the handful of articles the wizard happened to assign here.
      const badge = card.querySelector('.sell-count')?.getAttribute('data-bs-original-title') || '';
      const nums = badge.replace(/\u00a0/g, ' ').match(/[\d.,]+/g) || [];
      const toNum = (t) => (t ? parseInt(t.replace(/[.,]/g, ''), 10) : null);
      const sales = toNum(nums[0]);
      const stock = toNum(nums[1]);

      return { username, country, shipping, articlesValue, articles, sales, stock,
        delivery: delivery ? +delivery : null };
    }).filter(Boolean);

    const summary = parseDl(document.querySelector('#ShoppingWizardResult dl'));
    return {
      sellers,
      wizardTotal: parsePrice(Object.entries(summary).find(([k]) => /^Total/i.test(k))?.[1]),
      wizardShipping: parsePrice(Object.entries(summary).find(([k]) => /Shipping Cost/i.test(k))?.[1]),
      wizardCards: parsePrice(Object.entries(summary).find(([k]) => /Articles Value/i.test(k))?.[1]),
      wizardShipments: parseInt(Object.entries(summary).find(([k]) => /Shipments/i.test(k))?.[1], 10) || null,
      wizardWanted: parseInt(Object.entries(summary).find(([k]) => /Wanted Articles/i.test(k))?.[1], 10) || null,
    };
  }

  function wantedFromWizard(wiz) {
    const map = new Map();
    (wiz.sellers || []).forEach((s) => (s.articles || []).forEach((a) => {
      const key = normName(a.name);
      const cur = map.get(key) || { key, name: searchableName(a.name), qty: 0, wizardPrice: a.price };
      cur.qty += a.qty;
      cur.wizardPrice = Math.min(cur.wizardPrice ?? a.price, a.price ?? Infinity);
      map.set(key, cur);
    }));
    return [...map.values()].sort((a, b) => a.name.localeCompare(b.name));
  }

  function wantedFromText(text) {
    const map = new Map();
    text.split(/\r?\n/).forEach((raw) => {
      const line = raw.trim();
      if (!line || line.startsWith('//') || line.startsWith('#')) return;
      const m = line.match(/^(\d+)\s*[xX]?\s+(.*)$/);
      const qty = m ? parseInt(m[1], 10) : 1;
      let name = (m ? m[2] : line).replace(/\s*\([A-Za-z0-9]{2,6}\)\s*\d*\s*$/, '').trim();
      if (!name) return;
      const key = normName(name);
      const cur = map.get(key) || { key, name: searchableName(name), qty: 0, wizardPrice: null };
      cur.qty += qty;
      map.set(key, cur);
    });
    return [...map.values()].sort((a, b) => a.name.localeCompare(b.name));
  }

  function wantlistsFromDoc(doc) {
    const seen = new Set();
    const out = [];
    const add = (id, name) => {
      id = String(id || '').trim();
      if (!/^\d+$/.test(id) || seen.has(id)) return;
      seen.add(id);
      out.push({ id, name: String(name || '').trim() || `Wants list ${id}` });
    };

    // The filter panel is rendered client-side, so a plain fetch sees only its
    // props attribute — which is where the real list names live.
    doc.querySelectorAll('[data-props]').forEach((el) => {
      const raw = el.getAttribute('data-props');
      if (!raw || raw.indexOf('idWantslistOptions') === -1) return;
      try {
        const props = JSON.parse(raw);
        (props.options?.idWantslistOptions || []).forEach((o) => add(o.value, o.label));
      } catch { /* not the panel we wanted */ }
    });
    if (out.length) return out;

    // Already-hydrated page: read the picker itself.
    doc.querySelectorAll('select[name="idWantslist"] option')
      .forEach((o) => add(o.getAttribute('value'), o.textContent));
    if (out.length) return out;

    // Last resort: the Wants overview, whose links all read "View / Edit list",
    // so take the name from the surrounding row instead of the link text.
    const generic = /view|edit|delete|share|copy|list$/i;
    doc.querySelectorAll('a[href*="/Wants/"]').forEach((a) => {
      const m = (a.getAttribute('href') || '').match(/\/Wants\/(\d+)/);
      if (!m) return;
      let name = a.textContent.trim();
      if (!name || generic.test(name)) {
        const row = a.closest('tr, .row, li, .card');
        const head = row && row.querySelector('h1, h2, h3, h4, h5, h6, strong, b, td, .col');
        const text = (head ? head.textContent : '').replace(/\s+/g, ' ').trim();
        name = text && !generic.test(text) ? text.slice(0, 60) : '';
      }
      add(m[1], name);
    });
    return out;
  }

  async function fetchWantlists(sellerHint) {
    if (sellerHint) {
      try {
        const doc = await httpGetDoc(
          `${location.origin}/${LANG_SEG}/${GAME_SEG}/Users/${encodeURIComponent(sellerHint)}/Offers/Singles`);
        const lists = wantlistsFromDoc(doc);
        if (lists.length) return lists;
      } catch { /* fall through */ }
    }
    const doc = await httpGetDoc(`${location.origin}/${LANG_SEG}/${GAME_SEG}/Wants`);
    return wantlistsFromDoc(doc);
  }

  async function fetchWantlist(id) {
    const doc = await httpGetDoc(`${location.origin}/${LANG_SEG}/${GAME_SEG}/Wants/${id}`);
    const map = new Map();
    const rows = [...doc.querySelectorAll('[id^="wantsRow"], .table-body .row, tbody tr')];
    rows.forEach((row) => {
      const link = row.querySelector('a[href*="/Products/"]');
      if (!link) return;
      const name = link.textContent.trim();
      if (!name) return;
      const amtInput = row.querySelector('input[name*="amount" i], input[name*="Amount" i]');
      const qty = amtInput ? (parseInt(amtInput.value, 10) || 1) : 1;
      const key = normName(name);
      const cur = map.get(key) || { key, name: searchableName(name), qty: 0, wizardPrice: null };
      cur.qty += qty;
      map.set(key, cur);
    });
    return [...map.values()].sort((a, b) => a.name.localeCompare(b.name));
  }

  /*
   * Probe: find the query parameter the offer search uses
   */

  async function probeSearchParam(seller, knownCardName) {
    const cached = localStorage.getItem(PARAM_KEY);
    const order = cached ? [cached, ...SEARCH_PARAM_CANDIDATES.filter((p) => p !== cached)] : SEARCH_PARAM_CANDIDATES;
    const target = normName(knownCardName);

    for (const param of order) {
      try {
        const doc = await httpGetDoc(sellerSearchUrl(seller, knownCardName, param, 1));
        const rows = parseOfferRows(doc);
        if (rows.some((r) => normName(r.name) === target)) {
          localStorage.setItem(PARAM_KEY, param);
          return param;
        }
      } catch (e) {
        if (String(e.message).startsWith('blocked')) throw e;
      }
      await sleep(jitter());
    }
    return null;
  }

  /*
   * Scraping one seller × one card
   */

  async function offersFor(seller, want, param, force) {
    // force skips the cache: the recovery pass exists precisely because the
    // sweep already stored an empty result for this card, and asking the cache
    // again would just hand that same empty answer straight back.
    const cached = force ? null : cacheGet(seller, want.key);
    if (cached) return { units: cached, cached: true };

    const target = want.key;
    const units = [];
    for (let page = 1; page <= cfg.maxPagesPerCard; page++) {
      const doc = await httpGetDoc(sellerSearchUrl(seller, want.name, param, page));
      const rows = parseOfferRows(doc);
      rows.filter((r) => normName(r.name) === target && offerAllowed(r))
        .forEach((r) => { for (let i = 0; i < Math.min(r.count, 4); i++) units.push(r.price); });
      if (rows.length < 20) break;
      await sleep(jitter());
    }
    units.sort((a, b) => a - b);
    const keep = units.slice(0, Math.max(4, want.qty));
    cacheSet(seller, want.key, keep);
    return { units: keep, cached: false };
  }

  /*
   * Analysis engine
   *
   * Every basket is quoted as the cost of a COMPLETE order: the cards it
   * covers, its shipping, plus each missing card at the cheapest price any
   * scanned seller has for it, plus one extra parcel to go and get them.
   * Without that, a basket is rewarded for skipping expensive cards.
   */

  // A seller's offers narrowed to your wants list: many cards per page
  // instead of one request per card.
  function sellerWantlistUrl(seller, idWantslist, page) {
    const base = `${location.origin}/${LANG_SEG}/${GAME_SEG}/Users/${encodeURIComponent(seller)}/Offers/Singles`;
    const p = new URLSearchParams({ sortBy: 'name_asc', idWantslist: String(idWantslist) });
    if (page > 1) p.set('site', String(page));
    return `${base}?${p.toString()}`;
  }

  const SCANNED_MARK = '__scanned__';

  // Walk a seller's wants-filtered pages and keep every offer we care about.
  async function scanSellerViaWantlist(seller, wantlistId, wanted, onPage) {
    const byKey = new Map(wanted.map((w) => [w.key, w]));
    const found = new Map();     // key -> unit prices
    let seenFirst = null;
    let pages = 0;

    const PAGE_CAP = 120;   // a big seller filtered to a 120-card list runs long
    let hitCap = false;
    for (let page = 1; page <= PAGE_CAP && !aborted; page++) {
      if (page === PAGE_CAP) hitCap = true;
      const doc = await httpGetDoc(sellerWantlistUrl(seller, wantlistId, page));
      const rows = parseOfferRows(doc);
      pages = page;
      if (!rows.length) break;

      // Guard against a page that silently repeats the previous one
      const firstId = rows[0].articleId;
      if (firstId && firstId === seenFirst) break;
      seenFirst = firstId;

      rows.forEach((r) => {
        const key = normName(r.name);
        if (!byKey.has(key) || !offerAllowed(r)) return;
        const list = found.get(key) || [];
        for (let i = 0; i < Math.min(r.count, 4); i++) list.push(r.price);
        found.set(key, list);
      });

      if (onPage) onPage(page, rows.length);

      const next = doc.querySelector('a[data-direction="next"]');
      if (!next || !next.getAttribute('href')) break;
      if (rows.length < 15) break;    // short page = last page
      await sleep(jitter());
    }

    // Record misses too, so a later run knows this seller was checked.
    const out = {};
    wanted.forEach((w) => {
      const units = (found.get(w.key) || []).sort((a, b) => a - b);
      out[w.key] = units.slice(0, Math.max(4, w.qty));
      cacheSet(seller, w.key, out[w.key]);
    });
    cacheSet(seller, SCANNED_MARK, [1]);
    return { cards: out, pages, hitCap };
  }

  /*
   * Which sellers are worth scanning?
   *
   * Ranked from the wizard page alone, no requests. Three signals: how many of
   * your cards the wizard already sourced there, how big their stock is (the
   * best predictor of covering the rest), and how much they charge to ship.
   */

  const REACH_WEIGHT = 2.0;

  function rankSellers(wizSellers, mode) {
    const ships = wizSellers.map((s) => s.shipping ?? cfg.defaultShipping).sort((a, b) => a - b);
    const medShip = ships[Math.floor(ships.length / 2)] || cfg.defaultShipping;
    const how = mode || cfg.rankMode;

    return wizSellers.map((s) => {
      const articles = s.articles.length;
      const value = s.articlesValue || 0;
      const reach = Math.log10((s.stock || 0) + 1);
      const shipPenalty = (s.shipping ?? cfg.defaultShipping) / (medShip || 1);
      // 'wizard': trust only what the wizard sourced here.
      // 'hybrid': also credit a big catalogue, which predicts the cards the
      //           wizard happened to buy elsewhere. Measurably the better bet.
      const score = how === 'wizard'
        ? articles * 10 + value * 0.1 - shipPenalty
        : articles + REACH_WEIGHT * reach - shipPenalty;
      return { ...s, articleCount: articles, reach, score };
    }).sort((a, b) => b.score - a.score);
  }

  function buildModel(wanted, matrix, shipping, sellerNames) {
    const S = sellerNames.length, W = wanted.length;
    const units = [];       // units[card][seller] = sorted unit prices
    const bestUnit = [];    // cheapest unit anywhere in the scan
    const bestSeller = [];  // who has it that cheap
    const reachable = [];   // units obtainable from the scan (capped at qty)
    const ship = sellerNames.map((s) => shipping[s] ?? cfg.defaultShipping);

    for (let i = 0; i < W; i++) {
      units[i] = [];
      let best = Infinity, who = null, avail = 0;
      for (let j = 0; j < S; j++) {
        const u = matrix[sellerNames[j]]?.[wanted[i].key] || [];
        units[i][j] = u;
        avail += u.length;
        if (u.length && u[0] < best) { best = u[0]; who = sellerNames[j]; }
      }
      bestUnit[i] = best === Infinity ? null : best;
      bestSeller[i] = who;
      reachable[i] = Math.min(avail, wanted[i].qty);
    }

    /*
     * Scoring needs numbers only, so flatten into a price grid: one row per copy
     * of a card, one column per seller. Far cheaper than rebuilding per-seller
     * shopping lists for every combination tried.
     */
    const slotCard = [];
    for (let i = 0; i < W; i++) for (let c = 0; c < wanted[i].qty; c++) slotCard.push(i);
    const nSlots = slotCard.length;
    const priceMat = new Float64Array(nSlots * S).fill(Infinity);
    const slotOK = new Uint8Array(nSlots);
    let si = 0;
    for (let i = 0; i < W; i++) {
      for (let c = 0; c < wanted[i].qty; c++, si++) {
        let any = 0;
        for (let j = 0; j < S; j++) {
          const u = units[i][j];
          if (u.length > c) { priceMat[si * S + j] = u[c]; any = 1; }
        }
        slotOK[si] = any;
      }
    }
    const shipArr = Float64Array.from(ship);

    const wantedUnits = wanted.reduce((a, w) => a + w.qty, 0);
    const reachableUnits = reachable.reduce((a, b) => a + b, 0);
    const nobodyHas = wanted.map((w, i) => ({ ...w, i })).filter((w) => reachable[w.i] < w.qty);
    const medianShip = ship.length ? [...ship].sort((a, b) => a - b)[Math.floor(ship.length / 2)] : cfg.defaultShipping;
    const allQtyOne = wanted.every((w) => w.qty === 1);

    return { units, bestUnit, bestSeller, reachable, ship, wanted, sellerNames,
      wantedUnits, reachableUnits, nobodyHas, medianShip, allQtyOne, S, W,
      slotCard, nSlots, priceMat, slotOK, shipArr };
  }

  // Cost of a line-up, in numbers only — no allocation, no shopping lists.
  function scoreCombo(m, idx) {
    const S = m.S, P = m.priceMat, n = m.nSlots, k = idx.length;
    let cards = 0, covered = 0, missing = 0;
    const gaps = [];
    for (let sl = 0; sl < n; sl++) {
      if (!m.slotOK[sl]) continue;
      const base = sl * S;
      let best = Infinity;
      for (let t = 0; t < k; t++) { const v = P[base + idx[t]]; if (v < best) best = v; }
      if (best < Infinity) { cards += best; covered++; }
      else {
        missing++;
        const c = m.slotCard[sl];
        if (gaps.length < 3 && gaps.indexOf(c) === -1) gaps.push(c);
      }
    }
    let ship = 0;
    for (let t = 0; t < k; t++) ship += m.shipArr[idx[t]];
    return { cards, ship, total: cards + ship, covered, missing, gaps };
  }

  // Same scoring, but pretending one card was never on the list.
  function scoreWithout(m, idx, dropCard) {
    const S = m.S, P = m.priceMat, n = m.nSlots, k = idx.length;
    let cards = 0, missing = 0;
    for (let sl = 0; sl < n; sl++) {
      if (!m.slotOK[sl] || m.slotCard[sl] === dropCard) continue;
      const base = sl * S;
      let best = Infinity;
      for (let t = 0; t < k; t++) { const v = P[base + idx[t]]; if (v < best) best = v; }
      if (best < Infinity) cards += best; else missing++;
    }
    let ship = 0;
    for (let t = 0; t < k; t++) ship += m.shipArr[idx[t]];
    return { total: cards + ship, ship, missing };
  }

  // What a basket costs as it stands, and which cards it cannot supply.
  function evalCombo(m, idx) {
    let cardCost = 0, found = 0;
    const lines = idx.map(() => []);
    const gaps = [];

    for (let i = 0; i < m.W; i++) {
      const qty = m.wanted[i].qty;
      let got = 0;

      if (m.allQtyOne) {
        let best = Infinity, bestPos = -1;
        for (let p = 0; p < idx.length; p++) {
          const u = m.units[i][idx[p]];
          if (u.length && u[0] < best) { best = u[0]; bestPos = p; }
        }
        if (bestPos >= 0) { cardCost += best; found++; got = 1; lines[bestPos].push({ i, price: best }); }
      } else {
        const pool = [];
        idx.forEach((j, p) => m.units[i][j].forEach((price) => pool.push({ price, p })));
        pool.sort((a, b) => a.price - b.price);
        pool.slice(0, qty).forEach((u) => {
          cardCost += u.price; found++; got++;
          lines[u.p].push({ i, price: u.price });
        });
      }

      // Only count what the scan can supply from somewhere.
      const short = Math.max(0, Math.min(qty - got, m.reachable[i] - got));
      if (short > 0) gaps.push({ i, qty: short, price: m.bestUnit[i], seller: m.bestSeller[i] });
    }

    const ship = idx.reduce((a, j) => a + m.ship[j], 0);
    return {
      idx, sellers: idx.map((j) => m.sellerNames[j]), lines,
      cardCost, ship, total: cardCost + ship,
      found, coverage: m.reachableUnits ? found / m.reachableUnits : 0,
      gaps, missingUnits: gaps.reduce((a, g) => a + g.qty, 0),
    };
  }

  // Cheapest known price for everything a basket is missing — a valid floor on
  // what completing it can cost, used to prune the search.
  function completionFloor(m, r) {
    return r.total + r.gaps.reduce((a, g) => a + g.price * g.qty, 0);
  }

  // Extend a basket, cheapest-first, until it covers everything reachable.
  // Comparing completed orders is the only fair comparison: otherwise a basket
  // looks cheap simply by leaving expensive cards out.
  function completeOf(m, idx) {
    let cur = idx.slice();
    let score = scoreCombo(m, cur);
    const added = [];
    let guard = 0;
    while (score.missing && guard++ < m.S) {
      let best = null, bestJ = -1;
      for (let j = 0; j < m.S; j++) {
        if (cur.indexOf(j) !== -1) continue;
        const cand = cur.concat(j).sort((a, b) => a - b);
        const r = scoreCombo(m, cand);
        const sc = r.total + r.missing * MISS_PENALTY;
        if (!best || sc < best.sc) { best = { sc, cand, r }; bestJ = j; }
      }
      if (!best) break;
      added.push(m.sellerNames[bestJ]);
      cur = best.cand;
      score = best.r;
    }
    return { combo: evalCombo(m, cur), added };
  }

  // Drop any seller the basket no longer needs, then try single swaps.
  function polish(m, r) {
    let cur = r;
    let improved = true;
    while (improved) {
      improved = false;
      for (let p = 0; p < cur.idx.length; p++) {
        const cand = cur.idx.filter((_, q) => q !== p);
        if (!cand.length) continue;
        const alt = evalCombo(m, cand);
        if (alt.missingUnits <= cur.missingUnits && alt.total < cur.total) { cur = alt; improved = true; break; }
      }
    }
    for (let p = 0; p < cur.idx.length; p++) {
      for (let j = 0; j < m.S; j++) {
        if (cur.idx.includes(j)) continue;
        const cand = cur.idx.slice(); cand[p] = j;
        const alt = evalCombo(m, cand.sort((a, b) => a - b));
        if (alt.missingUnits <= cur.missingUnits && alt.total < cur.total) cur = alt;
      }
    }
    return cur;
  }

  function* combinations(n, k, start = 0, acc = []) {
    if (acc.length === k) { yield acc.slice(); return; }
    for (let i = start; i <= n - (k - acc.length); i++) {
      acc.push(i);
      yield* combinations(n, k, i + 1, acc);
      acc.pop();
    }
  }

  function nCk(n, k) {
    let r = 1;
    for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i;
    return r;
  }

  const comboKey = (r) => r.idx.join('-');

  /*
   * Exhaustive for small line-ups, then greedy with a swap pass for larger ones.
   * Only the handful we display get turned into full baskets.
   */
  const MISS_PENALTY = 1000;      // coverage first, price second

  function searchBaskets(m, maxK) {
    const S = m.S;
    const bestByIdx = [];         // parcel count -> cheapest full-coverage line-up
    const rank = (r) => r.total + r.missing * MISS_PENALTY;

    const consider = (idx, r) => {
      if (r.missing === 0) {
        const k = idx.length;
        if (!bestByIdx[k] || r.total < bestByIdx[k].total) bestByIdx[k] = { idx: idx.slice(), total: r.total };
      }
    };

    const EXH = Math.min(3, S);
    for (let k = 1; k <= EXH; k++) {
      for (const idx of combinations(S, k)) consider(idx, scoreCombo(m, idx));
    }

    // Grow one seller at a time, improving each size with single swaps.
    let idx = [];
    for (let k = 1; k <= Math.min(maxK, S); k++) {
      let add = null;
      for (let j = 0; j < S; j++) {
        if (idx.indexOf(j) !== -1) continue;
        const cand = idx.concat(j).sort((x, y) => x - y);
        const r = scoreCombo(m, cand);
        const sc = rank(r);
        if (!add || sc < add.sc) add = { sc, cand, r };
      }
      if (!add) break;
      idx = add.cand;

      let improved = true;
      let guard = 0;
      while (improved && guard++ < 6) {
        improved = false;
        let cur = rank(scoreCombo(m, idx));
        for (let p = 0; p < idx.length; p++) {
          for (let j = 0; j < S; j++) {
            if (idx.indexOf(j) !== -1) continue;
            const cand = idx.slice();
            cand[p] = j;
            cand.sort((x, y) => x - y);
            const sc = rank(scoreCombo(m, cand));
            if (sc < cur - 1e-9) { idx = cand; cur = sc; improved = true; }
          }
        }
      }
      consider(idx, scoreCombo(m, idx));

      // A smaller line-up may still cover everything — try dropping each seller.
      if (idx.length > 1) {
        for (let p = 0; p < idx.length; p++) {
          const cand = idx.filter((_, q) => q !== p);
          consider(cand, scoreCombo(m, cand));
        }
      }
    }

    const bestByK = [];
    const complete = [];
    bestByIdx.forEach((entry, k) => {
      if (!entry) return;
      const full = evalCombo(m, entry.idx);
      bestByK[k] = full;
      complete.push(full);
    });
    complete.sort((a, b) => a.total - b.total);
    return { complete, bestByK };
  }

  /*
   * What this card costs you: the cheapest complete order minus the cheapest one
   * in a world where the card was never listed. Dropping a card can let a whole
   * seller go, which is why a 20-cent card can cost three euros.
   */
  function costOfCard(m, search, i) {
    const baseline = search.complete[0];
    if (!baseline) return null;
    const B = baseline.idx;

    let best = { total: scoreWithout(m, B, i).total, ship: baseline.ship, parcels: B.length };
    for (let p = 0; p < B.length; p++) {
      const cand = B.filter((_, q) => q !== p);
      if (!cand.length) continue;
      const r = scoreWithout(m, cand, i);
      if (r.missing === 0 && r.total < best.total) best = { total: r.total, ship: r.ship, parcels: cand.length };
    }

    const saving = baseline.total - best.total;
    const shipSaved = Math.max(0, baseline.ship - best.ship);
    return {
      saving,
      shipSaved,
      cardSaved: Math.max(0, saving - shipSaved),
      parcels: best.parcels,
      fewerParcels: B.length - best.parcels,
    };
  }

  // Which unused seller improves a basket the most?
  function gapFillers(m, base, limit = 5) {
    const out = [];
    for (let j = 0; j < m.S; j++) {
      if (base.idx.includes(j)) continue;
      const r = scoreCombo(m, [...base.idx, j].sort((a, b) => a - b));
      out.push({ seller: m.sellerNames[j], saving: base.total - r.total,
        adds: r.covered - base.found, result: r });
    }
    return out.sort((a, b) => (b.adds - a.adds) || (b.saving - a.saving)).slice(0, limit);
  }

  /*
   * UI
   */

  const ui = {};

  function injectStyles() {
    const css = document.createElement('style');
    css.textContent = `
      #cmSSO { scroll-margin-top: 100px; }
      #cmSSO .cmSSO-bar { height: 6px; background: var(--bs-secondary-bg, #e9ecef); border-radius: 3px; overflow: hidden; }
      #cmSSO .cmSSO-bar > i { display: block; height: 100%; background: var(--bs-success, #198754); }
      #cmSSO .cmSSO-log { max-height: 6rem; overflow-y: auto; font-size: .8rem; }
      #cmSSO td, #cmSSO th { vertical-align: middle; }
      #cmSSO .cmSSO-missing { font-size: .8rem; }
      #cmSSO .cmSSO-win { box-shadow: inset 3px 0 0 var(--bs-success, #198754); }
      #cmSSO details > summary { cursor: pointer; }
    `;
    document.head.appendChild(css);
  }

  function buildPanel(wiz) {
    const section = document.createElement('section');
    section.id = 'cmSSO';
    section.className = 'mb-4';
    section.innerHTML = `
      <h2>Fewer shipments</h2>
      <div class="bg-white border rounded p-3">
        <p class="text-muted mb-3">
          The wizard optimises card price and happily splits your order over
          <strong>${wiz.sellers.length}</strong> sellers. This checks every one of them properly,
          so you can choose how few parcels you are willing to live with.
        </p>

        <div class="row g-2 align-items-end mb-3">
          <div class="col-12 col-md-4">
            <label class="form-label mb-1" for="cmSSO-wantlist">Wants list <span class="text-danger">*</span></label>
            <select id="cmSSO-wantlist" class="form-select form-select-sm"><option value="">Loading your lists…</option></select>
          </div>
          <div class="col-12 col-md-3">
            <label class="form-label mb-1" for="cmSSO-source">Cards</label>
            <select id="cmSSO-source" class="form-select form-select-sm">
              <option value="wizard">From these results</option>
              <option value="wantlist">Everything on the list</option>
            </select>
          </div>
          <div class="col-6 col-md-3">
            <label class="form-label mb-1" for="cmSSO-lang">Language</label>
            <select id="cmSSO-lang" class="form-select form-select-sm">
              <option value="English"${cfg.languages.join() === 'English' ? ' selected' : ''}>English only</option>
              <option value=""${!cfg.languages.length ? ' selected' : ''}>Any language</option>
              ${['German', 'French', 'Italian', 'Spanish', 'Japanese']
                .map((l) => `<option value="${l}"${cfg.languages.join() === l ? ' selected' : ''}>${l} only</option>`).join('')}
            </select>
          </div>
          <div class="col-6 col-md-2">
            <label class="form-label mb-1" for="cmSSO-cond">Condition</label>
            <select id="cmSSO-cond" class="form-select form-select-sm">
              ${CONDITIONS.map((c) => `<option value="${c}"${c === cfg.minCondition ? ' selected' : ''}>${c} or better</option>`).join('')}
            </select>
          </div>
        </div>

        <div class="d-flex flex-wrap gap-2 mb-3">
          <button id="cmSSO-run" type="button" class="btn btn-primary"><span class="fonticon-wand me-2"></span>Scan all sellers</button>
          <button id="cmSSO-stop" type="button" class="btn btn-outline-danger" hidden>Stop</button>
          <button id="cmSSO-reanalyse" type="button" class="btn btn-outline-primary" hidden>Re-analyse last scan</button>
          <button id="cmSSO-clear" type="button" class="btn btn-outline-secondary ms-auto">Clear saved prices</button>
        </div>

        <div id="cmSSO-progress" hidden>
          <div class="cmSSO-bar mb-1"><i style="width:0%"></i></div>
          <div class="d-flex justify-content-between small text-muted">
            <span id="cmSSO-status">Starting…</span><span id="cmSSO-eta"></span>
          </div>
          <div class="cmSSO-log text-muted mt-2"></div>
        </div>

        <div id="cmSSO-results" class="mt-3"></div>
      </div>`;

    const anchor = document.querySelector('#ShoppingWizardResult')?.closest('section');
    if (anchor) anchor.after(section); else document.querySelector('main')?.appendChild(section);
    return section;
  }

  ui.note = (msg, kind = 'info') => {
    const log = document.querySelector('#cmSSO .cmSSO-log');
    if (!log) return;
    const div = document.createElement('div');
    div.className = kind === 'warn' ? 'text-danger' : '';
    div.textContent = msg;
    log.appendChild(div);
    log.scrollTop = log.scrollHeight;
  };

  ui.progress = (done, total, label) => {
    const wrap = document.querySelector('#cmSSO-progress');
    if (!wrap) return;
    wrap.hidden = false;
    wrap.querySelector('.cmSSO-bar > i').style.width = total ? `${(done / total) * 100}%` : '0%';
    wrap.querySelector('#cmSSO-status').textContent = label;
    wrap.querySelector('#cmSSO-eta').textContent = `${done} / ${total}`;
  };

  /*
   * Adding a basket to the cart
   *
   * Cardmarket's add-to-cart form carries no action attribute — its own
   * script reads data-ajax-action and wraps it in a request envelope. Rather
   * than guess at that envelope, we load the seller's offer page in a hidden
   * same-origin frame, tick the real checkboxes and click the site's own
   * "add selected" button. Whatever call it makes is by definition correct.
   *
   * Adding is not buying. Everything lands in the cart for you to review.
   */

  function frameLoad(url, timeout = 30000) {
    return new Promise((resolve, reject) => {
      const f = document.createElement('iframe');
      f.style.cssText = 'position:fixed;left:-10000px;top:0;width:1280px;height:900px;opacity:0;border:0';
      let settled = false;
      const done = (fn, arg) => { if (!settled) { settled = true; fn(arg); } };
      f.addEventListener('load', () => done(resolve, f));
      f.addEventListener('error', () => { f.remove(); done(reject, new Error('frame failed')); });
      setTimeout(() => { if (!settled) { f.remove(); done(reject, new Error('frame timed out')); } }, timeout);
      document.body.appendChild(f);
      f.src = url;
    });
  }

  /*
   * The cart page does not use the offer-row markup, so counting those finds
   * nothing however full the cart is. The header total is the dependable signal.
   */
  async function cartState() {
    try {
      const doc = await httpGetDoc(`${location.origin}/${LANG_SEG}/${GAME_SEG}/ShoppingCart`);
      const header = doc.querySelector('#cart');
      const value = parsePrice(header ? header.textContent : '');
      const rows = doc.querySelectorAll(
        '[id^="articleRow"], [id^="stockRow"], [id^="cartArticle"], .article-row, [data-id-article]').length;
      return { value, rows };
    } catch { return null; }
  }

  const cartGrew = (a, b) => !!a && !!b && (
    (a.value != null && b.value != null && b.value > a.value + 0.001) || b.rows > a.rows);

  const cartLabel = (st) => (!st ? 'unknown'
    : `${st.rows} article${st.rows === 1 ? '' : 's'}${st.value != null ? `, ${euro(st.value)}` : ''}`);

  /*
   * Cardmarket refuses to be framed, so we reproduce the request. Its modal gave
   * the fields (__cmtkn, idArticle[id], amount[id]) but not the URL; other forms
   * post to /<lang>/<game>/PostGetAction/<ActionName>, so the action goes in the
   * path. We try that first and confirm against your real cart before sending
   * more. "AddArticles" is plural: one request per seller, not per card.
   */
  const CART_ACTION = 'ShoppingCart_Add_AddArticlesFromUserOffers';
  const ROUTE_KEY = 'cmSSO.addRoute.v1';

  function addRoutes() {
    const base = `${location.origin}/${LANG_SEG}/${GAME_SEG}`;
    return [
      { id: 'ajax-path', url: `${base}/AjaxAction/${CART_ACTION}`, extra: {} },
      { id: 'postget-path', url: `${base}/PostGetAction/${CART_ACTION}`, extra: {} },
      { id: 'ajax-field', url: `${base}/AjaxAction`, extra: { action: CART_ACTION } },
      { id: 'ajax-field-alt', url: `${base}/AjaxAction`, extra: { ajaxAction: CART_ACTION } },
      { id: 'ajax-query', url: `${base}/AjaxAction?action=${encodeURIComponent(CART_ACTION)}`, extra: {} },
    ];
  }

  async function postCart(route, token, items) {
    const body = new URLSearchParams();
    if (token) body.set('__cmtkn', token);
    Object.entries(route.extra).forEach(([k, v]) => body.set(k, v));
    items.forEach((it) => {
      body.set(`idArticle[${it.id}]`, String(it.id));
      body.set(`amount[${it.id}]`, String(it.qty || 1));
    });
    try {
      const res = await fetch(route.url, {
        method: 'POST',
        credentials: 'same-origin',
        headers: {
          'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
          'X-Requested-With': 'XMLHttpRequest',
        },
        body: body.toString(),
      });
      return { ok: res.ok, status: res.status, text: (await res.text().catch(() => '')).slice(0, 200) };
    } catch (e) {
      return { ok: false, status: 0, text: String(e.message) };
    }
  }

  // Send one article down each candidate route until the cart actually grows.
  async function findRoute(token, item, before, log) {
    if (!before) return { route: null, reason: 'could not read your cart to confirm' };
    for (const route of addRoutes()) {
      const res = await postCart(route, token, [item]);
      await sleep(1500);
      const now = await cartState();
      if (!now) return { route: null, reason: 'could not read your cart to confirm' };
      if (cartGrew(before, now)) {
        localStorage.setItem(ROUTE_KEY, route.id);
        return { route, state: now };
      }
      log(`${route.id}: HTTP ${res.status}, cart still ${cartLabel(now)}`);
      await sleep(400);
    }
    return { route: null, reason: 'none of the request shapes changed the cart' };
  }

  // Read a seller's offer pages and pick the live article for each wanted card.
  async function collectSellerArticles(seller, wantlistId, targets, param) {
    const items = [];
    let token = null;
    const pages = [];
    if (wantlistId) {
      for (let p = 1; p <= 120; p++) pages.push(sellerWantlistUrl(seller, wantlistId, p));
    } else {
      [...targets.values()].forEach((t) => pages.push(sellerSearchUrl(seller, t.name, param, 1)));
    }

    for (let i = 0; i < pages.length; i++) {
      if (aborted) break;
      if ([...targets.values()].every((t) => t.done)) break;
      const doc = await httpGetDoc(pages[i]);
      token = token || doc.querySelector('input[name="__cmtkn"]')?.getAttribute('value') || null;
      const rows = parseOfferRows(doc);
      if (!rows.length) break;

      rows.forEach((r) => {
        const key = normName(r.name);
        const want = targets.get(key);
        if (!want || want.done || !r.articleId || !offerAllowed(r)) return;
        const up = r.price - want.price;
        if (up > 0.50 && up / Math.max(want.price, 0.01) > 0.15) { want.pricier = r.price; return; }
        want.done = true;
        want.paid = r.price;
        items.push({ id: r.articleId, qty: want.qty || 1, name: r.name, price: r.price });
      });

      if (wantlistId && rows.length < 15) break;
      await sleep(jitter());
    }
    return { token, items };
  }

  async function addBasketToCart(m, r, opts) {
    const dry = !!opts.dryRun;
    const wantlistId = document.querySelector('#cmSSO-wantlist')?.value || null;
    const param = localStorage.getItem(PARAM_KEY) || 'name';
    const out = document.querySelector('#cmSSO-cart-out');
    const log = (t) => { const d = document.createElement('div'); d.textContent = t; out.appendChild(d); };
    aborted = false;

    const bySeller = new Map();
    r.idx.forEach((j, p) => {
      const targets = new Map();
      r.lines[p].forEach((x) => targets.set(m.wanted[x.i].key, {
        name: m.wanted[x.i].name, price: x.price, qty: m.wanted[x.i].qty, done: false,
      }));
      if (targets.size) bySeller.set(m.sellerNames[j], targets);
    });
    if (!bySeller.size) { out.innerHTML = '<div class="alert alert-warning">Nothing in this basket.</div>'; return; }

    let before = dry ? null : await cartState();
    const cachedId = localStorage.getItem(ROUTE_KEY);
    let route = dry ? null : addRoutes().find((x) => x.id === cachedId) || null;
    let added = 0;
    let sellerNo = 0;

    for (const [seller, targets] of bySeller) {
      if (aborted) break;
      sellerNo++;
      out.innerHTML = `<div class="cmSSO-bar mb-1"><i style="width:${((sellerNo - 1) / bySeller.size) * 100}%"></i></div>
        <div class="small text-muted">${dry ? 'Checking' : 'Adding'} ${seller} — ${sellerNo} of ${bySeller.size}</div>`;

      let found;
      try {
        found = await collectSellerArticles(seller, wantlistId, targets, param);
      } catch (e) {
        log(`${seller}: could not read their offers (${e.message})`);
        continue;
      }
      if (dry || !found.items.length) continue;

      // First real send: work out which request shape this site wants.
      if (!route) {
        const probe = await findRoute(found.token, found.items[0], before, log);
        if (!probe.route) {
          out.innerHTML = `<div class="alert alert-danger">
            <strong>Could not add to the cart automatically</strong> — ${probe.reason}. Nothing was bought.
            <div class="mt-2">Use the seller links in the breakdown below: each opens that seller's offers
            filtered to your list, where you can tick the boxes and press Cardmarket's own add button.</div></div>`;
          return;
        }
        route = probe.route;
        added += 1;                                   // the probe article itself
        before = probe.state;
        log(`request shape: ${route.id}`);
        const rest = found.items.slice(1);
        if (rest.length) {
          await postCart(route, found.token, rest);
          await sleep(1500);
          const now = await cartState();
          added += cartGrew(before, now) ? Math.max(1, now.rows - before.rows) : 0;
          if (!cartGrew(before, now)) log(`${seller}: the rest of this basket did not register`);
          before = now || before;
        }
        continue;
      }

      await postCart(route, found.token, found.items);
      await sleep(1500);
      const now = await cartState();
      if (cartGrew(before, now)) added += Math.max(1, now.rows - before.rows);
      else log(`${seller}: nothing registered — their offers may have just sold`);
      before = now || before;
      await sleep(jitter());
    }

    const missed = [];
    bySeller.forEach((targets, seller) => targets.forEach((t) => {
      if (!t.done) missed.push({ seller, name: t.name, pricier: t.pricier });
    }));
    const wantedCount = [...bySeller.values()].reduce((a, t) => a + t.size, 0);
    const after = dry ? null : await cartState();

    const rows = missed.map((x) => `<tr>
        <td class="text-start">${x.name}</td><td class="text-start">${x.seller}</td>
        <td class="text-start">${x.pricier != null
          ? `<span class="badge text-bg-warning">price rose</span> now ${euro(x.pricier)}`
          : '<span class="badge text-bg-secondary">not found</span> not on their pages now'}</td>
      </tr>`).join('');

    out.innerHTML = `
      <div class="alert alert-${missed.length ? 'warning' : 'success'}">
        ${dry
          ? `<strong>Test run:</strong> ${wantedCount - missed.length} of ${wantedCount} cards are still there at the expected price. Nothing was added.`
          : `<strong>${added} of ${wantedCount} cards added.</strong>
             ${after ? ` Your cart now holds ${cartLabel(after)}.` : ''}
             <a href="/${LANG_SEG}/${GAME_SEG}/ShoppingCart">Open the cart</a> to check shipping and place each order.`}
      </div>
      ${rows ? `<div class="table-responsive"><table class="table table-sm">
        <thead><tr><th class="text-start">Card</th><th class="text-start">Seller</th><th class="text-start">What happened</th></tr></thead>
        <tbody>${rows}</tbody></table></div>` : ''}`;
  }

  const esc = (t) => String(t).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

  // The page a seller's offers live on, filtered to your wants list when we have one.
  function sellerPageUrl(m, seller, sampleName) {
    const id = document.querySelector('#cmSSO-wantlist')?.value || null;
    return id ? sellerWantlistUrl(seller, id, 1)
      : sellerSearchUrl(seller, sampleName, localStorage.getItem(PARAM_KEY) || 'name', 1);
  }

  /*
   * Compares a plain fetch against the same page in a frame, and reads the
   * single-article modal, to show whether framing is blocked.
   */
  async function diagnoseCart(m, r) {
    const out = document.querySelector('#cmSSO-cart-out');
    out.innerHTML = '<div class="small text-muted">Running checks…</div>';
    const notes = [];
    const seller = m.sellerNames[r.idx[0]];
    const sample = m.wanted[r.lines[0][0].i];
    const url = sellerPageUrl(m, seller, sample.name);
    notes.push(`seller: ${seller}`);
    notes.push(`page:   ${url}`);

    let articleId = null;
    try {
      const doc = await httpGetDoc(url);
      const rows = parseOfferRows(doc);
      articleId = rows.find((x) => x.articleId)?.articleId || null;
      notes.push(`fetched page -> ${rows.length} offer rows, first article ${articleId || 'none'}`);
      const langs = rows.filter((x) => x.language).length;
      notes.push(`  language readable on ${langs}/${rows.length} rows`);
    } catch (e) { notes.push(`fetched page -> FAILED: ${e.message}`); }

    try {
      const f = await frameLoad(url, 20000);
      let d = null;
      try { d = f.contentDocument; } catch { /* cross-origin */ }
      if (!d) notes.push('framed page  -> no access to the frame document (framing blocked)');
      else {
        const rows = parseOfferRows(d);
        notes.push(`framed page  -> ${rows.length} offer rows, url ${d.location ? d.location.pathname : '?'}`);
        notes.push(`  add-selected button present: ${!!d.querySelector('#BuyAllForm button[type="submit"]')}`);
        notes.push(`  a checkbox present: ${!!d.querySelector('input[type="checkbox"][name^="idArticle"]')}`);
      }
      f.remove();
    } catch (e) { notes.push(`framed page  -> FAILED: ${e.message}`); }

    if (articleId) {
      const modal = `${location.origin}/${LANG_SEG}/${GAME_SEG}/Modal/Article_PutSingleInShoppingCart`
        + `?idArticle=${articleId}&ajaxAction=ShoppingCart_Add_AddArticlesFromUserOffers&ajaxCB=Offers.addArticlesCB`;
      try {
        const res = await fetch(modal, { credentials: 'same-origin', headers: { 'X-Requested-With': 'XMLHttpRequest' } });
        const text = await res.text();
        const doc = new DOMParser().parseFromString(text, 'text/html');
        const form = doc.querySelector('form');
        notes.push(`modal ${res.status}, ${text.length} chars`);
        notes.push(`  form action: ${form ? (form.getAttribute('action') || '(none)') : '(no form)'}`);
        notes.push(`  data-ajax-action: ${form ? (form.getAttribute('data-ajax-action') || '(none)') : '-'}`);
        notes.push('  fields: ' + [...doc.querySelectorAll('input[name],select[name]')]
          .map((i) => `${i.getAttribute('name')}=${String(i.getAttribute('value') || '').slice(0, 24)}`).join(', '));
      } catch (e) { notes.push(`modal -> FAILED: ${e.message}`); }
    }

    notes.push(`remembered request shape: ${localStorage.getItem(ROUTE_KEY) || 'none yet'}`);
    notes.push(`cart right now: ${cartLabel(await cartState())}`);
    console.log('[cmSSO] add-to-cart diagnostics\n' + notes.join('\n'));
    out.innerHTML = `<div class="alert alert-info">
      <strong>Add-to-cart diagnostics</strong>
      <pre class="small mb-1 mt-2" style="white-space:pre-wrap">${esc(notes.join('\n'))}</pre>
      <div class="small">Nothing was added. Copy this text over and it pins down the fix.</div></div>`;
  }

  /*
   * Rendering results
   */

  function sellerLink(s) {
    return `<a href="/${LANG_SEG}/${GAME_SEG}/Users/${encodeURIComponent(s)}/Offers/Singles" target="_blank" rel="noopener">${s}</a>`;
  }
  function cardSearchLink(name) {
    return `<a href="/${LANG_SEG}/${GAME_SEG}/Products/Search?searchString=${encodeURIComponent(name)}" target="_blank" rel="noopener">${name}</a>`;
  }
  function gapList(m, gaps, limit = 60) {
    if (!gaps.length) return '<span class="text-success">nothing missing</span>';
    const items = gaps.slice(0, limit).map((g) =>
      `<li>${cardSearchLink(m.wanted[g.i].name)}${g.qty > 1 ? ` ×${g.qty}` : ''}
        <span class="text-muted">— ${euro(g.price)} at ${g.seller}</span></li>`).join('');
    return `<ul class="mb-0 ps-3">${items}${gaps.length > limit ? `<li class="text-muted">+${gaps.length - limit} more</li>` : ''}</ul>`;
  }

  async function copyText(text) {
    try { await navigator.clipboard.writeText(text); return true; } catch { /* often blocked on mobile */ }
    try {
      const ta = document.createElement('textarea');
      ta.value = text;
      ta.style.cssText = 'position:fixed;left:0;top:0;opacity:0';
      document.body.appendChild(ta);
      ta.focus();
      ta.select();
      const ok = document.execCommand('copy');
      ta.remove();
      return ok;
    } catch { return false; }
  }

  function shoppingList(m, r) {
    const out = [];
    r.idx.forEach((j, p) => {
      const line = r.lines[p];
      if (!line.length) return;
      out.push(`# ${m.sellerNames[j]} — ${line.length} cards, ${euro(line.reduce((a, x) => a + x.price, 0))}`);
      line.slice().sort((a, b) => m.wanted[a.i].name.localeCompare(m.wanted[b.i].name))
        .forEach((x) => out.push(`1 ${m.wanted[x.i].name}`));
      out.push('');
    });
    if (r.gaps.length) {
      out.push('# not in this basket');
      r.gaps.forEach((g) => out.push(`${g.qty} ${m.wanted[g.i].name}`));
    }
    return out.join('\n');
  }

  /*
   * The wizard already named a seller for every card it placed. If our scan
   * says nobody stocks one of those, the scan is wrong, not the market — so
   * say so instead of quietly telling you to buy it elsewhere.
   */
  function wizardContradictions(m, wiz) {
    const byKey = new Map();
    (wiz.sellers || []).forEach((s) => (s.articles || []).forEach((a) => {
      const k = normName(a.name);
      if (!byKey.has(k)) byKey.set(k, { seller: s.username, price: a.price });
    }));
    return m.nobodyHas.map((w) => ({ w, hit: byKey.get(w.key) })).filter((x) => x.hit);
  }

  function renderRecommendations(m, search, wiz, singlesByIdx) {
    const { complete, bestByK } = search;
    if (!complete.length) {
      return `<div class="alert alert-warning">No line-up covers every card. Look at the seller table below and pick from there.</div>`;
    }

    const cheapest = complete[0];
    const sizes = bestByK.map((r, k) => (r ? { k, r } : null)).filter(Boolean);
    const fewest = sizes[0];
    const bestSingle = singlesByIdx.slice().sort((a, b) => b.found - a.found || a.total - b.total)[0];
    const singleDone = completeOf(m, bestSingle.idx);
    const base = wiz.wizardTotal;

    const vs = (v) => (base == null ? '' :
      ` <span class="${v < base ? 'text-success' : 'text-danger'}">(${v < base ? '−' : '+'}${euro(Math.abs(v - base))} vs the wizard)</span>`);

    const items = [];

    items.push(`<li class="mb-2"><strong>Cheapest complete order:
      ${cheapest.sellers.map(sellerLink).join(' + ')}</strong> — all ${cheapest.found} available cards in
      ${cheapest.idx.length} parcel${cheapest.idx.length > 1 ? 's' : ''} for <strong>${euro(cheapest.total)}</strong>
      (${euro(cheapest.cardCost)} cards + ${euro(cheapest.ship)} shipping).${vs(cheapest.total)}</li>`);

    if (fewest && fewest.r !== cheapest) {
      const extra = fewest.r.total - cheapest.total;
      items.push(`<li class="mb-2"><strong>Fewest parcels: ${fewest.r.sellers.map(sellerLink).join(' + ')}</strong> —
        the same ${fewest.r.found} cards in just ${fewest.k} parcel${fewest.k > 1 ? 's' : ''} for ${euro(fewest.r.total)}.
        That is <strong>${euro(extra)}</strong> more than the cheapest option, for
        ${cheapest.idx.length - fewest.k} fewer parcel${cheapest.idx.length - fewest.k === 1 ? '' : 's'} to wait for.${vs(fewest.r.total)}</li>`);
    }

    items.push(`<li class="mb-2"><strong>Biggest single seller: ${sellerLink(bestSingle.sellers[0])}</strong> —
      ${bestSingle.found} of ${m.reachableUnits} cards for ${euro(bestSingle.total)} on its own.
      ${bestSingle.gaps.length
        ? `The ${bestSingle.gaps.length} card${bestSingle.gaps.length === 1 ? '' : 's'} it lacks are cheapest to pick up from
           ${singleDone.added.map(sellerLink).join(' + ') || 'nobody in this scan'},
           making ${euro(singleDone.combo.total)} all in.${vs(singleDone.combo.total)}`
        : 'It covers everything on its own.'}</li>`);

    // Cards whose real cost is mostly the parcel they force
    const offenders = m.wanted.map((w, i) => ({ w, c: costOfCard(m, search, i) }))
      .filter((x) => x.c && x.c.saving > 0.01)
      .sort((a, b) => b.c.saving - a.c.saving);
    const draggers = offenders.filter((x) => x.c.fewerParcels > 0);

    if (draggers.length) {
      const top = draggers[0];
      items.push(`<li class="mb-2"><strong>${cardSearchLink(top.w.name)} is the expensive one to keep</strong> —
        dropping it saves ${euro(top.c.saving)} and ${top.c.fewerParcels} parcel${top.c.fewerParcels === 1 ? '' : 's'},
        yet the card itself is only ${euro(top.c.cardSaved)}. The other ${euro(top.c.shipSaved)} is the shipping
        it drags along.${draggers.length > 1
          ? ` ${draggers.length - 1} other card${draggers.length === 2 ? '' : 's'} do the same — see the card list above.`
          : ''}</li>`);
    } else if (offenders.length) {
      items.push(`<li class="mb-2">No single card is forcing an extra parcel — every seller in this basket is
        carrying its weight. Dropping cards would only save their own price.</li>`);
    }

    const clashes = wizardContradictions(m, wiz);
    if (clashes.length) {
      items.push(`<li class="mb-2"><strong class="text-danger">The scan missed ${clashes.length} card${clashes.length === 1 ? '' : 's'} the wizard did find.</strong>
        ${clashes.slice(0, 6).map((x) => `${cardSearchLink(x.w.name)} <span class="text-muted">(${x.hit.seller}, ${euro(x.hit.price)})</span>`).join(', ')}${clashes.length > 6 ? ` and ${clashes.length - 6} more` : ''}.
        That means the sweep did not see those sellers' full stock — usually a saved scan made with a different wants list.
        Press <em>Clear saved prices</em> above and run again, and check the wants list matches the one this wizard run used.</li>`);
    }

    if (m.nobodyHas.length) {
      items.push(`<li class="mb-2"><strong>Not available from any of these ${m.S} sellers:</strong>
        ${m.nobodyHas.map((w) => cardSearchLink(w.name)).join(', ')}. Every total above excludes
        ${m.nobodyHas.length === 1 ? 'it' : 'them'}, so budget for one more order.</li>`);
    }

    const cheapestK = cheapest.idx.length;
    const slider = sizes.length < 2 ? '' : `
      <h5 class="mt-4">How many parcels?</h5>
      <p class="small text-muted mb-2">Every position buys all ${m.reachableUnits} available cards — only the
        number of sellers changes. <strong>${cheapestK} parcel${cheapestK === 1 ? '' : 's'}</strong> is the cheapest.</p>
      <div class="px-1">
        <input type="range" class="form-range" id="cmSSO-parcels" list="cmSSO-ticks"
          min="${sizes[0].k}" max="${sizes[sizes.length - 1].k}" step="1" value="${cheapestK}">
        <datalist id="cmSSO-ticks">${sizes.map(({ k }) => `<option value="${k}" label="${k}"></option>`).join('')}</datalist>
        <div class="d-flex justify-content-between small text-muted">
          <span>${sizes[0].k}</span><span>${sizes[sizes.length - 1].k} parcels</span>
        </div>
      </div>
      <div id="cmSSO-pick-summary" class="mt-2"></div>`;



    return `
      <div class="alert alert-light border">
        <h5 class="mb-2">What to do</h5>
        <ul class="mb-0">${items.join('')}</ul>
      </div>

      ${slider}`;
  }

  function renderDetail(m, r) {
    const box = document.querySelector('#cmSSO-detail');
    if (!box) return;
    const fillers = gapFillers(m, r);
    const fin = completeOf(m, r.idx);

    const perSeller = r.idx.map((j, p) => {
      const line = r.lines[p].slice().sort((a, b) => m.wanted[a.i].name.localeCompare(m.wanted[b.i].name));
      const sampleName = line.length ? m.wanted[line[0].i].name : (m.wanted[0] || {}).name || '';
      return `<div class="col-12 col-lg-6 mb-3">
        <div class="border rounded p-2 h-100">
          <div class="d-flex justify-content-between flex-wrap">
            <strong><a href="${sellerPageUrl(m, m.sellerNames[j], sampleName)}" target="_blank" rel="noopener"
              title="Open this seller's offers filtered to your list">${m.sellerNames[j]}</a></strong>
            <span class="small">${line.length} cards · ${euro(line.reduce((a, x) => a + x.price, 0))} + ${euro(m.ship[j])} shipping</span>
          </div>
          <ul class="mb-0 ps-3 cmSSO-missing mt-1">
            ${line.map((x) => `<li>${m.wanted[x.i].name} <span class="text-muted">${euro(x.price)}</span></li>`).join('') || '<li class="text-muted">nothing</li>'}
          </ul>
        </div></div>`;
    }).join('');

    const fillerRows = fillers.map((f) => `<tr>
        <td class="text-start">${sellerLink(f.seller)}</td>
        <td class="text-center">+${f.adds}</td>
        <td class="text-end ${f.saving > 0 ? 'text-success' : 'text-muted'}">${f.saving > 0 ? '−' : '+'}${euro(Math.abs(f.saving))}</td>
        <td class="text-end">${euro(f.result.total)}</td>
      </tr>`).join('');

    box.innerHTML = `
      <hr>
      <div class="d-flex justify-content-between align-items-start flex-wrap gap-2">
        <h5 class="mb-0">${r.sellers.join(' + ')}</h5>
        <div class="d-flex flex-wrap gap-2">
          <button type="button" class="btn btn-sm btn-outline-secondary" id="cmSSO-check">Check availability</button>
          <button type="button" class="btn btn-sm btn-success" id="cmSSO-add">Add basket to cart</button>
          <button type="button" class="btn btn-sm btn-outline-secondary" id="cmSSO-copy">Copy shopping list</button>
          <button type="button" class="btn btn-sm btn-outline-secondary" id="cmSSO-diag">Diagnose</button>
        </div>
      </div>
      <p class="small text-muted mt-1">
        ${euro(r.cardCost)} cards + ${euro(r.ship)} shipping = <strong>${euro(r.basket)}</strong>.
        ${r.missingUnits
          ? `Missing ${r.missingUnits} card${r.missingUnits === 1 ? '' : 's'}; the cheapest finish is ${fin.added.map(sellerLink).join(' + ') || 'not available in this scan'}, ${euro(fin.combo.total)} all in.`
          : 'This basket needs nothing else.'}
      </p>
      <div class="row">${perSeller}</div>
      <div class="row">
        <div class="col-12 col-lg-6 mb-3">
          <h6>Missing from this basket</h6>
          <div class="cmSSO-missing">${gapList(m, r.gaps)}</div>
        </div>
        <div class="col-12 col-lg-6 mb-3">
          <h6>Best seller to add next</h6>
          <table class="table table-sm">
            <thead><tr><th class="text-start">Seller</th><th class="text-center">Cards added</th>
              <th class="text-end">Change</th><th class="text-end">New total</th></tr></thead>
            <tbody>${fillerRows || '<tr><td colspan="4" class="text-muted">nothing left to add</td></tr>'}</tbody>
          </table>
        </div>
      </div>
      <div id="cmSSO-cart-out" class="mt-2"></div>`;

    const busy = (on) => {
      ['#cmSSO-add', '#cmSSO-check', '#cmSSO-diag'].forEach((sel) => {
        const el = box.querySelector(sel);
        if (el) el.disabled = on;
      });
    };
    box.querySelector('#cmSSO-diag')?.addEventListener('click', async () => {
      busy(true);
      try { await diagnoseCart(m, r); } finally { busy(false); }
    });
    box.querySelector('#cmSSO-check')?.addEventListener('click', async () => {
      busy(true);
      try { await addBasketToCart(m, r, { dryRun: true }); } finally { busy(false); }
    });
    box.querySelector('#cmSSO-add')?.addEventListener('click', async () => {
      const n = r.lines.reduce((a, l) => a + l.length, 0);
      if (!confirm(`Add ${n} cards from ${r.sellers.length} sellers to your Cardmarket cart?\n\n`
        + 'This does not buy anything \u2014 you review each order in the cart before checkout.')) return;
      busy(true);
      try { await addBasketToCart(m, r, { dryRun: false }); } finally { busy(false); }
    });
    box.querySelector('#cmSSO-copy')?.addEventListener('click', async (ev) => {
      const text = shoppingList(m, r);
      const btn = ev.target.closest('button') || ev.target;
      if (await copyText(text)) {
        btn.textContent = 'Copied';
        setTimeout(() => { btn.textContent = 'Copy shopping list'; }, 1500);
        return;
      }
      // Blocked: put it on screen so it can still be selected by hand.
      const out = box.querySelector('#cmSSO-cart-out');
      out.innerHTML = `<div class="alert alert-info mb-0">
        <div class="small mb-1">Your browser would not let the script use the clipboard — select and copy this:</div>
        <textarea class="form-control form-control-sm" rows="8" readonly></textarea></div>`;
      const ta = out.querySelector('textarea');
      ta.value = text;
      ta.focus();
      ta.select();
    });
  }

  /*
   * Card picker — park the maybes and re-run the numbers, no rescanning
   */

  let VIEW = null;                                   // last scan, unfiltered
  let excluded = new Set(readJSON(EXCL_KEY, []));
  let cardsOpen = false;

  function saveExcluded() { writeJSON(EXCL_KEY, [...excluded]); }

  // Per-card facts that do not depend on which cards are currently included.
  function cardStats(wanted, matrix, sellerNames) {
    return wanted.map((w) => {
      let cheapest = null, sellers = 0;
      sellerNames.forEach((s) => {
        const u = matrix[s]?.[w.key] || [];
        if (u.length) { sellers++; if (cheapest == null || u[0] < cheapest) cheapest = u[0]; }
      });
      return { w, cheapest, sellers };
    });
  }

  function renderCards(m, search, stats) {
    const rows = stats.map((st) => {
      const off = excluded.has(st.w.key);
      const i = m.wanted.findIndex((x) => x.key === st.w.key);
      const cost = (!off && i >= 0) ? costOfCard(m, search, i) : null;
      const worth = cost && cost.saving > 0.01;
      return {
        st, off, sort: worth ? cost.saving : -1,
        html: `<tr class="${off ? 'text-muted' : ''}">
          <td class="text-start"><div class="form-check mb-0">
            <input class="form-check-input" type="checkbox" data-card="${st.w.key}" id="cx-${st.w.key}" ${off ? '' : 'checked'}>
            <label class="form-check-label" for="cx-${st.w.key}">${st.w.name}${st.w.qty > 1 ? ` ×${st.w.qty}` : ''}</label>
          </div></td>
          <td class="text-end">${st.cheapest == null ? '<span class="text-danger">none</span>' : euro(st.cheapest)}</td>
          <td class="text-center">${st.sellers}</td>
          <td class="text-end">${off ? '<span class="text-muted">parked</span>'
            : worth ? `<span class="text-success fw-bold">−${euro(cost.saving)}</span>
                ${cost.fewerParcels > 0
                  ? `<div class="small text-warning-emphasis">${euro(cost.cardSaved)} card + ${euro(cost.shipSaved)} shipping
                     — drops ${cost.fewerParcels} parcel${cost.fewerParcels === 1 ? '' : 's'}</div>`
                  : cost.shipSaved > 0.05
                    ? `<div class="small text-muted">${euro(cost.cardSaved)} card + ${euro(cost.shipSaved)} cheaper shipping</div>`
                    : '<div class="small text-muted">just its own price</div>'}`
            : '<span class="text-muted">nothing</span>'}</td>
        </tr>`,
      };
    });
    rows.sort((a, b) => b.sort - a.sort || a.st.w.name.localeCompare(b.st.w.name));

    const off = stats.filter((st) => excluded.has(st.w.key)).length;
    const lonely = stats.filter((st) => st.sellers === 1 && !excluded.has(st.w.key)).length;

    return `
      <details id="cmSSO-cards" class="mb-3" ${cardsOpen ? 'open' : ''}>
        <summary><strong>Cards included: ${stats.length - off} of ${stats.length}</strong>
          ${off ? `<span class="text-muted"> — ${off} parked</span>` : ''}
          <span class="text-muted small"> · untick a maybe and everything below recalculates</span></summary>

        <div class="d-flex flex-wrap gap-2 my-2">
          <button type="button" class="btn btn-sm btn-outline-secondary" data-bulk="lonely">Park the ${lonely} card${lonely === 1 ? '' : 's'} only one seller has</button>
          <div class="input-group input-group-sm" style="width:14rem">
            <span class="input-group-text">Park over</span>
            <input type="number" class="form-control" id="cmSSO-overprice" min="0" step="0.5" value="5" aria-label="price limit">
            <span class="input-group-text">€</span>
            <button type="button" class="btn btn-outline-secondary" data-bulk="over">Go</button>
          </div>
          <button type="button" class="btn btn-sm btn-outline-secondary" data-bulk="reset">Include everything</button>
        </div>

        <p class="small text-muted mb-2">“What it costs you” is how much the cheapest complete order would drop
          if you dropped that card — a card that forces its own parcel costs far more than its price tag.</p>
        <div class="table-responsive" style="max-height:24rem;overflow-y:auto">
          <table class="table table-sm table-striped align-middle mb-0" id="cmSSO-cardtable">
            <thead class="position-sticky top-0 bg-white"><tr>
              <th class="text-start">Card</th><th class="text-end">Cheapest</th>
              <th class="text-center">Sellers</th><th class="text-end">What it costs you</th>
            </tr></thead>
            <tbody>${rows.map((r) => r.html).join('')}</tbody>
          </table>
        </div>
      </details>`;
  }

  function wireCards(stats) {
    const det = document.querySelector('#cmSSO-cards');
    if (!det) return;
    det.addEventListener('toggle', () => { cardsOpen = det.open; });

    det.querySelector('#cmSSO-cardtable')?.addEventListener('change', (e) => {
      const key = e.target.getAttribute('data-card');
      if (!key) return;
      if (e.target.checked) excluded.delete(key); else excluded.add(key);
      saveExcluded();
      cardsOpen = true;
      draw();
    });

    det.addEventListener('click', (e) => {
      const what = e.target.getAttribute('data-bulk');
      if (!what) return;
      if (what === 'reset') excluded.clear();
      if (what === 'lonely') stats.filter((st) => st.sellers <= 1).forEach((st) => excluded.add(st.w.key));
      if (what === 'over') {
        const lim = parseFloat(det.querySelector('#cmSSO-overprice').value);
        if (!isNaN(lim)) stats.filter((st) => st.cheapest != null && st.cheapest > lim).forEach((st) => excluded.add(st.w.key));
      }
      saveExcluded();
      cardsOpen = true;
      draw();
    });
  }

  /*
   * Seller picker — see who will be scanned before spending the time
   */

  let ranking = [];

  function renderResults(wiz, wanted, matrix, shipping, sellerNames, skipped) {
    VIEW = { wiz, wanted, matrix, shipping, sellerNames, skipped: skipped || [] };
    draw();
  }

  function draw() {
    if (!VIEW) return;
    const { wiz, wanted, matrix, shipping, sellerNames, skipped } = VIEW;
    const scrollY = window.scrollY;
    const active = wanted.filter((w) => !excluded.has(w.key));
    if (!active.length) {
      document.querySelector('#cmSSO-results').innerHTML =
        `<hr><div class="alert alert-warning">Every card is parked. Tick at least one to see an analysis.</div>`;
      return;
    }
    drawAnalysis(wiz, active, wanted, matrix, shipping, sellerNames, skipped);
    window.scrollTo({ top: scrollY });
  }

  function drawAnalysis(wiz, wanted, allWanted, matrix, shipping, sellerNames, skipped) {
    const m = buildModel(wanted, matrix, shipping, sellerNames);
    const stats = cardStats(allWanted, matrix, sellerNames);

    // Nothing found anywhere is a broken scan, not an answer. Say so rather
    // than declaring some seller the winner of an empty basket.
    if (!m.reachableUnits) {
      document.querySelector('#cmSSO-results').innerHTML = `
        <hr>
        <div class="alert alert-danger">
          <h5 class="mb-2">The scan found none of your cards</h5>
          <p class="mb-2">Not one of the ${m.S} sellers matched a single card, which means the scan
            failed rather than the sellers being empty. Any totals shown from this would be meaningless.</p>
          <p class="mb-1"><strong>Most likely:</strong></p>
          <ul class="mb-2">
            <li>${langUnknown > 0
              ? `${langUnknown} offers were rejected because their language could not be read — set
                 <strong>Language</strong> to “Any language” and run again to confirm.`
              : 'The card names on the sellers\' pages did not match your list.'}</li>
            <li>Your filters may be too tight — check Min. condition and the skip options.</li>
            <li>The wants list picked above may not be the one this wizard run used.</li>
          </ul>
          <button type="button" class="btn btn-sm btn-outline-danger" id="cmSSO-wipe">Clear saved prices and start over</button>
        </div>`;
      document.querySelector('#cmSSO-wipe')?.addEventListener('click', () => {
        cache = {};
        cacheFlush();
        localStorage.removeItem(SCAN_KEY);
        document.querySelector('#cmSSO-results').innerHTML =
          '<hr><div class="alert alert-info">Cleared. Adjust the settings above and run the scan again.</div>';
      });
      return;
    }
    const search = searchBaskets(m, Math.min(cfg.maxCombo, sellerNames.length));

    const singles = [];
    for (let j = 0; j < m.S; j++) singles.push(evalCombo(m, [j]));

    const wizardLine = wiz.wizardTotal != null
      ? `The wizard wanted <strong>${euro(wiz.wizardTotal)}</strong> — ${euro(wiz.wizardCards)} in cards plus ${euro(wiz.wizardShipping)} shipping across ${wiz.wizardShipments} parcels.`
      : '';

    const sellerRows = singles.slice().sort((a, b) => b.found - a.found || a.total - b.total).map((r) => {
      const s = r.sellers[0];
      const country = wiz.sellers.find((x) => x.username === s)?.country || '';
      const done = completeOf(m, r.idx);
      return `<tr data-single="${r.idx[0]}" style="cursor:pointer">
        <td class="text-start">${sellerLink(s)} <span class="text-muted small">${country}</span></td>
        <td class="text-center">${r.found} / ${m.reachableUnits}</td>
        <td class="text-center">${pct(r.coverage)}<div class="cmSSO-bar mt-1"><i style="width:${pct(r.coverage)}"></i></div></td>
        <td class="text-end">${euro(r.cardCost)}</td>
        <td class="text-end">${euro(r.ship)}</td>
        <td class="text-end">${euro(r.total)}</td>
        <td class="text-end fw-bold">${euro(done.combo.total)}
          <div class="text-muted small">${done.added.length ? `+ ${done.added.join(', ')}` : 'on its own'}</div></td>
        <td class="text-start cmSSO-missing">${r.gaps.length
          ? `<details><summary>${r.gaps.length} missing</summary>${gapList(m, r.gaps)}</details>`
          : '<span class="text-success">has everything</span>'}</td>
        <td class="text-end"><button type="button" class="btn btn-sm btn-outline-success" data-cart="s:${r.idx[0]}" title="Add this basket to your cart"><span class="fonticon-cart"></span></button></td>
      </tr>`;
    }).join('');

    document.querySelector('#cmSSO-results').innerHTML = `
      <hr>
      <p class="small text-muted">${wizardLine}
        Analysing ${m.wantedUnits} cards against ${m.S} sellers; ${m.reachableUnits} of them exist somewhere in this scan.
        Every basket below buys all ${m.reachableUnits}, so the totals are directly comparable — a line-up cannot look
        cheap by leaving expensive cards out. Click any row for the card-by-card breakdown.
        ${(() => {
          const parked = allWanted.filter((w) => excluded.has(w.key)).length;
          return parked ? `<strong>${parked} card${parked === 1 ? '' : 's'} parked</strong> and left out of these numbers.` : '';
        })()}
        ${skipped && skipped.length ? `<br><span class="text-warning-emphasis">${skipped.length} seller${skipped.length === 1 ? ' was' : 's were'} not scanned</span>
          (<span title="${skipped.map((x) => x.username).join(', ')}">${skipped.slice(0, 6).map((x) => x.username).join(', ')}${skipped.length > 6 ? ` +${skipped.length - 6} more` : ''}</span>),
          so a cheaper line-up may exist. Raise “Max. sellers to scan” and run again — already-scanned sellers come from cache, so only the new ones cost time.` : ''}</p>

      ${renderCards(m, search, stats)}

      ${renderRecommendations(m, search, wiz, singles)}

      <h5 class="mt-4">Every seller on its own</h5>
      <p class="small text-muted mb-2">"Complete order" is what that seller costs once the cards it lacks are added from the cheapest other sellers.</p>
      <div class="table-responsive">
        <table class="table table-sm table-striped align-middle" id="cmSSO-singles">
          <thead><tr>
            <th class="text-start">Seller</th><th class="text-center">Cards</th><th class="text-center">Coverage</th>
            <th class="text-end">Cards €</th><th class="text-end">Shipping</th><th class="text-end">Alone</th>
            <th class="text-end">Complete order</th><th class="text-start">Missing</th><th></th>
          </tr></thead>
          <tbody>${sellerRows}</tbody>
        </table>
      </div>

      <div id="cmSSO-detail"></div>`;

    const show = (r) => {
      renderDetail(m, r);
      document.querySelector('#cmSSO-detail').scrollIntoView({ behavior: 'smooth', block: 'nearest' });
    };
    const bind = (sel, attr, pick) => {
      document.querySelector(sel)?.addEventListener('click', (e) => {
        const tr = e.target.closest(`tr[${attr}]`);
        if (!tr || e.target.tagName === 'A' || e.target.closest('details')) return;
        if (e.target.closest('button[data-cart]')) return;   // handled below
        show(pick(tr.getAttribute(attr)));
      });
    };
    wireCards(stats);
    bind('#cmSSO-singles tbody', 'data-single', (v) => evalCombo(m, [+v]));

    const slider = document.querySelector('#cmSSO-parcels');
    const summary = document.querySelector('#cmSSO-pick-summary');
    const cheapest = search.complete[0];
    const showK = (k) => {
      const r = search.bestByK[k];
      if (!r || !summary) return;
      const vs = wiz.wizardTotal != null ? r.total - wiz.wizardTotal : null;
      const extra = cheapest ? r.total - cheapest.total : 0;
      summary.innerHTML = `
        <div class="border rounded p-2">
          <div class="d-flex justify-content-between flex-wrap gap-2">
            <div><strong>${r.sellers.map(sellerLink).join(' + ')}</strong></div>
            <div><strong>${euro(r.total)}</strong>
              <span class="text-muted small">${euro(r.cardCost)} cards + ${euro(r.ship)} shipping</span></div>
          </div>
          <div class="small mt-1">
            ${extra < 0.005
              ? '<span class="badge text-bg-success">cheapest</span>'
              : `<span class="text-muted">${euro(extra)} more than the cheapest option</span>`}
            ${vs != null ? ` · <span class="${vs < 0 ? 'text-success' : 'text-danger'}">${vs < 0 ? '−' : '+'}${euro(Math.abs(vs))} vs the wizard</span>` : ''}
          </div>
        </div>`;
      renderDetail(m, r);
    };
    if (slider) {
      slider.addEventListener('input', () => {
        let k = Number(slider.value);
        // not every parcel count is reachable; snap to the nearest that is
        if (!search.bestByK[k]) {
          for (let d = 1; d <= search.bestByK.length; d++) {
            if (search.bestByK[k - d]) { k -= d; break; }
            if (search.bestByK[k + d]) { k += d; break; }
          }
          slider.value = String(k);
        }
        showK(k);
      });
      showK(Number(slider.value));
    } else if (cheapest) {
      renderDetail(m, cheapest);
    }

    // Cart buttons in every table: open that basket, then add it.
    document.querySelector('#cmSSO-results')?.addEventListener('click', async (e) => {
      const btn = e.target.closest('button[data-cart]');
      if (!btn) return;
      e.stopPropagation();
      const v = btn.getAttribute('data-cart') || '';
      const basket = v.startsWith('s:')
        ? evalCombo(m, [Number(v.slice(2))])
        : search.complete[Number(v.slice(2))];
      if (!basket) return;

      renderDetail(m, basket);
      const n = basket.lines.reduce((a, l) => a + l.length, 0);
      if (!confirm(`Add ${n} cards from ${basket.sellers.join(' + ')} to your Cardmarket cart?\n\n`
        + 'This does not buy anything \u2014 you review each order in the cart before checkout.\n'
        + 'If an earlier attempt left anything in the cart, clear it first to avoid duplicates.')) return;

      btn.disabled = true;
      document.querySelector('#cmSSO-detail').scrollIntoView({ behavior: 'smooth', block: 'nearest' });
      try { await addBasketToCart(m, basket, { dryRun: false }); } finally { btn.disabled = false; }
    });

  }

  /*
   * Main run
   */

  async function run(wiz, panel) {
    aborted = false;
    const runBtn = panel.querySelector('#cmSSO-run');
    const stopBtn = panel.querySelector('#cmSSO-stop');
    runBtn.disabled = true;
    stopBtn.hidden = false;
    panel.querySelector('.cmSSO-log').innerHTML = '';

    // Pull settings out of the form
    cfg.minCondition = panel.querySelector('#cmSSO-cond').value;
    const lang = panel.querySelector('#cmSSO-lang').value;
    cfg.languages = lang ? [lang] : [];
    writeJSON(CFG_KEY, cfg);

    try {
      // 1. Wanted cards
      const source = panel.querySelector('#cmSSO-source').value;
      let wanted;
      const wantlistId = panel.querySelector('#cmSSO-wantlist').value || null;
      if (source === 'wantlist') {
        const id = wantlistId;
        if (!id) { ui.note('Pick a wants list first.', 'warn'); return; }
        ui.progress(0, 1, 'Reading wantlist…');
        wanted = await fetchWantlist(id);
        if (!wanted.length) {
          ui.note('Could not read that wantlist. Paste the cards instead.', 'warn');
          return;
        }
      } else {
        wanted = wantedFromWizard(wiz);
      }
      if (!wanted.length) { ui.note('No cards to look for.', 'warn'); return; }

      // The wants filter needs a real wants list; otherwise fall back.
      const fast = !!wantlistId;   // the wants list is required up front

      // Every seller gets scanned; the ranking only decides the order, so a
      // stopped run still has the most useful sellers done.
      const ranked = rankSellers(wiz.sellers);
      const chosen = ranked;
      const skipped = [];
      const sellerNames = chosen.map((x) => x.username);
      const shipping = {};
      wiz.sellers.forEach((x) => { shipping[x.username] = x.shipping ?? cfg.defaultShipping; });

      let param = null;
      if (!fast) {
        const probeSeller = chosen.find((s) => s.articles.length) || wiz.sellers.find((s) => s.articles.length);
        ui.progress(0, 1, 'Checking how seller search works…');
        param = await probeSearchParam(probeSeller.username, probeSeller.articles[0].name);
      }
      if (!fast && !param) {
        ui.note('Cardmarket\'s seller offer search did not respond as expected — nothing was scraped. Open a seller\'s offer page, search a card, and send me the resulting URL so I can fix the parameter.', 'warn');
        return;
      }
      langUnknown = 0;
      ui.note('Keep this tab open while it runs. Each seller is saved as it finishes, '
        + 'so if the browser interrupts you, running again picks up where it stopped.');
      ui.note(cfg.languages.length
        ? `Only ${cfg.languages.join(' / ')} printings will be considered.`
        : 'All languages will be considered.');

      const fresh = sellerNames.filter((n) => !cacheGet(n, SCANNED_MARK));
      // ~3 printings per card, ~20 rows a page
      const pagesEach = Math.max(1, Math.ceil((wanted.length * 3) / 20));
      const reqs = fast ? fresh.length * pagesEach : fresh.length * wanted.length;
      const mins = Math.max(1, Math.round((reqs * ((cfg.minDelay + cfg.maxDelay) / 2)) / (fast ? 1 : cfg.concurrency) / 60000));
      ui.note(fast
        ? `Sweeping each seller's wants-filtered pages. ${fresh.length} of ${sellerNames.length} sellers still need scanning `
          + `— roughly ${mins} minute${mins === 1 ? '' : 's'}. The rest come from the last scan.`
        : `Seller search uses "${param}". ${wanted.length} cards x ${fresh.length} new sellers `
          + `= about ${reqs} lookups, roughly ${mins} minute${mins === 1 ? '' : 's'}.`);

      // 3. Scrape
      const matrix = {};
      const wantedByKey = new Map(wanted.map((w) => [w.key, w]));
      const total = sellerNames.length * wanted.length;
      let done = 0;
      let reused = 0;
      const started = Date.now();
      const eta = () => {
        const spent = (Date.now() - started) / 1000;
        const fresh = Math.max(1, done - reused);
        const left = Math.round((spent / fresh) * (total - done));
        return `about ${Math.floor(left / 60)}m ${left % 60}s left`;
      };

      for (const seller of sellerNames) {
        if (aborted) break;
        matrix[seller] = {};

        // Reuse a seller only when the earlier sweep actually covered every card
        // we are asking about now. A partial hit means it was swept for a
        // different list, and treating the gaps as "not stocked" is how a card
        // the seller plainly has ends up reported as available from nobody.
        const covered = cacheGet(seller, SCANNED_MARK)
          && wanted.every((w) => cacheGet(seller, w.key) !== null);
        if (covered) {
          wanted.forEach((w) => { matrix[seller][w.key] = cacheGet(seller, w.key) || []; });
          done += wanted.length;
          reused += wanted.length;
          ui.progress(done, total, `${seller} — from earlier scan`);
          continue;
        }

        if (fast) {
          try {
            const res = await scanSellerViaWantlist(seller, wantlistId, wanted, (page) => {
              ui.progress(done, total, `${seller} — page ${page} · ${eta()}`);
            });
            matrix[seller] = res.cards;

            /*
             * The wizard proved which cards this seller stocks. If the sweep
             * missed one, the sweep is at fault, so look it up by name rather
             * than recording it as unstocked.
             */
            const proof = [...new Set((wiz.sellers.find((x) => x.username === seller)?.articles || [])
              .map((a) => normName(a.name))
              .filter((k) => wantedByKey.has(k) && !(matrix[seller][k] || []).length))];

            if (proof.length) {
              param = param || await probeSearchParam(seller, wantedByKey.get(proof[0]).name);
              let recovered = 0;
              for (const key of proof) {
                if (aborted || !param) break;
                try {
                  const r = await offersFor(seller, wantedByKey.get(key), param, true);
                  matrix[seller][key] = r.units;
                  if (r.units.length) recovered++;
                  if (!r.cached) await sleep(jitter());
                } catch { /* leave it empty */ }
              }
              ui.note(`${seller}: the sweep missed ${proof.length} card${proof.length === 1 ? '' : 's'} `
                + `the wizard found there; recovered ${recovered} by name.`
                + (recovered === 0 && !param ? ' The name search could not be set up for this seller.' : ''),
                recovered < proof.length ? 'warn' : 'info');
            }

            if (res.hitCap) {
              ui.note(`${seller}: stopped at the ${res.pages}-page limit — their list may be longer than that.`, 'warn');
            }
            done += wanted.length;
            ui.progress(done, total, `${seller} — ${res.pages} page${res.pages === 1 ? '' : 's'} · ${eta()}`);
          } catch (e) {
            if (String(e.message).startsWith('blocked')) {
              aborted = true;
              ui.note('Cardmarket is refusing requests. Stopped early — everything scanned so far is kept.', 'warn');
              break;
            }
            wanted.forEach((w) => { matrix[seller][w.key] = []; });
            done += wanted.length;
          }
          cacheFlush();
          await sleep(jitter());
          continue;
        }

        const queue = wanted.slice();
        const worker = async () => {
          while (queue.length && !aborted) {
            const want = queue.shift();
            let hitCache = false;
            try {
              const r = await offersFor(seller, want, param);
              matrix[seller][want.key] = r.units;
              hitCache = r.cached;
            } catch (e) {
              if (String(e.message).startsWith('blocked')) {
                aborted = true;
                ui.note('Cardmarket is refusing requests. Stopped early — cached results are kept.', 'warn');
                break;
              }
              matrix[seller][want.key] = [];
            }
            done++;
            if (hitCache) reused++;
            ui.progress(done, total, `${seller} — ${want.name}${hitCache ? ' (cached)' : ` · ${eta()}`}`);
            // Only pace real requests; cached lookups cost nothing.
            if (!hitCache) await sleep(jitter());
          }
        };
        await Promise.all(Array.from({ length: cfg.concurrency }, worker));
        if (!aborted) cacheSet(seller, SCANNED_MARK, [1]);
        cacheFlush();
      }

      cacheFlush();
      if (cfg.languages.length && langUnknown > 40) {
        ui.note(`${langUnknown} offers were skipped because their language could not be read. `
          + 'If coverage looks too thin, switch Language to "Any language" and compare.', 'warn');
      }
      const usable = sellerNames.filter((s) => matrix[s]);
      writeJSON(SCAN_KEY, { t: Date.now(), wanted, matrix, shipping, sellerNames: usable,
        skipped: skipped.map((x) => ({ username: x.username, articles: x.articleCount, stock: x.stock })) });
      panel.querySelector('#cmSSO-reanalyse').hidden = false;
      ui.progress(done, total, aborted ? 'Stopped — showing what was collected' : 'Done');
      renderResults(wiz, wanted, matrix, shipping, usable, skipped);
      document.querySelector('#cmSSO-results').scrollIntoView({ behavior: 'smooth', block: 'start' });
    } finally {
      runBtn.disabled = false;
      stopBtn.hidden = true;
    }
  }

  /*
   * Boot
   */

  function boot() {
    if (document.querySelector('#cmSSO')) return;
    const wiz = parseWizard();
    if (!wiz.sellers.length) return;

    injectStyles();
    const panel = buildPanel(wiz);

    const sourceSel = panel.querySelector('#cmSSO-source');
    sourceSel.addEventListener('change', async () => {
      void sourceSel.value;
    });

    (async () => {
      const sel = panel.querySelector('#cmSSO-wantlist');
      try {
        const lists = await fetchWantlists(wiz.sellers[0]?.username);
        sel.innerHTML = lists.length
          ? `<option value="">— none —</option>` + lists.map((l) => `<option value="${l.id}">${l.name}</option>`).join('')
          : '<option value="">No wants lists found</option>';
        // Newest list first is usually the one the wizard was just run on.
        const newest = lists.slice().sort((a, b) => Number(b.id) - Number(a.id))[0];
        if (newest) sel.value = newest.id;
      } catch {
        sel.innerHTML = '<option value="">Could not load your wants lists</option>';
        ui.note('Could not read your wants lists — the fast sweep needs one. '
          + 'Reload the page, or scan without it (slower).', 'warn');
      }
    })();

    panel.querySelector('#cmSSO-run').addEventListener('click', () => {
      const sel = panel.querySelector('#cmSSO-wantlist');
      if (!sel.value) {
        sel.classList.add('is-invalid');
        ui.progress(0, 1, 'Pick the wants list this wizard run used, then scan.');
        return;
      }
      sel.classList.remove('is-invalid');
      run(wiz, panel);
    });

    const reBtn = panel.querySelector('#cmSSO-reanalyse');
    const saved = readJSON(SCAN_KEY, null);
    if (saved && saved.sellerNames?.length) {
      reBtn.hidden = false;
      reBtn.title = `Scanned ${new Date(saved.t).toLocaleString()}`;
    }
    reBtn.addEventListener('click', () => {
      const scan = readJSON(SCAN_KEY, null);
      if (!scan) return;
      writeJSON(CFG_KEY, cfg);
      renderResults(wiz, scan.wanted, scan.matrix, scan.shipping, scan.sellerNames, scan.skipped || []);
    });
    panel.querySelector('#cmSSO-stop').addEventListener('click', () => {
      aborted = true;
      ui.note('Stopping after the requests in flight…');
    });
    panel.querySelector('#cmSSO-clear').addEventListener('click', () => {
      cache = {};
      cacheFlush();
      ui.note('Saved prices cleared. The next run fetches everything fresh.');
      panel.querySelector('#cmSSO-progress').hidden = false;
    });
  }

  boot();
})();
