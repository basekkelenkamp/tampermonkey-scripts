// ==UserScript==
// @name         Cardmarket Shopping Wizard — Single-Seller Optimizer
// @namespace    cm-shopping-wizard-optimizer
// @version      2.3.0
// @description  Re-checks every seller from a Shopping Wizard result individually and tells you which basket to actually buy. Prices every option as a complete order, so fewer parcels can win.
// @author       you
// @match        https://www.cardmarket.com/*/Wants/ShoppingWizard*
// @run-at       document-idle
// @grant        none
// @noframes
// ==/UserScript==

/*
 * HOW IT WORKS
 * 0. Finds the wants list the wizard ran on (remembered from the wizard form,
 *    else matched against your lists by card names). No picker.
 * 1. Reads sellers, shipping and offered articles off the wizard results page.
 * 2. Sweeps each seller's offers filtered to that wants list, paging through them:
 *    a few requests per seller instead of one per card, then double-checks the
 *    result against the cards the wizard already proved that seller stocks.
 *    Cardmarket applies each card's own options from the list (language,
 *    minimum condition, expansion, foil/signed/altered) to these pages, and
 *    to the by-name fallback too, so the script keeps no filters of its own.
 * 3. Scores line-ups as COMPLETE ORDERS — a basket is extended until it covers
 *    every reachable card, else it looks cheap by omitting expensive ones.
 * 4. Parking a card recalculates instantly from the stored scan.
 * 5. Add to cart finds the live articles (wants pages, then by name), sends
 *    them in small batches, verifies each against your real cart and retries
 *    anything that did not land, reporting it by name.
 *
 * Politeness: randomised delay, backoff on 429/503, a hard stop when blocked, and a
 * local cache so re-runs and re-analysis cost nothing.
 */

(function () {
  'use strict';

  /*
   * Config
   */

  const CFG_KEY = 'cmSSO.cfg.v3';
  const CACHE_KEY = 'cmSSO.cache.v3';
  const SCAN_KEY = 'cmSSO.scan.v2';
  const EXCL_KEY = 'cmSSO.excluded.v1';
  // The wants list the wizard form was last opened or submitted with, and the
  // list each results page turned out to belong to.
  const LAST_LIST_KEY = 'cmSSO.lastWizardList.v1';
  const RESULT_LIST_KEY = 'cmSSO.resultLists.v1';

  const DEFAULTS = {
    concurrency: 2,        // parallel requests inside one seller
    minDelay: 350,         // ms, per request, randomised
    maxDelay: 900,
    cacheHours: 24,
    maxPagesPerCard: 2,    // offer pages to walk per seller+card
    rankMode: 'hybrid',    // 'hybrid' = wizard cards + stock size, 'wizard' = wizard cards only
    maxCombo: 12,          // how many parcels the slider may reach
    defaultShipping: 1.70, // fallback when the wizard didn't show one
  };

  const LANGUAGE_NAMES = [
    'English', 'French', 'German', 'Spanish', 'Italian', 'Simplified Chinese',
    'Japanese', 'Portuguese', 'Russian', 'Korean', 'Traditional Chinese',
  ];

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


  const [LANG_SEG, GAME_SEG] = location.pathname.split('/').filter(Boolean);

  /*
   * Cache
   */

  // The wants list this results page belongs to: { id, name, how } once found.
  let WANTLIST = null;

  let cache = readJSON(CACHE_KEY, {});
  function filterHash() {
    // The wants list is the whole filter: a sweep filtered to list A never saw
    // the cards on list B (or saw them under A's options), so it is the key.
    return WANTLIST?.id || 'nolist';
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

  /*
   * A seller's offers for one card. `name` is the only name filter seller pages
   * honour (searchString, productName and cardName are ignored and return the
   * whole store). With idWantslist alongside, Cardmarket also applies that
   * card's options from the list, so expansion, language and condition hold
   * here exactly as on the wants-filtered sweep.
   */
  function sellerSearchUrl(seller, cardName, page, idWantslist) {
    const base = `${location.origin}/${LANG_SEG}/${GAME_SEG}/Users/${encodeURIComponent(seller)}/Offers/Singles`;
    const p = new URLSearchParams();
    p.set('name', searchableName(cardName));
    if (idWantslist) p.set('idWantslist', String(idWantslist));
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

  // Everything else (language, condition, expansion, foil, signed, altered) is
  // already applied by Cardmarket from the wants list. A playset's price is for
  // four cards, so it would be mispriced as one copy.
  const offerAllowed = (o) => !o.playset;

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

  /*
   * Which wants list did this wizard run use?
   *
   * The results page does not say. So: the wizard form page (also matched by
   * this script) remembers the list it was opened or submitted with, and every
   * candidate is checked against the results by card names before it is used.
   * When nothing was remembered, your lists are tried newest first and the one
   * holding the wizard's cards wins.
   */

  const listIdFrom = (href) => {
    const s = String(href || '');
    const m = s.match(/[?&]idWantsList=(\d+)/i) || s.match(/\/Wants\/(\d+)(?:[/?#]|$)/);
    return m ? m[1] : null;
  };

  // Every wants list id the overview links to, newest (highest id) first.
  function wantlistIdsFromDoc(doc) {
    const ids = new Set();
    doc.querySelectorAll('a[href*="/Wants/"], a[href*="idWantsList="]').forEach((a) => {
      const id = listIdFrom(a.getAttribute('href'));
      if (id) ids.add(id);
    });
    return [...ids].sort((a, b) => Number(b) - Number(a));
  }

  // A wants list page: its title and the card names on it.
  async function fetchWantsList(id) {
    const doc = await httpGetDoc(`${location.origin}/${LANG_SEG}/${GAME_SEG}/Wants/${id}`);
    const table = doc.querySelector('table');
    const keys = new Set();
    if (table) {
      const ths = [...table.querySelectorAll('thead th')];
      let col = ths.findIndex((th) => th.classList.contains('name'));
      if (col < 0) col = 3;
      table.querySelectorAll('tbody tr').forEach((tr) => {
        const td = tr.children[col];
        const name = td ? td.textContent.trim() : '';
        if (name) keys.add(normName(name));
      });
    }
    const name = (doc.title || '').split('|')[0].trim() || `Wants list ${id}`;
    return { id, name, keys };
  }

  // On the wizard form: remember the list it runs on.
  function rememberWizardList() {
    const save = (id) => { if (id) writeJSON(LAST_LIST_KEY, { id: String(id), t: Date.now() }); };
    save(listIdFrom(location.search));
    document.addEventListener('submit', (e) => {
      const f = e.target;
      const field = f && f.querySelector && f.querySelector('[name="idWantsList"], [name="idWantslist"]');
      save(field && /^\d+$/.test(field.value) ? field.value : listIdFrom(f?.getAttribute?.('action')));
    }, true);
    document.addEventListener('change', (e) => {
      const el = e.target;
      if (el && /^idWants?list$/i.test(el.name || '') && /^\d+$/.test(el.value)) save(el.value);
    }, true);
  }

  async function detectWantlist(wiz, onStep) {
    const wizardKeys = new Set(wantedFromWizard(wiz).map((w) => w.key));
    // cover: share of the wizard's cards on the list. fit: share of the list
    // the wizard placed. An older, bigger list can hold every card too, so a
    // list must fit well as well as cover to be taken without looking further.
    const measure = (keys) => {
      let hit = 0;
      wizardKeys.forEach((k) => { if (keys.has(k)) hit++; });
      return { cover: wizardKeys.size ? hit / wizardKeys.size : 0, fit: keys.size ? hit / keys.size : 0 };
    };
    const tried = new Set();
    let best = null;
    const attempt = async (id, how, needCover, needFit = 0) => {
      if (!id || tried.has(id)) return null;
      tried.add(id);
      onStep?.(`Checking wants list ${id}…`);
      let list;
      try { list = await fetchWantsList(id); } catch (e) {
        if (String(e.message).startsWith('blocked')) throw e;
        return null;
      }
      const { cover, fit } = measure(list.keys);
      const found = { ...list, how, coverage: cover, fit };
      if (cover >= needCover && fit >= needFit) return found;
      if (!best || cover + fit > best.coverage + best.fit) best = { ...found, how: 'closest match' };
      return null;
    };

    const path = location.pathname;
    const byResult = readJSON(RESULT_LIST_KEY, {});
    const last = readJSON(LAST_LIST_KEY, null);
    const fresh = last && Date.now() - last.t < 48 * 3600e3 ? last.id : null;
    const linked = [...document.querySelectorAll('a[href*="/Wants/"], a[href*="idWantsList="]')]
      .map((a) => listIdFrom(a.getAttribute('href'))).filter(Boolean);

    let hit = await attempt(byResult[path], 'used for this page before', 0.5);
    for (const id of linked) { if (hit) break; hit = await attempt(id, 'linked from this page', 0.5, 0.5); }
    if (!hit) hit = await attempt(fresh, 'the list you opened the wizard with', 0.8);

    if (!hit) {
      const ids = wantlistIdsFromDoc(await httpGetDoc(`${location.origin}/${LANG_SEG}/${GAME_SEG}/Wants`));
      for (const id of ids.slice(0, 30)) {
        if (aborted) break;
        hit = await attempt(id, 'matched by its cards', 0.95, 0.8);
        if (hit) break;
        await sleep(jitter());
      }
    }
    if (!hit && best && best.coverage >= 0.8) hit = best;
    if (hit) {
      byResult[path] = hit.id;
      const keys = Object.keys(byResult);
      keys.slice(0, Math.max(0, keys.length - 50)).forEach((k) => delete byResult[k]);
      writeJSON(RESULT_LIST_KEY, byResult);
    }
    return hit;
  }

  /*
   * Scraping one seller × one card
   */

  async function offersFor(seller, want, force) {
    // force skips the cache: the recovery pass exists precisely because the
    // sweep already stored an empty result for this card, and asking the cache
    // again would just hand that same empty answer straight back.
    const cached = force ? null : cacheGet(seller, want.key);
    if (cached) return { units: cached, cached: true };

    const target = want.key;
    const units = [];
    for (let page = 1; page <= cfg.maxPagesPerCard; page++) {
      const doc = await httpGetDoc(sellerSearchUrl(seller, want.name, page, WANTLIST?.id));
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
     * Scoring needs numbers only. Single copies (the usual case) get a flat
     * card x seller grid of cheapest prices; cards wanted more than once are
     * merged across the chosen sellers, so two copies can come from two
     * different sellers.
     */
    const first = new Float64Array(W * S).fill(Infinity);
    const multi = [];
    for (let i = 0; i < W; i++) {
      for (let j = 0; j < S; j++) if (units[i][j].length) first[i * S + j] = units[i][j][0];
      if (wanted[i].qty > 1) multi.push(i);
    }
    const isMulti = new Uint8Array(W);
    multi.forEach((i) => { isMulti[i] = 1; });
    const shipArr = Float64Array.from(ship);

    const wantedUnits = wanted.reduce((a, w) => a + w.qty, 0);
    const reachableUnits = reachable.reduce((a, b) => a + b, 0);
    const nobodyHas = wanted.map((w, i) => ({ ...w, i })).filter((w) => reachable[w.i] < w.qty);
    const medianShip = ship.length ? [...ship].sort((a, b) => a - b)[Math.floor(ship.length / 2)] : cfg.defaultShipping;
    const allQtyOne = wanted.every((w) => w.qty === 1);

    return { units, bestUnit, bestSeller, reachable, ship, wanted, sellerNames,
      wantedUnits, reachableUnits, nobodyHas, medianShip, allQtyOne, S, W,
      first, multi, isMulti, shipArr };
  }

  // Cost of a line-up, in numbers only — no allocation, no shopping lists.
  // dropCard scores it as if that card had never been on the list.
  function scoreCombo(m, idx, dropCard = -1) {
    const S = m.S, F = m.first, k = idx.length;
    let cards = 0, covered = 0, missing = 0;
    const gaps = [];
    for (let i = 0; i < m.W; i++) {
      if (i === dropCard || m.isMulti[i] || !m.reachable[i]) continue;
      const base = i * S;
      let best = Infinity;
      for (let t = 0; t < k; t++) { const v = F[base + idx[t]]; if (v < best) best = v; }
      if (best < Infinity) { cards += best; covered++; }
      else { missing++; if (gaps.length < 3) gaps.push(i); }
    }
    for (let q = 0; q < m.multi.length; q++) {
      const i = m.multi[q];
      if (i === dropCard) continue;
      const need = m.reachable[i];
      // k-way merge of the chosen sellers' sorted unit prices
      const pos = new Array(k).fill(0);
      let got = 0;
      while (got < need) {
        let best = Infinity, bt = -1;
        for (let t = 0; t < k; t++) {
          const u = m.units[i][idx[t]];
          if (pos[t] < u.length && u[pos[t]] < best) { best = u[pos[t]]; bt = t; }
        }
        if (bt < 0) break;
        pos[bt]++; got++; cards += best;
      }
      covered += got;
      if (got < need) { missing += need - got; if (gaps.length < 3) gaps.push(i); }
    }
    let ship = 0;
    for (let t = 0; t < k; t++) ship += m.shipArr[idx[t]];
    return { cards, ship, total: cards + ship, covered, missing, gaps };
  }
  const scoreWithout = (m, idx, dropCard) => scoreCombo(m, idx, dropCard);

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

  /*
   * Exhaustive for every line-up size that fits a compute budget (usually up
   * to 3-4 parcels), then greedy growth with swap passes — restarted from
   * several promising sellers, because a single greedy path commits to its
   * first pick and can miss the pairings that win at larger sizes.
   */
  const MISS_PENALTY = 1000;      // coverage first, price second
  const EXH_BUDGET = 60000;       // combinations scored exhaustively per size
  const SEEDS = 5;                // extra greedy restarts

  function searchBaskets(m, maxK) {
    const S = m.S;
    const bestByIdx = [];         // parcel count -> cheapest full-coverage line-up
    const rank = (r) => r.total + r.missing * MISS_PENALTY;

    const consider = (idx, r) => {
      if (r.missing === 0) {
        const k = idx.length;
        if (!bestByIdx[k] || r.total < bestByIdx[k].total - 1e-9) bestByIdx[k] = { idx: idx.slice(), total: r.total };
      }
    };

    for (let k = 1; k <= Math.min(maxK, S); k++) {
      if (nCk(S, k) > EXH_BUDGET) break;
      for (const idx of combinations(S, k)) consider(idx, scoreCombo(m, idx));
    }

    const improve = (start) => {
      let idx = start;
      let cur = rank(scoreCombo(m, idx));
      let improved = true;
      let guard = 0;
      while (improved && guard++ < 5) {
        improved = false;
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
      return idx;
    };

    // Grow one seller at a time from a starting line-up.
    const grow = (seed) => {
      let idx = seed.slice();
      if (idx.length) consider(idx, scoreCombo(m, idx));
      while (idx.length < Math.min(maxK, S)) {
        let add = null;
        for (let j = 0; j < S; j++) {
          if (idx.indexOf(j) !== -1) continue;
          const cand = idx.concat(j).sort((x, y) => x - y);
          const sc = rank(scoreCombo(m, cand));
          if (!add || sc < add.sc) add = { sc, cand };
        }
        if (!add) break;
        idx = improve(add.cand);
        consider(idx, scoreCombo(m, idx));

        // A smaller line-up may still cover everything — try dropping each seller.
        if (idx.length > 1) {
          for (let p = 0; p < idx.length; p++) {
            const cand = idx.filter((_, q) => q !== p);
            consider(cand, scoreCombo(m, cand));
          }
        }
      }
    };

    grow([]);
    const seeds = [...Array(S).keys()]
      .map((j) => ({ j, r: scoreCombo(m, [j]) }))
      .sort((a, b) => rank(a.r) - rank(b.r))
      .slice(0, SEEDS);
    seeds.forEach(({ j }) => grow([j]));

    // A bigger line-up that costs more than a smaller one is never worth showing.
    const bestByK = [];
    const complete = [];
    let floor = Infinity;
    bestByIdx.forEach((entry, k) => {
      if (!entry || entry.total >= floor - 0.005) return;
      floor = entry.total;
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
      #cmSSO .cmSSO-bar > i { display: block; height: 100%; background: var(--bs-success, #198754); transition: width .2s; }
      #cmSSO .cmSSO-log { max-height: 6rem; overflow-y: auto; font-size: .8rem; }
      #cmSSO td, #cmSSO th { vertical-align: middle; }
      #cmSSO .cmSSO-small { font-size: .8rem; }
      #cmSSO details > summary { cursor: pointer; }
      #cmSSO .cmSSO-hero { border-left: 4px solid var(--bs-success, #198754) !important; }
      #cmSSO .cmSSO-k { min-width: 6rem; line-height: 1.15; }
      #cmSSO .cmSSO-k small { display: block; font-size: .75rem; opacity: .85; }
      #cmSSO tr[data-single] { cursor: pointer; }
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
        <p class="text-muted small mb-3">
          The wizard split this order over <strong>${wiz.sellers.length}</strong> sellers to save cents on cards.
          This scans every one of them and prices each option as a complete order, so you can see what
          fewer parcels really cost — then puts the basket you pick in your cart.
        </p>

        <div class="row g-2 align-items-end">
          <div class="col-12 col-md-7 small">
            <div class="text-muted">Wants list</div>
            <div id="cmSSO-wantlist">Finding the list this wizard ran on…</div>
          </div>
          <div class="col-12 col-md-5 d-flex gap-2">
            <button id="cmSSO-run" type="button" class="btn btn-primary btn-sm flex-grow-1"><span class="fonticon-wand me-2"></span>Scan sellers</button>
            <button id="cmSSO-stop" type="button" class="btn btn-outline-danger btn-sm" hidden>Stop</button>
            <button id="cmSSO-reanalyse" type="button" class="btn btn-outline-primary btn-sm" hidden>Last scan</button>
          </div>
        </div>

        <details id="cmSSO-tools" class="mt-2">
          <summary class="small text-muted">Tools</summary>
          <div class="border rounded p-2 mt-2 small">
            <p class="text-muted mb-2">Each card's language, condition, expansion and foil/signed/altered
              options come from your wants list — edit them there.</p>
            <div class="d-flex flex-wrap gap-2 align-items-center">
              <button id="cmSSO-clear" type="button" class="btn btn-sm btn-outline-secondary">Clear saved prices</button>
              <button id="cmSSO-samples" type="button" class="btn btn-sm btn-outline-secondary"
                title="Download the raw HTML of the pages this script reads, to help fix parsing">Save page samples</button>
            </div>
          </div>
        </details>

        <div id="cmSSO-progress" class="mt-3" hidden>
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

  const esc = (t) => String(t ?? '').replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

  /*
   * Adding a basket to the cart
   *
   * Cardmarket refuses to be framed, so we reproduce its own request: a POST of
   * __cmtkn, idArticle[id] and amount[id] to the AddArticlesFromUserOffers
   * action. The exact URL shape is probed once and remembered.
   *
   * Why the old version lost cards:
   *  - it only looked on the wants-filtered pages, but the scan recovers cards
   *    the wants filter hides by searching them BY NAME — so those cards were
   *    priced into the basket and then never found when adding;
   *  - it sent each seller's whole basket as one request, so a single article
   *    that had just sold (or an amount above what the seller has) could make
   *    the whole batch bounce, and nothing retried it;
   *  - a page that failed mid-seller threw away everything already collected;
   *  - it asked for the full wanted quantity at every seller, even when the
   *    basket split copies over several sellers.
   *
   * Now: articles are collected from the wants pages AND by name, every send is
   * checked against the real cart, and whatever did not land is retried one
   * article at a time and reported by name. Adding is not buying.
   */

  const CART_ACTION = 'ShoppingCart_Add_AddArticlesFromUserOffers';
  const ROUTE_KEY = 'cmSSO.addRoute.v1';
  const CART_CHUNK = 8;

  function addRoutes() {
    const base = `${location.origin}/${LANG_SEG}/${GAME_SEG}`;
    const all = [
      { id: 'ajax-path', url: `${base}/AjaxAction/${CART_ACTION}`, extra: {} },
      { id: 'postget-path', url: `${base}/PostGetAction/${CART_ACTION}`, extra: {} },
      { id: 'ajax-field', url: `${base}/AjaxAction`, extra: { action: CART_ACTION } },
      { id: 'ajax-field-alt', url: `${base}/AjaxAction`, extra: { ajaxAction: CART_ACTION } },
      { id: 'ajax-query', url: `${base}/AjaxAction?action=${encodeURIComponent(CART_ACTION)}`, extra: {} },
    ];
    // Remembered shape first.
    const known = localStorage.getItem(ROUTE_KEY);
    return all.sort((a, b) => (b.id === known) - (a.id === known));
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
      return { ok: res.ok, status: res.status };
    } catch (e) {
      return { ok: false, status: 0 };
    }
  }

  // The cart page, raw. The header carries the value; the body usually carries
  // each article id, which lets us verify article by article.
  async function cartSnapshot() {
    try {
      const res = await fetch(`${location.origin}/${LANG_SEG}/${GAME_SEG}/ShoppingCart`,
        { credentials: 'same-origin', cache: 'no-store' });
      if (!res.ok) return null;
      const html = await res.text();
      const doc = new DOMParser().parseFromString(html, 'text/html');
      const header = doc.querySelector('#cart');
      return { value: parsePrice(header ? header.textContent : ''), html };
    } catch { return null; }
  }

  const hasId = (snap, id) => !!snap && new RegExp(`(^|\\D)${id}(\\D|$)`).test(snap.html);
  const valueGrew = (a, b) => !!a && !!b && a.value != null && b.value != null && b.value > a.value + 0.001;

  // Read one seller's pages and pick live articles for every card we want there.
  async function collectSellerArticles(seller, wantlistId, targets) {
    let token = null;
    const cands = new Map();                    // card key -> Map(articleId -> offer)
    const have = (key) => [...(cands.get(key)?.values() || [])].reduce((a, c) => a + c.count, 0);
    const enough = () => [...targets].every(([k, t]) => have(k) >= t.qty);

    const take = (doc) => {
      token = token || doc.querySelector('input[name="__cmtkn"]')?.getAttribute('value') || null;
      const rows = parseOfferRows(doc);
      rows.forEach((r) => {
        const key = normName(r.name);
        const t = targets.get(key);
        if (!t || !r.articleId || !offerAllowed(r)) return;
        const up = r.price - t.price;
        if (up > 0.50 && up / Math.max(t.price, 0.01) > 0.15) {
          t.pricier = Math.min(t.pricier ?? Infinity, r.price);
          return;
        }
        const m = cands.get(key) || new Map();
        m.set(r.articleId, { id: r.articleId, price: r.price, count: Math.max(1, r.count) });
        cands.set(key, m);
      });
      return rows;
    };
    // One retry per page; a page that keeps failing ends the walk but keeps
    // everything already collected.
    const get = async (url) => {
      try { return await httpGetDoc(url); } catch (e) {
        if (aborted || String(e.message).startsWith('blocked')) throw e;
        await sleep(2000);
        return httpGetDoc(url);
      }
    };

    if (wantlistId) {
      let seenFirst = null;
      for (let p = 1; p <= 120 && !aborted && !enough(); p++) {
        let doc;
        try { doc = await get(sellerWantlistUrl(seller, wantlistId, p)); } catch (e) {
          if (String(e.message).startsWith('blocked')) throw e;
          break;
        }
        const rows = take(doc);
        if (!rows.length) break;
        if (rows[0].articleId && rows[0].articleId === seenFirst) break;
        seenFirst = rows[0].articleId;
        const next = doc.querySelector('a[data-direction="next"]');
        if (!next || !next.getAttribute('href') || rows.length < 15) break;
        await sleep(jitter());
      }
    }

    // Whatever the wants filter did not show, look up by name — the same
    // fallback the scan uses, so every card it priced can actually be found.
    const short = [...targets].filter(([k, t]) => have(k) < t.qty);
    for (const [key, t] of short) {
      if (aborted) break;
      for (let page = 1; page <= cfg.maxPagesPerCard; page++) {
        let doc;
        try { doc = await get(sellerSearchUrl(seller, t.name, page, wantlistId)); } catch (e) {
          if (String(e.message).startsWith('blocked')) throw e;
          break;
        }
        const rows = take(doc);
        await sleep(jitter());
        if (rows.length < 20 || have(key) >= t.qty) break;
      }
    }

    // Cheapest live articles first, never asking for more than an article has.
    const items = [];
    targets.forEach((t, key) => {
      const list = [...(cands.get(key)?.values() || [])].sort((a, b) => a.price - b.price);
      let need = t.qty;
      t.got = 0;
      for (const c of list) {
        if (need <= 0) break;
        const q = Math.min(need, c.count);
        items.push({ id: c.id, qty: q, price: c.price, name: t.name, seller });
        need -= q;
        t.got += q;
      }
    });
    return { token, items };
  }

  async function addBasketToCart(m, r, opts) {
    const dry = !!opts.dryRun;
    const wantlistId = WANTLIST?.id || null;
    const out = document.querySelector('#cmSSO-cart-out');
    out.innerHTML = `<div class="cmSSO-bar mb-1"><i style="width:0%"></i></div>
      <div class="small text-muted" data-status>Starting…</div><div class="cmSSO-log text-muted mt-1" data-log></div>`;
    const bar = out.querySelector('.cmSSO-bar > i');
    const status = (t, frac) => { out.querySelector('[data-status]').textContent = t; bar.style.width = `${frac * 100}%`; };
    const log = (t) => {
      const box = out.querySelector('[data-log]');
      if (!box) return;
      const d = document.createElement('div'); d.textContent = t; box.appendChild(d); box.scrollTop = box.scrollHeight;
    };
    aborted = false;

    // Per seller: how many copies of each card this basket buys there.
    const bySeller = new Map();
    r.idx.forEach((j, p) => {
      const targets = new Map();
      r.lines[p].forEach((x) => {
        const w = m.wanted[x.i];
        const t = targets.get(w.key) || { name: w.name, price: 0, qty: 0 };
        t.qty += 1;
        t.price = Math.max(t.price, x.price);
        targets.set(w.key, t);
      });
      if (targets.size) bySeller.set(m.sellerNames[j], targets);
    });
    if (!bySeller.size) { out.innerHTML = '<div class="alert alert-warning">Nothing in this basket.</div>'; return; }
    const wantedUnits = [...bySeller.values()].reduce((a, ts) => a + [...ts.values()].reduce((b, t) => b + t.qty, 0), 0);

    // Phase 1 — find the live articles.
    const batches = [];
    let n = 0;
    for (const [seller, targets] of bySeller) {
      if (aborted) break;
      status(`Finding articles at ${seller} (${++n} of ${bySeller.size})…`, (n - 1) / bySeller.size * (dry ? 1 : 0.4));
      try {
        const found = await collectSellerArticles(seller, wantlistId, targets);
        if (found.items.length) batches.push({ seller, ...found });
      } catch (e) {
        log(`${seller}: could not read their offers (${e.message})`);
        if (String(e.message).startsWith('blocked')) { log('Cardmarket is throttling us — stopped. Try again in a few minutes.'); break; }
      }
    }

    const missedTargets = [];
    bySeller.forEach((targets, seller) => targets.forEach((t) => {
      const short = t.qty - (t.got || 0);
      if (short > 0) missedTargets.push({ seller, name: t.name, qty: short, why: t.pricier != null ? 'pricier' : 'gone', price: t.pricier });
    }));
    const foundUnits = batches.reduce((a, b) => a + b.items.reduce((s, it) => s + it.qty, 0), 0);

    if (dry) {
      out.innerHTML = summaryHtml({ dry, wantedUnits, foundUnits, missedTargets, failed: [], added: 0, already: 0 });
      return;
    }

    // Phase 2 — send, verify against the real cart, retry singles.
    let snap = await cartSnapshot();
    if (!snap) {
      out.innerHTML = '<div class="alert alert-danger">Could not read your cart, so nothing was sent. Are you logged in?</div>';
      return;
    }
    const queue = batches.flatMap((b) => b.items.map((it) => ({ ...it, token: b.token })));
    // If the cart page shows article ids at all, it shows the ones already in it.
    let idsVisible = queue.some((it) => hasId(snap, it.id)) || null;
    const already = idsVisible ? queue.filter((it) => hasId(snap, it.id)) : [];
    let todo = queue.filter((it) => !already.includes(it));
    const added = [];
    const failed = [];
    const totalSend = todo.length || 1;
    let route = null;

    // Did these items land between two snapshots?
    const landed = (before, after, items) => {
      if (!after) return [];
      if (idsVisible) return items.filter((it) => hasId(after, it.id));
      return valueGrew(before, after) ? items : [];          // only used one at a time
    };

    // Calibrate on the first article: find the request shape, learn whether the
    // cart page exposes ids (then we can batch), else go one at a time.
    while (todo.length && !route && !aborted) {
      const it = todo[0];
      status(`Adding ${it.name}…`, 0.4);
      for (const rt of addRoutes()) {
        await postCart(rt, it.token, [it]);
        await sleep(1300);
        const now = await cartSnapshot();
        if (now && (hasId(now, it.id) || valueGrew(snap, now))) {
          route = rt;
          localStorage.setItem(ROUTE_KEY, rt.id);
          if (idsVisible == null) idsVisible = hasId(now, it.id);
          snap = now;
          break;
        }
        if (now) snap = now;
        await sleep(400);
      }
      if (!route) {
        // Maybe this one article sold. Try the next before giving up entirely.
        failed.push(it);
        todo.shift();
        if (failed.length >= 3) break;
        continue;
      }
      added.push(it);
      todo.shift();
    }
    // Gave up after three refusals in a row. If nothing ever landed, the
    // request itself is wrong; otherwise those articles are simply gone.
    if (!route && todo.length && !already.length) {
      out.innerHTML = `<div class="alert alert-danger"><strong>Could not add to the cart automatically</strong> —
        none of the request shapes changed your cart. Nothing was bought.
        <div class="mt-2">Use <em>Copy list</em> and the seller links below, or press <em>Diagnose cart</em> and send the output.</div></div>`;
      return;
    }
    if (!route) { failed.push(...todo); todo = []; }
    if (route) log(`request shape: ${route.id}; verifying ${idsVisible ? 'by article id, in batches' : 'by cart value, one at a time'}`);

    const chunk = idsVisible ? CART_CHUNK : 1;
    const retry = [];
    for (let i = 0; i < todo.length && !aborted; i += chunk) {
      const part = todo.slice(i, i + chunk);
      status(`Adding ${part[0].seller}: ${part.map((x) => x.name).join(', ')}`, 0.4 + 0.6 * ((added.length + failed.length) / totalSend));
      await postCart(route, part[0].token, part);
      await sleep(1200);
      const now = await cartSnapshot();
      const ok = landed(snap, now, part);
      added.push(...ok);
      part.filter((x) => !ok.includes(x)).forEach((x) => retry.push(x));
      if (now) snap = now;
      await sleep(jitter());
    }

    // Second chance, one article per request, after a short pause.
    if (retry.length && !aborted) {
      log(`${retry.length} article${retry.length === 1 ? '' : 's'} did not register — retrying one by one`);
      await sleep(2500);
      for (const it of retry) {
        if (aborted) break;
        status(`Retrying ${it.name} (${it.seller})…`, 0.4 + 0.6 * ((added.length + failed.length) / totalSend));
        await postCart(route, it.token, [it]);
        await sleep(1500);
        const now = await cartSnapshot();
        if (landed(snap, now, [it]).length) added.push(it); else failed.push(it);
        if (now) snap = now;
        await sleep(jitter());
      }
    }

    const units = (list) => list.reduce((a, it) => a + it.qty, 0);
    out.innerHTML = summaryHtml({
      dry, wantedUnits, foundUnits, missedTargets, failed,
      added: units(added), already: units(already), cart: snap,
    });
  }

  function summaryHtml({ dry, wantedUnits, foundUnits, missedTargets, failed, added, already, cart }) {
    const rows = [
      ...missedTargets.map((x) => [x.name, x.seller, x.why === 'pricier'
        ? `<span class="badge text-bg-warning">price rose</span> now ${euro(x.price)}`
        : '<span class="badge text-bg-secondary">sold out</span> not on their pages any more']),
      ...failed.map((x) => [x.name, x.seller,
        '<span class="badge text-bg-danger">refused</span> Cardmarket did not accept it — likely just sold']),
    ].map(([a, b, c]) => `<tr><td class="text-start">${esc(a)}</td><td class="text-start">${esc(b)}</td><td class="text-start">${c}</td></tr>`).join('');
    const short = missedTargets.reduce((a, x) => a + x.qty, 0) + failed.reduce((a, x) => a + x.qty, 0);
    const head = dry
      ? `<strong>${foundUnits} of ${wantedUnits} cards</strong> are still listed at the expected price. Nothing was added.`
      : `<strong>${added + already} of ${wantedUnits} cards are in your cart</strong>${already ? ` (${already} were already there)` : ''}.
         ${cart?.value != null ? `Cart value now ${euro(cart.value)}.` : ''}
         <a href="/${LANG_SEG}/${GAME_SEG}/ShoppingCart">Open the cart</a> to check shipping and place each order.`;
    return `<div class="alert alert-${short ? 'warning' : 'success'} mb-2">${head}</div>
      ${rows ? `<div class="table-responsive"><table class="table table-sm mb-0">
        <thead><tr><th class="text-start">Card</th><th class="text-start">Seller</th><th class="text-start">What happened</th></tr></thead>
        <tbody>${rows}</tbody></table></div>` : ''}`;
  }

  // The page a seller's offers live on, filtered to your wants list when we have one.
  function sellerPageUrl(m, seller, sampleName) {
    const id = WANTLIST?.id || null;
    return id ? sellerWantlistUrl(seller, id, 1) : sellerSearchUrl(seller, sampleName, 1, null);
  }

  async function diagnoseCart(m, r) {
    const out = document.querySelector('#cmSSO-cart-out');
    out.innerHTML = '<div class="small text-muted">Running checks…</div>';
    const notes = [];
    const p = r.lines.findIndex((l) => l.length);
    if (p < 0) { out.innerHTML = '<div class="alert alert-warning">Nothing in this basket.</div>'; return; }
    const seller = m.sellerNames[r.idx[p]];
    const url = sellerPageUrl(m, seller, m.wanted[r.lines[p][0].i].name);
    notes.push(`seller: ${seller}`, `page:   ${url}`);

    let articleId = null;
    try {
      const doc = await httpGetDoc(url);
      const rows = parseOfferRows(doc);
      articleId = rows.find((x) => x.articleId)?.articleId || null;
      notes.push(`offer rows: ${rows.length}, first article ${articleId || 'none'}`);
      notes.push(`  language readable on ${rows.filter((x) => x.language).length}/${rows.length} rows`);
      notes.push(`  counts: ${rows.slice(0, 8).map((x) => x.count).join(',')}`);
      notes.push(`  token present: ${!!doc.querySelector('input[name="__cmtkn"]')}`);
    } catch (e) { notes.push(`offer page FAILED: ${e.message}`); }

    if (articleId) {
      const modal = `${location.origin}/${LANG_SEG}/${GAME_SEG}/Modal/Article_PutSingleInShoppingCart`
        + `?idArticle=${articleId}&ajaxAction=${CART_ACTION}&ajaxCB=Offers.addArticlesCB`;
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
      } catch (e) { notes.push(`modal FAILED: ${e.message}`); }
    }

    const snap = await cartSnapshot();
    const ids = snap ? (snap.html.match(/idArticle\D{0,6}(\d{6,})/g) || []).length : 0;
    notes.push(`remembered request shape: ${localStorage.getItem(ROUTE_KEY) || 'none yet'}`);
    notes.push(`cart: ${snap ? `value ${euro(snap.value)}, ${snap.html.length} chars, ~${ids} article-id mentions` : 'unreadable'}`);
    console.log('[cmSSO] add-to-cart diagnostics\n' + notes.join('\n'));
    out.innerHTML = `<div class="alert alert-info">
      <strong>Add-to-cart diagnostics</strong>
      <pre class="small mb-1 mt-2" style="white-space:pre-wrap">${esc(notes.join('\n'))}</pre>
      <div class="small">Nothing was added. Copy this text over and it pins down the fix.</div></div>`;
  }

  /*
   * Rendering helpers
   */

  function sellerLink(s) {
    return `<a href="/${LANG_SEG}/${GAME_SEG}/Users/${encodeURIComponent(s)}/Offers/Singles" target="_blank" rel="noopener">${esc(s)}</a>`;
  }
  function cardSearchLink(name) {
    return `<a href="/${LANG_SEG}/${GAME_SEG}/Products/Search?searchString=${encodeURIComponent(name)}" target="_blank" rel="noopener">${esc(name)}</a>`;
  }
  function gapList(m, gaps, limit = 60) {
    if (!gaps.length) return '<span class="text-success">nothing missing</span>';
    const items = gaps.slice(0, limit).map((g) =>
      `<li>${cardSearchLink(m.wanted[g.i].name)}${g.qty > 1 ? ` ×${g.qty}` : ''}
        <span class="text-muted">— ${euro(g.price)} at ${esc(g.seller)}</span></li>`).join('');
    return `<ul class="mb-0 ps-3">${items}${gaps.length > limit ? `<li class="text-muted">+${gaps.length - limit} more</li>` : ''}</ul>`;
  }
  const plural = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;
  function vsWizard(total, wiz) {
    if (wiz.wizardTotal == null) return '';
    const d = total - wiz.wizardTotal;
    return `<span class="${d < 0 ? 'text-success' : 'text-danger'}">${d < 0 ? '−' : '+'}${euro(Math.abs(d))} vs the wizard</span>`;
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
   * says nobody stocks one of those, the scan is wrong, not the market.
   */
  function wizardContradictions(m, wiz) {
    const byKey = new Map();
    (wiz.sellers || []).forEach((s) => (s.articles || []).forEach((a) => {
      const k = normName(a.name);
      if (!byKey.has(k)) byKey.set(k, { seller: s.username, price: a.price });
    }));
    return m.nobodyHas.map((w) => ({ w, hit: byKey.get(w.key) })).filter((x) => x.hit);
  }

  /*
   * Results: one hero card with the parcel picker and the cart button, the
   * chosen basket underneath, then insights, and the deep-dive tables folded.
   */

  let VIEW = null;       // last scan, unfiltered
  let STATE = null;      // current analysis + selected basket
  let excluded = new Set(readJSON(EXCL_KEY, []));
  let cardsOpen = false;
  let singlesOpen = false;
  let cardFilter = '';

  function saveExcluded() { writeJSON(EXCL_KEY, [...excluded]); }

  function renderHero(m, search) {
    const sizes = search.bestByK.map((r, k) => (r ? { k, r } : null)).filter(Boolean);
    const cheapest = search.complete[0];
    const chips = sizes.map(({ k, r }) => `<button type="button" data-act="k" data-k="${k}"
        class="btn btn-sm cmSSO-k ${r === cheapest ? 'btn-outline-success' : 'btn-outline-secondary'}">
        ${plural(k, 'parcel')}<small>${euro(r.total)}${r === cheapest ? ' ★' : ''}</small></button>`).join('');
    return `
      <div class="border rounded p-3 mb-3 cmSSO-hero">
        ${sizes.length
          ? `<div class="small text-muted mb-2">How many parcels? Every option buys all ${m.reachableUnits} available
              cards, so the prices compare directly. ★ is the cheapest.</div>
             <div class="d-flex flex-wrap gap-2 mb-3">${chips}</div>`
          : '<div class="alert alert-warning py-2">No line-up covers every card. Pick a seller from the table below.</div>'}
        <div id="cmSSO-pick"></div>
        <div class="d-flex flex-wrap gap-2 mt-3 align-items-center">
          <button type="button" data-act="add" class="btn btn-success"><span class="fonticon-cart me-2"></span>Add to cart</button>
          <button type="button" data-act="check" class="btn btn-sm btn-outline-secondary">Check availability</button>
          <button type="button" data-act="copy" class="btn btn-sm btn-outline-secondary">Copy list</button>
          <button type="button" data-act="stop" class="btn btn-sm btn-outline-danger" hidden>Stop</button>
          <button type="button" data-act="diag" class="btn btn-sm btn-link text-muted ms-auto">Diagnose cart</button>
        </div>
        <div id="cmSSO-cart-out" class="mt-2"></div>
      </div>
      <div id="cmSSO-detail"></div>`;
  }

  function showBasket(r) {
    if (!STATE || !r) return;
    const { m, search, wiz } = STATE;
    STATE.basket = r;
    const cheapest = search.complete[0];
    document.querySelectorAll('#cmSSO [data-act="k"]').forEach((b) => {
      b.classList.toggle('active', search.bestByK[+b.getAttribute('data-k')] === r);
    });
    const extra = cheapest ? r.total - cheapest.total : 0;
    const fin = r.missingUnits ? completeOf(m, r.idx) : null;
    const pick = document.querySelector('#cmSSO-pick');
    if (pick) {
      pick.innerHTML = `
        <div class="d-flex justify-content-between flex-wrap gap-2 align-items-end">
          <div>${r.sellers.map(sellerLink).join(' + ')}
            <div class="small text-muted">${plural(r.found, 'card')} · ${plural(r.idx.length, 'parcel')}</div></div>
          <div class="text-end"><span class="fs-4 fw-bold">${euro(r.total)}</span>
            <div class="small text-muted">${euro(r.cardCost)} cards + ${euro(r.ship)} shipping</div></div>
        </div>
        <div class="small mt-1">
          ${!cheapest || extra < 0.005 ? '<span class="badge text-bg-success">cheapest</span>' : `<span class="text-muted">${euro(extra)} more than the cheapest</span>`}
          ${wiz.wizardTotal != null ? ` · ${vsWizard(r.total, wiz)}` : ''}
          ${r.missingUnits ? ` · <span class="text-danger">misses ${plural(r.missingUnits, 'card')}</span>
            — cheapest finish: ${fin.added.map(sellerLink).join(' + ') || 'none in this scan'}, ${euro(fin.combo.total)} all in` : ''}
        </div>`;
    }
    const cartOut = document.querySelector('#cmSSO-cart-out');
    if (cartOut && !STATE.busy) cartOut.innerHTML = '';
    renderDetail(m, r);
  }

  function renderDetail(m, r) {
    const box = document.querySelector('#cmSSO-detail');
    if (!box) return;
    const perSeller = r.idx.map((j, p) => {
      const line = r.lines[p].slice().sort((a, b) => m.wanted[a.i].name.localeCompare(m.wanted[b.i].name));
      const sampleName = line.length ? m.wanted[line[0].i].name : (m.wanted[0] || {}).name || '';
      return `<div class="col-12 col-md-6 col-xl-4 mb-3">
        <div class="border rounded p-2 h-100">
          <div class="d-flex justify-content-between flex-wrap gap-1">
            <strong><a href="${sellerPageUrl(m, m.sellerNames[j], sampleName)}" target="_blank" rel="noopener"
              title="Open this seller's offers filtered to your list">${esc(m.sellerNames[j])}</a></strong>
            <span class="small text-muted">${line.length} · ${euro(line.reduce((a, x) => a + x.price, 0))} + ${euro(m.ship[j])}</span>
          </div>
          <ul class="mb-0 ps-3 cmSSO-small mt-1">
            ${line.map((x) => `<li>${esc(m.wanted[x.i].name)} <span class="text-muted">${euro(x.price)}</span></li>`).join('') || '<li class="text-muted">nothing</li>'}
          </ul>
        </div></div>`;
    }).join('');

    const fillers = r.missingUnits ? gapFillers(m, r) : [];
    box.innerHTML = `
      <div class="row">${perSeller}</div>
      ${r.gaps.length ? `<div class="row">
        <div class="col-12 col-lg-6 mb-3"><h6>Missing from this basket</h6><div class="cmSSO-small">${gapList(m, r.gaps)}</div></div>
        <div class="col-12 col-lg-6 mb-3"><h6>Best seller to add next</h6>
          <table class="table table-sm cmSSO-small"><thead><tr><th class="text-start">Seller</th><th class="text-center">Cards added</th>
            <th class="text-end">New total</th></tr></thead>
          <tbody>${fillers.map((f) => `<tr><td class="text-start">${sellerLink(f.seller)}</td>
            <td class="text-center">+${f.adds}</td><td class="text-end">${euro(f.result.total)}</td></tr>`).join('')
            || '<tr><td colspan="3" class="text-muted">nothing left to add</td></tr>'}</tbody></table></div>
      </div>` : ''}`;
  }

  function renderInsights(m, search, wiz, singles) {
    const items = [];
    const bestSingle = singles.slice().sort((a, b) => b.found - a.found || a.total - b.total)[0];
    if (bestSingle) {
      const done = completeOf(m, bestSingle.idx);
      items.push(`<li><strong>Biggest single seller:</strong> ${sellerLink(bestSingle.sellers[0])} has
        ${bestSingle.found} of ${m.reachableUnits} cards (${euro(bestSingle.total)}).
        ${bestSingle.gaps.length
          ? `Topped up from ${done.added.map(sellerLink).join(' + ') || 'nobody in this scan'}: ${euro(done.combo.total)} all in.`
          : 'It covers everything on its own.'}</li>`);
    }

    const draggers = m.wanted.map((w, i) => ({ w, c: costOfCard(m, search, i) }))
      .filter((x) => x.c && x.c.saving > 0.01 && x.c.fewerParcels > 0)
      .sort((a, b) => b.c.saving - a.c.saving);
    if (draggers.length) {
      const top = draggers[0];
      items.push(`<li><strong>${cardSearchLink(top.w.name)} costs more than it looks:</strong> dropping it saves
        ${euro(top.c.saving)} and ${plural(top.c.fewerParcels, 'parcel')} — the card is ${euro(top.c.cardSaved)},
        the rest is shipping it drags along.${draggers.length > 1 ? ` ${draggers.length - 1} more like it in the card list.` : ''}</li>`);
    }

    const clashes = wizardContradictions(m, wiz);
    if (clashes.length) {
      items.push(`<li class="text-danger"><strong>The scan missed ${plural(clashes.length, 'card')} the wizard did find:</strong>
        ${clashes.slice(0, 6).map((x) => cardSearchLink(x.w.name)).join(', ')}${clashes.length > 6 ? ` +${clashes.length - 6}` : ''}.
        Usually a saved scan from another wants list or older list options — clear saved prices and scan again.</li>`);
    }
    if (m.nobodyHas.length) {
      items.push(`<li><strong>Not available from these ${m.S} sellers:</strong>
        ${m.nobodyHas.map((w) => cardSearchLink(w.name)).join(', ')} — not in any total above.</li>`);
    }
    return items.length ? `<ul class="small mb-3 ps-3">${items.join('')}</ul>` : '';
  }

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
    const rows = stats.map((st, n) => {
      const off = excluded.has(st.w.key);
      const i = m.wanted.findIndex((x) => x.key === st.w.key);
      const cost = (!off && i >= 0) ? costOfCard(m, search, i) : null;
      const worth = cost && cost.saving > 0.01;
      return {
        st, off, sort: worth ? cost.saving : -1,
        html: `<tr class="${off ? 'text-muted' : ''}" data-name="${esc(st.w.key)}">
          <td class="text-start"><div class="form-check mb-0">
            <input class="form-check-input" type="checkbox" data-card="${esc(st.w.key)}" id="cmSSO-cx-${n}" ${off ? '' : 'checked'}>
            <label class="form-check-label" for="cmSSO-cx-${n}">${esc(st.w.name)}${st.w.qty > 1 ? ` ×${st.w.qty}` : ''}</label>
          </div></td>
          <td class="text-end">${st.cheapest == null ? '<span class="text-danger">none</span>' : euro(st.cheapest)}</td>
          <td class="text-center">${st.sellers}</td>
          <td class="text-end">${off ? '<span class="text-muted">parked</span>'
            : worth ? `<span class="text-success fw-bold">−${euro(cost.saving)}</span>
                ${cost.fewerParcels > 0
                  ? `<div class="small text-warning-emphasis">drops ${plural(cost.fewerParcels, 'parcel')}</div>` : ''}`
            : '<span class="text-muted">—</span>'}</td>
        </tr>`,
      };
    });
    rows.sort((a, b) => b.sort - a.sort || a.st.w.name.localeCompare(b.st.w.name));

    const off = stats.filter((st) => excluded.has(st.w.key)).length;
    const lonely = stats.filter((st) => st.sellers === 1 && !excluded.has(st.w.key)).length;

    return `
      <details id="cmSSO-cards" class="mb-2" ${cardsOpen ? 'open' : ''}>
        <summary><strong>Cards: ${stats.length - off} of ${stats.length} included</strong>
          ${off ? `<span class="text-muted"> · ${off} parked</span>` : ''}
          <span class="text-muted small"> · untick a maybe and everything recalculates</span></summary>
        <div class="d-flex flex-wrap gap-2 my-2 align-items-center">
          <input type="search" class="form-control form-control-sm" id="cmSSO-cardfilter" placeholder="Find a card…"
            style="max-width:14rem" value="${esc(cardFilter)}">
          <div class="input-group input-group-sm" style="width:13rem">
            <span class="input-group-text">Park over</span>
            <input type="number" class="form-control" id="cmSSO-overprice" min="0" step="0.5" value="5" aria-label="price limit">
            <span class="input-group-text">€</span>
            <button type="button" class="btn btn-outline-secondary" data-bulk="over">Go</button>
          </div>
          ${lonely ? `<button type="button" class="btn btn-sm btn-outline-secondary" data-bulk="lonely">Park ${plural(lonely, 'single-seller card')}</button>` : ''}
          ${off ? '<button type="button" class="btn btn-sm btn-outline-secondary" data-bulk="reset">Include everything</button>' : ''}
        </div>
        <div class="table-responsive" style="max-height:24rem;overflow-y:auto">
          <table class="table table-sm table-striped align-middle mb-0" id="cmSSO-cardtable">
            <thead class="position-sticky top-0 bg-white"><tr>
              <th class="text-start">Card</th><th class="text-end">Cheapest</th>
              <th class="text-center">Sellers</th><th class="text-end" title="How much the cheapest complete order drops without this card">Dropping saves</th>
            </tr></thead>
            <tbody>${rows.map((r) => r.html).join('')}</tbody>
          </table>
        </div>
      </details>`;
  }

  function applyCardFilter() {
    const q = normName(cardFilter);
    document.querySelectorAll('#cmSSO-cardtable tbody tr').forEach((tr) => {
      tr.hidden = !!q && !(tr.getAttribute('data-name') || '').includes(q);
    });
  }

  function wireCards(stats) {
    const det = document.querySelector('#cmSSO-cards');
    if (!det) return;
    det.addEventListener('toggle', () => { cardsOpen = det.open; });
    const filter = det.querySelector('#cmSSO-cardfilter');
    filter?.addEventListener('input', () => { cardFilter = filter.value; applyCardFilter(); });
    applyCardFilter();

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

  function renderSingles(m, wiz, singles) {
    const rows = singles.slice().sort((a, b) => b.found - a.found || a.total - b.total).map((r) => {
      const s = r.sellers[0];
      const country = wiz.sellers.find((x) => x.username === s)?.country || '';
      const done = completeOf(m, r.idx);
      return `<tr data-single="${r.idx[0]}">
        <td class="text-start">${sellerLink(s)} <span class="text-muted small">${esc(country)}</span></td>
        <td class="text-center" style="min-width:6rem">${r.found} / ${m.reachableUnits}<div class="cmSSO-bar mt-1"><i style="width:${pct(r.coverage)}"></i></div></td>
        <td class="text-end">${euro(r.total)}<div class="text-muted small">${euro(r.ship)} ship</div></td>
        <td class="text-end fw-bold">${euro(done.combo.total)}
          <div class="text-muted small fw-normal">${done.added.length ? `+ ${esc(done.added.join(', '))}` : 'on its own'}</div></td>
      </tr>`;
    }).join('');
    return `
      <details id="cmSSO-singles-wrap" class="mb-2" ${singlesOpen ? 'open' : ''}>
        <summary><strong>Every seller on its own</strong>
          <span class="text-muted small"> · click a row to load it above</span></summary>
        <div class="table-responsive mt-2">
          <table class="table table-sm table-striped table-hover align-middle mb-0" id="cmSSO-singles">
            <thead><tr><th class="text-start">Seller</th><th class="text-center">Cards</th>
              <th class="text-end">Alone</th><th class="text-end" title="Plus the cheapest sellers for what it lacks">Complete order</th></tr></thead>
            <tbody>${rows}</tbody>
          </table>
        </div>
      </details>`;
  }

  function renderResults(wiz, wanted, matrix, shipping, sellerNames) {
    VIEW = { wiz, wanted, matrix, shipping, sellerNames };
    draw();
  }

  function draw() {
    if (!VIEW) return;
    const { wiz, wanted, matrix, shipping, sellerNames } = VIEW;
    const scrollY = window.scrollY;
    const active = wanted.filter((w) => !excluded.has(w.key));
    if (!active.length) {
      STATE = null;
      document.querySelector('#cmSSO-results').innerHTML =
        `<hr><div class="alert alert-warning">Every card is parked. Tick at least one to see an analysis.</div>
         ${renderCards(buildModel([], matrix, shipping, sellerNames), { complete: [] }, cardStats(wanted, matrix, sellerNames))}`;
      wireCards(cardStats(wanted, matrix, sellerNames));
      return;
    }
    drawAnalysis(wiz, active, wanted, matrix, shipping, sellerNames);
    window.scrollTo({ top: scrollY });
  }

  function drawAnalysis(wiz, wanted, allWanted, matrix, shipping, sellerNames) {
    const m = buildModel(wanted, matrix, shipping, sellerNames);
    const stats = cardStats(allWanted, matrix, sellerNames);
    const results = document.querySelector('#cmSSO-results');

    // Nothing found anywhere is a broken scan, not an answer.
    if (!m.reachableUnits) {
      STATE = null;
      results.innerHTML = `
        <hr>
        <div class="alert alert-danger">
          <h5 class="mb-2">The scan found none of your cards</h5>
          <p class="mb-2">Not one of the ${m.S} sellers matched a single card, which means the scan
            failed rather than the sellers being empty.</p>
          <ul class="mb-2">
            <li>The card names on the sellers' pages did not match your list.</li>
            <li>The options on your wants list (language, condition, expansion) may be too tight.</li>
            <li>The wants list shown above may not be the one this wizard run used.</li>
          </ul>
          <button type="button" class="btn btn-sm btn-outline-danger" data-act="wipe">Clear saved prices and start over</button>
        </div>`;
      return;
    }

    const search = searchBaskets(m, Math.min(cfg.maxCombo, sellerNames.length));
    const singles = [];
    for (let j = 0; j < m.S; j++) singles.push(evalCombo(m, [j]));
    STATE = { m, search, wiz, singles, basket: null, busy: false };

    const parked = allWanted.filter((w) => excluded.has(w.key)).length;
    results.innerHTML = `
      <hr>
      ${renderHero(m, search)}
      ${renderInsights(m, search, wiz, singles)}
      ${renderCards(m, search, stats)}
      ${renderSingles(m, wiz, singles)}
      <p class="small text-muted mt-3 mb-0">
        ${wiz.wizardTotal != null ? `Wizard: ${euro(wiz.wizardTotal)}${wiz.wizardCards != null ? ` (${euro(wiz.wizardCards)} cards + ${euro(wiz.wizardShipping)} shipping${wiz.wizardShipments ? `, ${plural(wiz.wizardShipments, 'parcel')}` : ''})` : ''}. ` : ''}
        ${m.wantedUnits} cards against ${m.S} sellers; ${m.reachableUnits} exist somewhere in this scan.
        ${parked ? `${plural(parked, 'card')} parked.` : ''}
        Shipping is taken from the wizard page — a bigger parcel can cost a little more to ship.
      </p>`;

    wireCards(stats);
    const sd = document.querySelector('#cmSSO-singles-wrap');
    sd?.addEventListener('toggle', () => { singlesOpen = sd.open; });
    showBasket(search.complete[0] || singles.slice().sort((a, b) => b.found - a.found || a.total - b.total)[0]);
  }

  // One delegated handler for everything inside the results, installed once.
  async function onResultsClick(e) {
    const t = e.target;
    const actEl = t.closest('[data-act]');
    const act = actEl?.getAttribute('data-act');

    if (act === 'wipe') {
      cache = {};
      cacheFlush();
      localStorage.removeItem(SCAN_KEY);
      document.querySelector('#cmSSO-results').innerHTML =
        '<hr><div class="alert alert-info">Cleared. Adjust the settings above and run the scan again.</div>';
      return;
    }
    if (!STATE) return;
    const { m, search } = STATE;

    if (act === 'k') { showBasket(search.bestByK[+actEl.getAttribute('data-k')]); return; }
    if (act === 'stop') { aborted = true; return; }

    const row = t.closest('tr[data-single]');
    if (row && !t.closest('a, details > summary, button')) {
      showBasket(evalCombo(m, [+row.getAttribute('data-single')]));
      document.querySelector('#cmSSO-results .cmSSO-hero')?.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
      return;
    }

    const r = STATE.basket;
    if (!r || !act || STATE.busy) return;

    if (act === 'copy') {
      const text = shoppingList(m, r);
      if (await copyText(text)) {
        actEl.textContent = 'Copied';
        setTimeout(() => { actEl.textContent = 'Copy list'; }, 1500);
        return;
      }
      const out = document.querySelector('#cmSSO-cart-out');
      out.innerHTML = `<div class="alert alert-info mb-0">
        <div class="small mb-1">Your browser blocked the clipboard — select and copy this:</div>
        <textarea class="form-control form-control-sm" rows="8" readonly></textarea></div>`;
      const ta = out.querySelector('textarea');
      ta.value = text;
      ta.focus();
      ta.select();
      return;
    }

    if (act === 'add' || act === 'check' || act === 'diag') {
      if (act === 'add') {
        const n = r.lines.reduce((a, l) => a + l.length, 0);
        if (!confirm(`Add ${n} cards from ${r.sellers.length} seller${r.sellers.length === 1 ? '' : 's'} to your Cardmarket cart?\n\n`
          + 'This does not buy anything — you review each order in the cart before checkout. '
          + 'Articles already in your cart are detected and skipped.')) return;
      }
      STATE.busy = true;
      const hero = document.querySelector('#cmSSO-results .cmSSO-hero');
      const btns = hero ? [...hero.querySelectorAll('button[data-act]:not([data-act="stop"])')] : [];
      const stop = hero?.querySelector('[data-act="stop"]');
      btns.forEach((b) => { b.disabled = true; });
      if (stop && act !== 'diag') stop.hidden = false;
      try {
        if (act === 'diag') await diagnoseCart(m, r);
        else await addBasketToCart(m, r, { dryRun: act === 'check' });
      } catch (err) {
        const out = document.querySelector('#cmSSO-cart-out');
        if (out) out.innerHTML = `<div class="alert alert-danger">Stopped: ${esc(err.message)}</div>`;
      } finally {
        STATE && (STATE.busy = false);
        btns.forEach((b) => { b.disabled = false; });
        if (stop) stop.hidden = true;
      }
    }
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

    try {
      // 1. Wanted cards
      // The cards are the ones this wizard run placed; the wants list filters
      // each seller's offers down to them, with each card's own options.
      const wanted = wantedFromWizard(wiz);
      if (!wanted.length) { ui.note('No cards to look for.', 'warn'); return; }
      if (wantlistReady) await wantlistReady;
      const wantlistId = WANTLIST?.id || null;
      const fast = !!wantlistId;
      if (!fast) {
        ui.note('No wants list found for this wizard run, so cards are searched by name without '
          + 'your list options (language, condition, expansion). Expect other printings.', 'warn');
      }

      // Every seller gets scanned; the ranking only decides the order, so a
      // stopped run still has the most useful sellers done.
      const sellerNames = rankSellers(wiz.sellers).map((x) => x.username);
      const shipping = {};
      wiz.sellers.forEach((x) => { shipping[x.username] = x.shipping ?? cfg.defaultShipping; });

      ui.note('Keep this tab open while it runs. Each seller is saved as it finishes, '
        + 'so running again picks up where it stopped.');
      if (fast) ui.note(`Wants list: ${WANTLIST.name} — its per-card options apply.`);

      const fresh = sellerNames.filter((n) => !cacheGet(n, SCANNED_MARK));
      const pagesEach = Math.max(1, Math.ceil((wanted.length * 3) / 20));   // ~3 printings per card, ~20 rows a page
      const reqs = fast ? fresh.length * pagesEach : fresh.length * wanted.length;
      const mins = Math.max(1, Math.round((reqs * ((cfg.minDelay + cfg.maxDelay) / 2)) / (fast ? 1 : cfg.concurrency) / 60000));
      ui.note(`${fresh.length} of ${sellerNames.length} sellers need scanning — roughly ${plural(mins, 'minute')}. The rest come from the last scan.`);

      // 2. Scrape
      const matrix = {};
      const wantedByKey = new Map(wanted.map((w) => [w.key, w]));
      const total = sellerNames.length * wanted.length;
      let done = 0;
      let reused = 0;
      const started = Date.now();
      const eta = () => {
        const spent = (Date.now() - started) / 1000;
        const work = Math.max(1, done - reused);
        const left = Math.round((spent / work) * (total - done));
        return `about ${Math.floor(left / 60)}m ${left % 60}s left`;
      };

      for (const seller of sellerNames) {
        if (aborted) break;
        matrix[seller] = {};

        // Reuse a seller only when the earlier sweep covered every card we ask about now.
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

            // The wizard proved which cards this seller stocks. If the sweep
            // missed one, look it up by name rather than recording it as unstocked.
            const proof = [...new Set((wiz.sellers.find((x) => x.username === seller)?.articles || [])
              .map((a) => normName(a.name))
              .filter((k) => wantedByKey.has(k) && !(matrix[seller][k] || []).length))];

            if (proof.length) {
              let recovered = 0;
              for (const key of proof) {
                if (aborted) break;
                try {
                  const r = await offersFor(seller, wantedByKey.get(key), true);
                  matrix[seller][key] = r.units;
                  if (r.units.length) recovered++;
                  if (!r.cached) await sleep(jitter());
                } catch { /* leave it empty */ }
              }
              if (recovered < proof.length) {
                ui.note(`${seller}: ${proof.length - recovered} card${proof.length - recovered === 1 ? '' : 's'} the wizard found there `
                  + 'are not listed there with your wants-list options (or have sold).', 'warn');
              }
            }

            if (res.hitCap) ui.note(`${seller}: stopped at the ${res.pages}-page limit.`, 'warn');
            done += wanted.length;
            ui.progress(done, total, `${seller} — ${plural(res.pages, 'page')} · ${eta()}`);
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
              const r = await offersFor(seller, want);
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
            if (!hitCache) await sleep(jitter());
          }
        };
        await Promise.all(Array.from({ length: cfg.concurrency }, worker));
        if (!aborted) cacheSet(seller, SCANNED_MARK, [1]);
        cacheFlush();
      }

      cacheFlush();
      const usable = sellerNames.filter((s) => matrix[s]);
      writeJSON(SCAN_KEY, { t: Date.now(), wanted, matrix, shipping, sellerNames: usable });
      panel.querySelector('#cmSSO-reanalyse').hidden = false;
      ui.progress(done, total, aborted ? 'Stopped — showing what was collected' : 'Done');
      renderResults(wiz, wanted, matrix, shipping, usable);
      document.querySelector('#cmSSO-results').scrollIntoView({ behavior: 'smooth', block: 'start' });
    } finally {
      runBtn.disabled = false;
      stopBtn.hidden = true;
    }
  }

  /*
   * Page samples: the raw HTML (what a fetch sees, scripts not run) of every
   * page this script parses, bundled into one JSON file. Session tokens are
   * blanked out before saving.
   */
  async function saveSamples(wiz, panel) {
    panel.querySelector('#cmSSO-progress').hidden = false;
    const base = `${location.origin}/${LANG_SEG}/${GAME_SEG}`;
    if (wantlistReady) await wantlistReady;
    const listId = WANTLIST?.id || null;
    const seller = wiz.sellers.find((s) => s.articles.length)?.username || wiz.sellers[0]?.username;
    const pages = [
      ['wizard-results', location.href],
      ['wants-overview', `${base}/Wants`],
      listId && ['wantlist', `${base}/Wants/${listId}`],
      listId && seller && ['seller-wants-filtered', sellerWantlistUrl(seller, listId, 1)],
      seller && ['seller-offers', `${base}/Users/${encodeURIComponent(seller)}/Offers/Singles`],
      ['cart', `${base}/ShoppingCart`],
    ].filter(Boolean);

    const scrub = (html) => html
      .replace(/(name=["']__cmtkn["'][^>]*value=["'])[^"']*/gi, '$1REDACTED')
      .replace(/(value=["'])[^"']*(["'][^>]*name=["']__cmtkn)/gi, '$1REDACTED$2')
      .replace(/("__cmtkn"\s*:\s*")[^"]*/g, '$1REDACTED');

    const out = { saved: new Date().toISOString(), script: '2.3.0', listId, seller, pages: {},
      renderedWizard: scrub(document.documentElement.outerHTML) };
    for (const [name, url] of pages) {
      ui.note(`Saving ${name}…`);
      try {
        const res = await fetch(url, { credentials: 'same-origin', cache: 'no-store' });
        out.pages[name] = { url, status: res.status, html: scrub(await res.text()) };
      } catch (e) {
        out.pages[name] = { url, error: String(e.message) };
      }
      await sleep(jitter());
    }
    const blob = new Blob([JSON.stringify(out, null, 1)], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = `cardmarket-samples-${Date.now()}.json`;
    document.body.appendChild(a);
    a.click();
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 5000);
    ui.note('Samples saved to your downloads. Contains your username and lists; session tokens are removed.');
  }

  /*
   * Boot
   */

  let wantlistReady = null;

  function boot() {
    if (document.querySelector('#cmSSO')) return;
    // The wizard form: only note which wants list it runs on.
    if (!/\/ShoppingWizard\/Results\//.test(location.pathname)) { rememberWizardList(); return; }
    const wiz = parseWizard();
    if (!wiz.sellers.length) return;

    injectStyles();
    const panel = buildPanel(wiz);
    panel.querySelector('#cmSSO-results').addEventListener('click', onResultsClick);

    const info = panel.querySelector('#cmSSO-wantlist');
    wantlistReady = (async () => {
      try {
        WANTLIST = await detectWantlist(wiz, (t) => { info.textContent = t; });
      } catch { WANTLIST = null; }
      if (WANTLIST) {
        const href = `/${LANG_SEG}/${GAME_SEG}/Wants/${WANTLIST.id}`;
        info.innerHTML = `<a href="${href}" target="_blank" rel="noopener"><strong>${esc(WANTLIST.name)}</strong></a>
          <span class="text-muted">· ${esc(WANTLIST.how)}${WANTLIST.coverage < 0.95 ? `, ${pct(WANTLIST.coverage)} of the cards match` : ''}</span>`;
      } else {
        info.innerHTML = '<span class="text-danger">Could not tell which wants list this wizard ran on.</span> '
          + '<span class="text-muted">Open the wizard from your wants list and run it again, or scan anyway (searches by name, ignores list options).</span>';
      }
    })();

    panel.querySelector('#cmSSO-run').addEventListener('click', () => run(wiz, panel));

    const reBtn = panel.querySelector('#cmSSO-reanalyse');
    const saved = readJSON(SCAN_KEY, null);
    if (saved && saved.sellerNames?.length) {
      reBtn.hidden = false;
      reBtn.title = `Show the scan from ${new Date(saved.t).toLocaleString()} again`;
    }
    reBtn.addEventListener('click', () => {
      const scan = readJSON(SCAN_KEY, null);
      if (!scan) return;
      renderResults(wiz, scan.wanted, scan.matrix, scan.shipping, scan.sellerNames);
    });
    panel.querySelector('#cmSSO-stop').addEventListener('click', () => {
      aborted = true;
      ui.note('Stopping after the requests in flight…');
    });
    panel.querySelector('#cmSSO-samples').addEventListener('click', async (ev) => {
      const btn = ev.currentTarget;
      btn.disabled = true;
      try { await saveSamples(wiz, panel); } finally { btn.disabled = false; }
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
