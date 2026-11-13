'use strict';
/* =====================================================================
   Tummy Express — algorithms + UI
   Node numbering used by the distance matrix D (metres):
     0                 = restaurant
     1 .. R            = riders
     R+1 .. R+N        = customers
   ===================================================================== */

// ==== ALGORITHMS ====
const SPEED_KMH = 25;
const km = m => (m / 1000).toFixed(2);
const minutesFor = m => (m / 1000) / SPEED_KMH * 60;

function haversine(a, b) {
  const t = x => x * Math.PI / 180, R = 6371000;
  const dLa = t(b[0] - a[0]), dLo = t(b[1] - a[1]);
  const h = Math.sin(dLa / 2) ** 2 + Math.cos(t(a[0])) * Math.cos(t(b[0])) * Math.sin(dLo / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(h));
}
function fallbackMatrix(pts) {
  return pts.map((a, i) => pts.map((b, j) => (i === j ? 0 : haversine(a, b) * 1.3)));
}

// cost of rider r delivering order o: ride to restaurant, then to customer
function legCost(D, R, r, o) { return D[1 + r][0] + D[0][1 + R + o]; }

// 1) Brute force: try every injective rider -> order assignment
function bruteForce(D, R, N) {
  let steps = 0, best = Infinity, bestAssign = null;
  const used = new Array(R).fill(false), cur = new Array(N).fill(-1);
  const improvements = [], sample = [];
  (function rec(o, sum) {
    if (o === N) {
      steps++;
      if (sample.length < 6) sample.push({ assign: cur.slice(), total: sum });
      if (sum < best - 1e-9) {
        best = sum; bestAssign = cur.slice();
        improvements.push({ assign: cur.slice(), total: sum, step: steps });
      }
      return;
    }
    for (let r = 0; r < R; r++) {
      if (used[r]) continue;
      used[r] = true; cur[o] = r;
      rec(o + 1, sum + legCost(D, R, r, o));
      used[r] = false;
    }
  })(0, 0);
  return { assign: bestAssign, total: best, steps, improvements, sample };
}

// 2) Divide & conquer: cheapest item by splitting the list in halves
function cheapestDC(items) {
  let steps = 0;
  const trace = [];
  function solve(lo, hi, depth) {
    if (lo === hi) return items[lo];
    const mid = (lo + hi) >> 1;
    const L = solve(lo, mid, depth + 1);
    const Rt = solve(mid + 1, hi, depth + 1);
    steps++;
    const win = Rt.price < L.price ? Rt : L;
    trace.push({ depth, lo, hi, left: L, right: Rt, winner: win });
    return win;
  }
  const winner = solve(0, items.length - 1, 0);
  return { winner, steps, trace };
}

// 3) Dynamic programming: Held–Karp shortest path from restaurant through all customers
function heldKarp(D, R, N) {
  const cn = i => R + 1 + i, F = 1 << N;
  const dp = Array.from({ length: F }, () => new Array(N).fill(Infinity));
  const par = Array.from({ length: F }, () => new Array(N).fill(-1));
  let steps = 0;
  for (let j = 0; j < N; j++) { dp[1 << j][j] = D[0][cn(j)]; steps++; }
  for (let mask = 1; mask < F; mask++) {
    for (let j = 0; j < N; j++) {
      if (!(mask & (1 << j)) || dp[mask][j] === Infinity) continue;
      for (let k = 0; k < N; k++) {
        if (mask & (1 << k)) continue;
        steps++;
        const nm = mask | (1 << k), v = dp[mask][j] + D[cn(j)][cn(k)];
        if (v < dp[nm][k]) { dp[nm][k] = v; par[nm][k] = j; }
      }
    }
  }
  let end = 0, total = Infinity;
  for (let j = 0; j < N; j++) if (dp[F - 1][j] < total) { total = dp[F - 1][j]; end = j; }
  const order = [];
  let mask = F - 1, j = end;
  while (j !== -1) { order.push(j); const pj = par[mask][j]; mask ^= (1 << j); j = pj; }
  order.reverse();
  const legs = order.map((c, i) => (i === 0 ? D[0][cn(c)] : D[cn(order[i - 1])][cn(c)]));
  return { order, total, steps, legs, states: F * N };
}

// 4) Greedy: each order (in sequence) gets the nearest free rider (to the restaurant)
function greedyAssign(D, R, N) {
  const used = new Array(R).fill(false), assign = [], trace = [];
  let steps = 0, total = 0;
  for (let o = 0; o < N; o++) {
    let bestR = -1, bestD = Infinity;
    for (let r = 0; r < R; r++) {
      if (used[r]) continue;
      steps++;
      if (D[1 + r][0] < bestD) { bestD = D[1 + r][0]; bestR = r; }
    }
    used[bestR] = true; assign.push(bestR);
    total += legCost(D, R, bestR, o);
    trace.push({ order: o, rider: bestR, pickup: bestD });
  }
  return { assign, total, steps, trace };
}

// ==== UI ====
const $ = s => document.querySelector(s);
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const sleep = ms => new Promise(r => setTimeout(r, ms));
const PALETTE = ['#fc8019', '#38bdf8', '#a78bfa', '#4ade80', '#f472b6', '#facc15'];
const LIMITS = { riderMin: 2, riderMax: 6, orderMin: 2, orderMax: 5 };

const INFO = {
  brute: {
    title: 'Brute Force', cls: 'c-brute', paradigm: 'Exhaustive search',
    problem: 'Which rider should receive which order so the total distance is the smallest?',
    time: 'O(P(R,N)·N)', space: 'O(N)', stepLabel: 'Assignments tried',
    how: ['Treat each order as a slot and each rider as a candidate.', 'Recursively generate <b>every</b> way to give each order a different rider.', 'Cost of a pair = rider → restaurant + restaurant → customer (road km).', 'Keep the assignment with the smallest total. It is guaranteed optimal.']
  },
  dc: {
    title: 'Divide & Conquer', cls: 'c-dc', paradigm: 'Split · Solve · Merge',
    problem: 'Which food item in this batch of orders is the cheapest?',
    time: 'O(n)', space: 'O(log n)', stepLabel: 'Comparisons',
    how: ['<b>Divide</b> the order list into two halves.', '<b>Conquer</b> each half recursively until one item remains.', '<b>Combine</b> by comparing the two half-winners and keeping the cheaper.', 'Recurrence: T(n) = 2T(n/2) + O(1), so n − 1 comparisons.']
  },
  dp: {
    title: 'Dynamic Programming', cls: 'c-dp', paradigm: 'Held–Karp bitmask DP',
    problem: 'In what order should a rider visit every customer for the shortest road route?',
    time: 'O(n²·2ⁿ)', space: 'O(n·2ⁿ)', stepLabel: 'DP transitions',
    how: ['State = (set of customers already visited, last customer).', 'dp[mask][j] = shortest distance leaving the restaurant, visiting <b>mask</b>, ending at j.', 'Extend each state to every unvisited customer and keep the minimum.', 'Reconstruct the best route with parent pointers, then replay it on the map.']
  },
  greedy: {
    title: 'Greedy', cls: 'c-greedy', paradigm: 'Locally best choice',
    problem: 'Give every order the nearest free rider. Is it as good as the best assignment?',
    time: 'O(N·R)', space: 'O(R)', stepLabel: 'Distance checks',
    how: ['Take orders one by one in the order they arrived.', 'Pick the <b>nearest free rider</b> to the restaurant.', 'Lock that rider and never reconsider.', 'Fast, but can be worse than brute force. See the verdict below.']
  }
};

const S = {
  riders: [], customers: [], rest: null, D: null, fallback: false,
  results: null, tab: 'brute', startTime: Date.now(),
  map: null, tiles: null, layer: null, drawTok: 0, ride: null, routeCache: new Map()
};

/* ---------- theme ---------- */
function setTheme(t) {
  document.documentElement.setAttribute('data-theme', t);
  $('#themeBtn').textContent = t === 'dark' ? '🌙' : '☀️';
  try { localStorage.setItem('te-theme', t); } catch (e) { /* ignore */ }
  if (S.map) applyTiles();
}
function initTheme() {
  let t = 'dark';
  try { t = localStorage.getItem('te-theme') || (matchMedia('(prefers-color-scheme: light)').matches ? 'light' : 'dark'); } catch (e) { /* ignore */ }
  setTheme(t);
  $('#themeBtn').addEventListener('click', () => setTheme(document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark'));
}

/* ---------- small helpers ---------- */
function toast(msg) {
  const t = $('#toast'); t.textContent = msg; t.hidden = false;
  clearTimeout(toast.id); toast.id = setTimeout(() => (t.hidden = true), 3200);
}
function countUp(el, to) {
  const t0 = performance.now(), dur = 900;
  (function f(now) {
    const p = Math.min(1, (now - t0) / dur);
    el.textContent = Math.round(to * (1 - Math.pow(1 - p, 3))).toLocaleString('en-IN');
    if (p < 1) requestAnimationFrame(f);
  })(t0);
}
function confetti() {
  const box = document.createElement('div'); box.className = 'confetti';
  for (let i = 0; i < 44; i++) {
    const s = document.createElement('span');
    s.style.left = Math.random() * 100 + '%';
    s.style.background = PALETTE[i % PALETTE.length];
    s.style.animationDuration = 2 + Math.random() * 2 + 's';
    s.style.animationDelay = Math.random() * .6 + 's';
    box.appendChild(s);
  }
  document.body.appendChild(box);
  setTimeout(() => box.remove(), 4800);
}
function initReveal() {
  const io = new IntersectionObserver(es => es.forEach(e => { if (e.isIntersecting) { e.target.classList.add('in'); io.unobserve(e.target); } }), { threshold: .12 });
  document.querySelectorAll('.reveal').forEach(el => io.observe(el));
  document.querySelectorAll('[data-count]').forEach(el => countUp(el, +el.dataset.count));
}
function revealNow(root) { root.querySelectorAll('.reveal').forEach(el => el.classList.add('in')); }

/* ---------- form rows ---------- */
function updateCounts() {
  const nr = document.querySelectorAll('.rider-row').length, no = document.querySelectorAll('.order-row').length;
  $('#riderCount').textContent = `(${nr}/${LIMITS.riderMax})`;
  $('#orderCount').textContent = `(${no}/${LIMITS.orderMax})`;
  $('#addRider').disabled = nr >= LIMITS.riderMax;
  $('#addOrder').disabled = no >= LIMITS.orderMax;
  document.querySelectorAll('.rider-row .rm').forEach(b => (b.disabled = nr <= LIMITS.riderMin));
  document.querySelectorAll('.order-row .rm').forEach(b => (b.disabled = no <= LIMITS.orderMin));
  document.querySelectorAll('.rider-row .badge').forEach((b, i) => (b.textContent = i + 1));
  document.querySelectorAll('.order-row .badge').forEach((b, i) => (b.textContent = '#' + (i + 1)));
}
function addRider(name = '', place = '') {
  const d = document.createElement('div'); d.className = 'row rider-row';
  d.innerHTML = '<span class="badge">🛵</span><input class="r-name" placeholder="Rider name" autocomplete="off"><input class="r-place" placeholder="Where is the rider? e.g. Guindy" autocomplete="off"><button type="button" class="icon-btn rm" title="Remove">✕</button>';
  d.querySelector('.r-name').value = name; d.querySelector('.r-place').value = place;
  d.querySelector('.rm').addEventListener('click', () => { d.remove(); updateCounts(); });
  $('#riderList').appendChild(d); updateCounts();
}
function addOrder(cust = '', place = '', food = '', price = '') {
  const d = document.createElement('div'); d.className = 'row order-row';
  d.innerHTML = '<span class="badge">#</span><input class="o-cust" placeholder="Customer name" autocomplete="off"><input class="o-place" placeholder="Delivery place / address" autocomplete="off"><input class="o-food" placeholder="Food item" autocomplete="off"><input class="o-price" placeholder="Price ₹" inputmode="decimal" autocomplete="off"><button type="button" class="icon-btn rm" title="Remove">✕</button>';
  d.querySelector('.o-cust').value = cust; d.querySelector('.o-place').value = place;
  d.querySelector('.o-food').value = food; d.querySelector('.o-price').value = price;
  d.querySelector('.rm').addEventListener('click', () => { d.remove(); updateCounts(); });
  $('#orderList').appendChild(d); updateCounts();
}
function resetForm(sample) {
  $('#riderList').innerHTML = ''; $('#orderList').innerHTML = '';
  $('#formError').hidden = true;
  document.querySelectorAll('.invalid').forEach(i => i.classList.remove('invalid'));
  if (sample) {
    $('#city').value = 'Chennai, India';
    $('#restName').value = 'Tummy Express Kitchen';
    $('#restPlace').value = 'T Nagar';
    [['Ravi', 'Chennai Central'], ['Suresh', 'Egmore'], ['Meena', 'Guindy'], ['Imran', 'Adyar']].forEach(r => addRider(...r));
    [['Arun', 'Marina Beach', 'Chicken Biryani', '220'], ['Bhavya', 'Phoenix Marketcity', 'Masala Dosa', '90'],
     ['Karthik', 'Besant Nagar', 'Veg Meals', '150'], ['Divya', 'Mylapore', 'Paneer Wrap', '130']].forEach(o => addOrder(...o));
  } else {
    ['city', 'restName', 'restPlace'].forEach(id => ($('#' + id).value = ''));
    for (let i = 0; i < 2; i++) { addRider(); addOrder(); }
  }
}

/* ---------- validation ---------- */
const COORD_RE = /^\s*(-?\d{1,2}(?:\.\d+)?)\s*,\s*(-?\d{1,3}(?:\.\d+)?)\s*$/;
function looksLikeCoords(s) { return /^[\s\d.,+-]+$/.test(s) && /\d/.test(s) && s.includes(','); }
function readForm() {
  const city = $('#city').value.trim();
  const rest = { name: $('#restName').value.trim(), place: $('#restPlace').value.trim(), els: [$('#restName'), $('#restPlace')] };
  const riders = [...document.querySelectorAll('.rider-row')].map(r => ({ name: r.querySelector('.r-name').value.trim(), place: r.querySelector('.r-place').value.trim(), els: [r.querySelector('.r-name'), r.querySelector('.r-place')] }));
  const orders = [...document.querySelectorAll('.order-row')].map(r => ({
    customer: r.querySelector('.o-cust').value.trim(), place: r.querySelector('.o-place').value.trim(),
    food: r.querySelector('.o-food').value.trim(), priceRaw: r.querySelector('.o-price').value.trim().replace(/^₹\s*/, ''),
    els: [...r.querySelectorAll('input')]
  }));
  return { city, rest, riders, orders };
}
function validate(f) {
  const bad = (msg, ...els) => ({ error: msg, els });
  if (!f.city) return bad('Please enter a city.', $('#city'));
  if (!f.rest.name) return bad('Please enter the restaurant name.', $('#restName'));
  if (!f.rest.place) return bad('Please enter the restaurant location.', $('#restPlace'));
  if (looksLikeCoords(f.rest.place) && !validCoord(f.rest.place)) return bad('Restaurant coordinates look wrong. Use “latitude, longitude”, e.g. 13.0827, 80.2707.', $('#restPlace'));
  if (f.riders.length < LIMITS.riderMin || f.riders.length > LIMITS.riderMax) return bad(`Use between ${LIMITS.riderMin} and ${LIMITS.riderMax} riders.`);
  if (f.orders.length < LIMITS.orderMin || f.orders.length > LIMITS.orderMax) return bad(`Use between ${LIMITS.orderMin} and ${LIMITS.orderMax} orders.`);
  if (f.riders.length < f.orders.length) return bad(`You have ${f.orders.length} orders but only ${f.riders.length} riders. Each order needs its own rider, so add riders or remove orders.`);
  const seenR = new Set();
  for (let i = 0; i < f.riders.length; i++) {
    const r = f.riders[i];
    if (!r.name) return bad(`Rider ${i + 1}: enter a name.`, r.els[0]);
    if (!r.place) return bad(`Rider ${i + 1}: enter a location.`, r.els[1]);
    if (looksLikeCoords(r.place) && !validCoord(r.place)) return bad(`Rider ${i + 1}: coordinates look wrong.`, r.els[1]);
    const k = r.name.toLowerCase();
    if (seenR.has(k)) return bad(`Duplicate rider name “${r.name}”. Names must be unique.`, r.els[0]);
    seenR.add(k);
  }
  const seenC = new Set();
  for (let i = 0; i < f.orders.length; i++) {
    const o = f.orders[i], n = i + 1;
    if (!o.customer) return bad(`Order ${n}: enter the customer name.`, o.els[0]);
    if (!o.place) return bad(`Order ${n}: enter the delivery place.`, o.els[1]);
    if (looksLikeCoords(o.place) && !validCoord(o.place)) return bad(`Order ${n}: coordinates look wrong.`, o.els[1]);
    if (!o.food) return bad(`Order ${n}: enter the food item.`, o.els[2]);
    if (!/^\d+(\.\d+)?$/.test(o.priceRaw)) return bad(`Order ${n}: price must be a number like 120 or 99.5.`, o.els[3]);
    if (Number(o.priceRaw) <= 0) return bad(`Order ${n}: price must be greater than 0.`, o.els[3]);
    const k = o.customer.toLowerCase();
    if (seenC.has(k)) return bad(`Duplicate customer name “${o.customer}”. Names must be unique.`, o.els[0]);
    seenC.add(k);
  }
  return null;
}
function validCoord(s) {
  const m = COORD_RE.exec(s); if (!m) return false;
  return Math.abs(+m[1]) <= 90 && Math.abs(+m[2]) <= 180;
}
function showError(v) {
  document.querySelectorAll('.invalid').forEach(i => i.classList.remove('invalid'));
  const box = $('#formError'); box.hidden = false; box.textContent = '⚠️ ' + v.error;
  box.style.animation = 'none'; void box.offsetWidth; box.style.animation = '';
  (v.els || []).forEach(e => e && e.classList.add('invalid'));
  if (v.els && v.els[0]) v.els[0].focus();
  box.scrollIntoView({ behavior: 'smooth', block: 'center' });
}

/* ---------- loader ---------- */
function loader(show, title, msg, pct) {
  $('#loader').hidden = !show;
  if (title) $('#loaderTitle').textContent = title;
  if (msg) $('#loaderMsg').textContent = msg;
  if (pct != null) $('#loaderBar').style.width = pct + '%';
}

/* ---------- geocoding + routing (online services) ---------- */
let lastGeo = 0;
const geoCache = new Map();
async function fetchJSON(url, ms = 12000) {
  const ctl = new AbortController(), t = setTimeout(() => ctl.abort(), ms);
  try {
    const res = await fetch(url, { signal: ctl.signal, headers: { Accept: 'application/json' } });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    return await res.json();
  } finally { clearTimeout(t); }
}
async function geocode(place, city) {
  if (validCoord(place)) { const m = COORD_RE.exec(place); return { lat: +m[1], lng: +m[2], label: place }; }
  const q = place.toLowerCase().includes(city.split(',')[0].trim().toLowerCase()) ? place : `${place}, ${city}`;
  if (geoCache.has(q)) return geoCache.get(q);
  const wait = 1100 - (Date.now() - lastGeo);
  if (wait > 0) await sleep(wait);
  lastGeo = Date.now();
  let data;
  try { data = await fetchJSON('https://nominatim.openstreetmap.org/search?format=json&limit=1&q=' + encodeURIComponent(q)); }
  catch (e) { throw new Error(`Could not reach the place-search service while looking up “${place}”. Check your internet connection and try again.`); }
  if (!data || !data.length) throw new Error(`Couldn’t find “${place}” in ${city}. Try adding the area name, a fuller address, or type coordinates like 13.0827, 80.2707.`);
  const out = { lat: +data[0].lat, lng: +data[0].lon, label: data[0].display_name };
  geoCache.set(q, out);
  return out;
}
async function roadMatrix(pts) {
  const coords = pts.map(p => `${p[1]},${p[0]}`).join(';');
  const j = await fetchJSON(`https://router.project-osrm.org/table/v1/driving/${coords}?annotations=distance`, 15000);
  if (j.code !== 'Ok' || !j.distances) throw new Error('bad table');
  const fb = fallbackMatrix(pts);
  return j.distances.map((row, i) => row.map((v, k) => (v == null ? fb[i][k] : v)));
}
async function roadRoute(points) {
  const key = points.map(p => p.join(',')).join('|');
  if (S.routeCache.has(key)) return S.routeCache.get(key);
  let out = points;
  if (!S.fallback) {
    try {
      const coords = points.map(p => `${p[1]},${p[0]}`).join(';');
      const j = await fetchJSON(`https://router.project-osrm.org/route/v1/driving/${coords}?overview=full&geometries=geojson`, 15000);
      if (j.code === 'Ok' && j.routes && j.routes[0]) out = j.routes[0].geometry.coordinates.map(c => [c[1], c[0]]);
    } catch (e) { /* straight line fallback */ }
  }
  S.routeCache.set(key, out);
  return out;
}

/* ---------- main flow ---------- */
async function plan(e) {
  e.preventDefault();
  const f = readForm(), v = validate(f);
  if (v) { showError(v); return; }
  $('#formError').hidden = true;
  document.querySelectorAll('.invalid').forEach(i => i.classList.remove('invalid'));
  $('#planBtn').disabled = true;
  try {
    const targets = [
      { kind: 'rest', place: f.rest.place, name: f.rest.name },
      ...f.riders.map(r => ({ kind: 'rider', place: r.place, name: r.name })),
      ...f.orders.map(o => ({ kind: 'cust', place: o.place, name: o.customer }))
    ];
    loader(true, 'Finding your places…', 'Starting', 3);
    const pts = [];
    for (let i = 0; i < targets.length; i++) {
      const t = targets[i];
      loader(true, 'Finding your places…', `Locating ${t.name} (${i + 1}/${targets.length})`, 5 + (i / targets.length) * 70);
      const g = await geocode(t.place, f.city);
      pts.push([g.lat, g.lng]); t.label = g.label;
    }
    loader(true, 'Measuring real roads…', 'Asking OSRM for road distances', 82);
    S.fallback = false;
    let D;
    try { D = await roadMatrix(pts); }
    catch (err) { D = fallbackMatrix(pts); S.fallback = true; }

    loader(true, 'Running algorithms…', 'Brute force · D&C · DP · Greedy', 92);
    const R = f.riders.length, N = f.orders.length;
    S.rest = { name: f.rest.name, pos: pts[0] };
    S.riders = f.riders.map((r, i) => ({ name: r.name, pos: pts[1 + i] }));
    S.customers = f.orders.map((o, i) => ({ name: o.customer, food: o.food, price: Number(o.priceRaw), pos: pts[1 + R + i] }));
    S.D = D; S.startTime = Date.now(); S.routeCache.clear();

    const time = fn => { const t0 = performance.now(); const r = fn(); r.ms = performance.now() - t0; return r; };
    const items = S.customers.map((c, i) => ({ i, food: c.food, price: c.price, customer: c.name }));
    S.results = {
      brute: time(() => bruteForce(D, R, N)),
      dc: time(() => cheapestDC(items)),
      dp: time(() => heldKarp(D, R, N)),
      greedy: time(() => greedyAssign(D, R, N))
    };
    S.results.dp.rider = nearestRider(D, R);
    loader(true, 'Done!', 'Drawing your map', 100);
    await sleep(300);
    loader(false);
    showResults();
  } catch (err) {
    loader(false);
    showError({ error: err.message || 'Something went wrong. Please try again.' });
  } finally {
    $('#planBtn').disabled = false;
  }
}
function nearestRider(D, R) {
  let b = 0; for (let r = 1; r < R; r++) if (D[1 + r][0] < D[1 + b][0]) b = r;
  return b;
}

/* ---------- results ---------- */
function showResults() {
  ['#results', '#compare'].forEach(s => { $(s).hidden = false; revealNow($(s)); });
  $('#navResults').classList.remove('disabled'); $('#navCompare').classList.remove('disabled');
  const n = $('#notice');
  n.hidden = !S.fallback;
  if (S.fallback) n.textContent = '⚠️ The road-distance service is unavailable, so distances use straight-line × 1.3 as an estimate.';
  buildKPIs(); buildCompare();
  initMap();
  selectTab('brute');
  $('#results').scrollIntoView({ behavior: 'smooth' });
  confetti();
}
function buildKPIs() {
  const r = S.results, dpTotal = r.dp.total, pre = S.D[1 + r.dp.rider][0];
  const diff = r.greedy.total - r.brute.total;
  const cards = [
    ['Best assignment', km(r.brute.total) + ' km', `Brute force, ${r.brute.steps.toLocaleString('en-IN')} options checked`],
    ['Shortest drop route', km(dpTotal) + ' km', `All drops in ~${Math.round(minutesFor(dpTotal + pre))} min`],
    ['Greedy penalty', diff < 1 ? 'None 🎉' : '+' + km(diff) + ' km', diff < 1 ? 'Greedy matched the optimum' : `${((diff / r.brute.total) * 100).toFixed(1)}% longer than optimal`],
    ['Cheapest item', '₹' + r.dc.winner.price, `${r.dc.winner.food} (${r.dc.winner.customer})`]
  ];
  $('#kpis').innerHTML = cards.map((c, i) => `<div class="kpi" style="animation-delay:${i * 90}ms"><small>${c[0]}</small><strong>${esc(c[1])}</strong><span>${esc(c[2])}</span></div>`).join('');
}
function buildCompare() {
  const r = S.results, order = ['brute', 'dc', 'dp', 'greedy'];
  const solves = { brute: 'Rider ↔ order matching', dc: 'Cheapest food item', dp: 'Shortest delivery route', greedy: 'Nearest-rider matching' };
  const result = {
    brute: `Optimal total ${km(r.brute.total)} km`,
    dc: `₹${r.dc.winner.price} · ${r.dc.winner.food}`,
    dp: `${km(r.dp.total)} km route`,
    greedy: `${km(r.greedy.total)} km (${r.greedy.total - r.brute.total < 1 ? 'optimal' : '+' + km(r.greedy.total - r.brute.total) + ' km'})`
  };
  const colors = { brute: '#fb7185', dc: '#38bdf8', dp: '#a78bfa', greedy: '#4ade80' };
  const max = Math.log10(Math.max(...order.map(k => r[k].steps)) + 1) || 1;
  $('#bars').innerHTML = order.map(k => `<div class="barrow"><span>${INFO[k].title}</span><div class="track"><div class="fill" data-w="${Math.max(4, Math.log10(r[k].steps + 1) / max * 100)}" style="background:${colors[k]}"></div></div><em>${r[k].steps.toLocaleString('en-IN')} steps</em></div>`).join('');
  $('#cmpBody').innerHTML = order.map(k => `<tr><td><span class="chip ${INFO[k].cls}">${INFO[k].title}</span></td><td>${solves[k]}</td><td><code>${INFO[k].time}</code></td><td><code>${INFO[k].space}</code></td><td><b>${r[k].steps.toLocaleString('en-IN')}</b></td><td>${r[k].ms < 0.01 ? '<0.01' : r[k].ms.toFixed(2)} ms</td><td>${esc(result[k])}</td></tr>`).join('');
  setTimeout(() => document.querySelectorAll('#bars .fill').forEach(f => (f.style.width = f.dataset.w + '%')), 80);
}

function selectTab(key) {
  S.tab = key;
  document.querySelectorAll('.tab').forEach(t => t.classList.toggle('active', t.dataset.tab === key));
  $('#panel').innerHTML = panelHTML(key);
  $('#panel').style.animation = 'none'; void $('#panel').offsetWidth; $('#panel').style.animation = '';
  const c = $('#panel .count'); if (c) countUp(c, +c.dataset.to);
  setTimeout(() => document.querySelectorAll('.pbar .fill').forEach(f => (f.style.width = f.dataset.w + '%')), 60);
  if (key === 'dp') {
    $('#replayBtn').addEventListener('click', () => startRide());
  }
  drawMap(key);
}

function panelHTML(key) {
  const A = INFO[key], r = S.results[key];
  const logs = logHTML(key);
  return `
    <div class="algo-head"><span class="chip ${A.cls}">${A.paradigm}</span><h3>${A.title}</h3><p>${A.problem}</p></div>
    <div class="result-card">${resultHTML(key)}</div>
    <div class="metrics">
      <div class="metric hl"><b class="count" data-to="${r.steps}">0</b><small>${A.stepLabel}</small></div>
      <div class="metric"><b>${A.time}</b><small>Time</small></div>
      <div class="metric"><b>${A.space}</b><small>Space</small></div>
      <div class="metric"><b>${r.ms < 0.01 ? '<0.01' : r.ms.toFixed(2)}ms</b><small>Runtime</small></div>
    </div>
    <details class="how" open><summary>How it works</summary><ol>${A.how.map(h => `<li>${h}</li>`).join('')}</ol></details>
    <details class="how"><summary>Step log</summary><ul>${logs}</ul></details>`;
}

function resultHTML(key) {
  const r = S.results[key], C = S.customers, Rd = S.riders, D = S.D, R = Rd.length;
  if (key === 'brute' || key === 'greedy') {
    const lines = r.assign.map((ri, o) => {
      const d = legCost(D, R, ri, o);
      return `<div class="res-line" style="--c:${PALETTE[o % 6]};animation-delay:${o * 80}ms"><span class="dot"></span><span>Order of <b>${esc(C[o].customer || C[o].name)}</b> received by <b>Rider ${ri + 1} · ${esc(Rd[ri].name)}</b></span><em>${km(d)} km</em></div>`;
    }).join('');
    let verdict = '';
    if (key === 'brute') verdict = '<div class="verdict good">✅ Guaranteed optimal: no other assignment is shorter.</div>';
    else {
      const best = S.results.brute.total, diff = r.total - best;
      verdict = diff < 1
        ? '<div class="verdict good">🎉 Greedy matched the brute-force optimum on this input.</div>'
        : `<div class="verdict warn">⚠️ Greedy is <b>${km(diff)} km longer</b> (${((diff / best) * 100).toFixed(1)}%) than the brute-force best of ${km(best)} km.</div>`;
    }
    return `<h4>${key === 'brute' ? 'Best assignment' : 'Greedy assignment'}</h4>${lines}<div class="total-line"><span>Total distance: ${km(r.total)} km</span><span>⏱ ~${Math.round(minutesFor(r.total))} min riding</span></div>${verdict}`;
  }
  if (key === 'dc') {
    const max = Math.max(...C.map(c => c.price));
    const bars = C.map(c => `<div class="pbar ${c.price === r.winner.price && c.food === r.winner.food ? 'win' : ''}"><span>${esc(c.food)}</span><div class="track"><div class="fill" data-w="${(c.price / max) * 100}"></div></div><span>₹${c.price}</span></div>`).join('');
    return `<h4>Cheapest item</h4><div class="big-answer">${esc(r.winner.food)} · ₹${r.winner.price}<small>Ordered by ${esc(r.winner.customer)}</small></div><div class="price-bars">${bars}</div>`;
  }
  // dp timeline
  const rider = Rd[r.rider], pre = D[1 + r.rider][0];
  const fmt = m => new Date(S.startTime + m * 60000).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
  let cum = pre;
  let li = `<li data-n="1"><span class="eta">${fmt(minutesFor(cum))}</span><b>Pickup at ${esc(S.rest.name)}</b><span>${esc(rider.name)} rides ${km(pre)} km to the kitchen</span></li>`;
  r.order.forEach((c, i) => {
    cum += r.legs[i];
    li += `<li data-n="${i + 2}"><span class="eta">${fmt(minutesFor(cum))}</span><b>Deliver to ${esc(C[c].name)}</b><span>${esc(C[c].food)} · +${km(r.legs[i])} km · ${km(cum)} km total · ~${Math.round(minutesFor(cum))} min</span></li>`;
  });
  return `<h4>Delivery timeline · rider ${esc(rider.name)}</h4><ul class="timeline" id="timeline">${li}</ul>
    <div class="total-line"><span>Route: ${km(r.total)} km</span><span>All delivered by ${fmt(minutesFor(cum))}</span></div>
    <div class="ride-ctrl"><button type="button" class="btn small primary" id="replayBtn">▶ Replay ride</button>
    <label>Speed <select id="speedSel"><option value="1">1×</option><option value="2">2×</option><option value="4">4×</option></select></label></div>
    <div class="ride-status" id="rideStatus"></div>`;
}

function logHTML(key) {
  const r = S.results[key], C = S.customers, Rd = S.riders;
  const nm = a => a.map((ri, o) => `${esc(Rd[ri].name)}→${esc(C[o].name)}`).join(', ');
  if (key === 'brute') {
    return r.improvements.slice(-8).map(x => `<li>Step ${x.step}: new best <b>${km(x.total)} km</b> (${nm(x.assign)})</li>`).join('') +
      `<li>…checked all <b>${r.steps.toLocaleString('en-IN')}</b> assignments.</li>`;
  }
  if (key === 'dc') return r.trace.map(t => `<li>${'&nbsp;&nbsp;'.repeat(t.depth)}Compare <b>${esc(t.left.food)} ₹${t.left.price}</b> vs <b>${esc(t.right.food)} ₹${t.right.price}</b> → ${esc(t.winner.food)}</li>`).join('');
  if (key === 'dp') return `<li>${r.states.toLocaleString('en-IN')} states (2<sup>${S.customers.length}</sup> subsets × ${S.customers.length} end points).</li><li>Best order: <b>${r.order.map(c => esc(S.customers[c].name)).join(' → ')}</b></li><li>Each leg: ${r.legs.map(l => km(l) + ' km').join(', ')}</li>`;
  return r.trace.map(t => `<li>${esc(C[t.order].name)}'s order → nearest free rider <b>${esc(Rd[t.rider].name)}</b> (${km(t.pickup)} km from kitchen)</li>`).join('');
}

/* ---------- map ---------- */
function initMap() {
  if (!S.map) {
    S.map = L.map('map', { zoomControl: true }).setView(S.rest.pos, 12);
    S.layer = L.layerGroup().addTo(S.map);
    applyTiles();
  }
  setTimeout(() => S.map.invalidateSize(), 150);
}
function applyTiles() {
  if (S.tiles) S.map.removeLayer(S.tiles);
  const dark = document.documentElement.getAttribute('data-theme') === 'dark';
  S.tiles = L.tileLayer(dark ? 'https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png' : 'https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',
    { maxZoom: 19, attribution: '© OpenStreetMap contributors' + (dark ? ' © CARTO' : '') }).addTo(S.map);
}
function icon(html, w = 40) { return L.divIcon({ className: '', html, iconSize: [w, 40], iconAnchor: [w / 2, 20] }); }
function addPins(opts) {
  const group = [];
  L.marker(S.rest.pos, { icon: icon('<div class="pin rest">🍔</div>', 46) }).bindTooltip(`🍔 ${esc(S.rest.name)}`).addTo(S.layer);
  group.push(S.rest.pos);
  if (opts.riders) opts.riders.forEach(i => {
    L.marker(S.riders[i].pos, { icon: icon(`<div class="pin" style="--c:#8b5cf6">🛵<b>${i + 1}</b></div>`) }).bindTooltip(`🛵 Rider ${i + 1} · ${esc(S.riders[i].name)}`).addTo(S.layer);
    group.push(S.riders[i].pos);
  });
  S.customers.forEach((c, i) => {
    const cls = opts.winner != null ? (opts.winner === i ? 'win' : 'dim') : '';
    const html = opts.price
      ? `<div class="pin price ${cls}" style="--c:${PALETTE[i % 6]}">₹${c.price}</div>`
      : `<div class="pin ${cls}" style="--c:${PALETTE[i % 6]}">🏠<b>${i + 1}</b></div>`;
    L.marker(c.pos, { icon: icon(html, opts.price ? 64 : 40) }).bindTooltip(`🏠 ${esc(c.name)} · ${esc(c.food)} ₹${c.price}`).addTo(S.layer);
    group.push(c.pos);
  });
  return group;
}
function stopRide() { if (S.ride) { cancelAnimationFrame(S.ride.raf); S.ride = null; } }

async function drawMap(key) {
  const tok = ++S.drawTok;
  stopRide(); S.layer.clearLayers();
  const R = S.riders.length;
  if (key === 'dc') {
    const w = S.results.dc.winner.i;
    const g = addPins({ price: true, winner: w });
    S.map.fitBounds(L.latLngBounds(g).pad(.25));
    return;
  }
  if (key === 'dp') return drawDP(tok);
  const g = addPins({ riders: [...Array(R).keys()] });
  S.map.fitBounds(L.latLngBounds(g).pad(.2));
  const assign = S.results[key].assign;
  const jobs = assign.map((ri, o) => Promise.all([
    roadRoute([S.riders[ri].pos, S.rest.pos]),
    roadRoute([S.rest.pos, S.customers[o].pos])
  ]));
  const routes = await Promise.all(jobs);
  if (tok !== S.drawTok) return;
  routes.forEach(([a, b], o) => {
    const col = PALETTE[o % 6];
    L.polyline(a, { color: col, weight: 4, opacity: .7, dashArray: '8 10' }).addTo(S.layer);
    L.polyline(b, { color: col, weight: 6, opacity: .95 }).bindTooltip(`${esc(S.riders[assign[o]].name)} → ${esc(S.customers[o].name)} · ${km(legCost(S.D, R, assign[o], o))} km`).addTo(S.layer);
  });
}

async function drawDP(tok) {
  const r = S.results.dp, rider = S.riders[r.rider];
  const way = [rider.pos, S.rest.pos, ...r.order.map(c => S.customers[c].pos)];
  const g = addPins({ riders: [r.rider] });
  S.map.fitBounds(L.latLngBounds(g).pad(.2));
  const pts = await roadRoute(way);
  if (tok !== S.drawTok) return;
  // snap waypoints onto the polyline (monotonic)
  const wp = []; let from = 0;
  way.forEach((p, i) => {
    if (i === 0) { wp.push(0); return; }
    let bi = from, bd = Infinity;
    for (let k = from; k < pts.length; k++) {
      const d = (pts[k][0] - p[0]) ** 2 + (pts[k][1] - p[1]) ** 2;
      if (d < bd) { bd = d; bi = k; }
    }
    wp.push(bi); from = bi;
  });
  wp[wp.length - 1] = pts.length - 1;
  L.polyline(pts, { color: '#a78bfa', weight: 6, opacity: .35 }).addTo(S.layer);
  const trail = L.polyline([], { color: '#fc8019', weight: 6, opacity: .95 }).addTo(S.layer);
  const cum = [0];
  for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + S.map.distance(pts[i - 1], pts[i]));
  const marker = L.marker(pts[0], { icon: icon('<div class="pin mover"><span>🛵</span></div>'), zIndexOffset: 1000 }).addTo(S.layer);
  S.ride = { pts, wp, cum, trail, marker, raf: 0, tok };
  startRide();
}

function startRide() {
  const R = S.ride; if (!R) return;
  cancelAnimationFrame(R.raf);
  document.querySelectorAll('#timeline li').forEach(li => li.classList.remove('done'));
  const st = $('#rideStatus'); if (st) st.textContent = '';
  const speed = +($('#speedSel') ? $('#speedSel').value : 1) || 1;
  const total = R.cum[R.cum.length - 1] || 1;
  const dur = Math.max(7000, Math.min(22000, total * 1.1)) / speed;
  const t0 = performance.now();
  let seg = 0, k = 1, lastLng = R.pts[0][1];
  const lis = [...document.querySelectorAll('#timeline li')];
  const tick = now => {
    if (S.ride !== R) return;
    const p = Math.min(1, (now - t0) / dur), d = p * total;
    while (seg < R.cum.length - 2 && R.cum[seg + 1] < d) seg++;
    const a = R.pts[seg], b = R.pts[Math.min(seg + 1, R.pts.length - 1)];
    const span = (R.cum[Math.min(seg + 1, R.cum.length - 1)] - R.cum[seg]) || 1;
    const f = Math.min(1, Math.max(0, (d - R.cum[seg]) / span));
    const pos = [a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f];
    R.marker.setLatLng(pos);
    R.trail.setLatLngs([...R.pts.slice(0, seg + 1), pos]);
    const el = R.marker.getElement();
    if (el && Math.abs(pos[1] - lastLng) > 1e-7) { const m = el.querySelector('.mover'); if (m) m.classList.toggle('flip', pos[1] > lastLng); lastLng = pos[1]; }
    while (k < R.wp.length && d >= R.cum[R.wp[k]] - 0.5) { if (lis[k - 1]) lis[k - 1].classList.add('done'); k++; }
    if (p < 1) R.raf = requestAnimationFrame(tick);
    else { const s = $('#rideStatus'); if (s) s.textContent = '🎉 All orders delivered!'; }
  };
  R.raf = requestAnimationFrame(tick);
}

/* ---------- boot ---------- */
document.addEventListener('DOMContentLoaded', () => {
  initTheme(); initReveal(); resetForm(false);
  $('#addRider').addEventListener('click', () => addRider());
  $('#addOrder').addEventListener('click', () => addOrder());
  $('#sampleBtn').addEventListener('click', () => { resetForm(true); toast('Sample loaded. Press “Plan my delivery”.'); });
  $('#clearBtn').addEventListener('click', () => resetForm(false));
  $('#plannerForm').addEventListener('submit', plan);
  $('#tabs').addEventListener('click', e => { const b = e.target.closest('.tab'); if (b) selectTab(b.dataset.tab); });
  document.querySelectorAll('#plannerForm input').forEach(i => i.addEventListener('input', () => i.classList.remove('invalid')));
});
