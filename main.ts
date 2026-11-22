// Push-optimal Sokoban solver (slim). Generator levels: a one-wide hallway, up to four
// rooms off it (one door each, 3-4 boxes a room); a box pushed into the hallway never
// returns, so the level optimum is the sum of its rooms' optima. Cut the hallway, solve
// each room from its door with push-level A* over an admissible assignment heuristic
// (min-cost matching of boxes to goals over true single-box push distances), stitch
// with shortest hallway walks.
// Node-count budgets, fixed tie order: deterministic.
import {mkdirSync, readdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output', LU = 'udlr', UU = 'UDLR', INF = 1 << 28;
const PS = (t) => { const rows = t.split('\n').filter((r) => r.length), h = rows.length, w = Math.max(...rows.map((r) => r.length)), z = w * h, wall = new Uint8Array(z).fill(1), gl = [], bx = []; let pl = -1;
  rows.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = row[x], i = y * w + x; if (c === '#') continue; wall[i] = 0; if ('.*+'.includes(c)) gl.push(i); if ('$*'.includes(c)) bx.push(i); if ('@+'.includes(c)) pl = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (!x || !y || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return {w, z, wall, gl, bx, pl, D: [-w, w, -1, 1]}; };
// PD: dist[g*z+s] = fewest pushes moving one box from s onto goal g, other boxes ignored.
const PD = (L, open, goals) => { const {z, D} = L, dist = new Int32Array(z * goals.length).fill(INF), q = new Int32Array(z);
  goals.forEach((g, gi) => { const b0 = gi * z; let hd = 0, tl = 0; q[tl++] = g; dist[b0 + g] = 0;
    while (hd < tl) { const t = q[hd++], td = dist[b0 + t];
      for (let d = 0; d < 4; d++) { const dd = D[d], b = t - dd, s = t - 2 * dd; if (b < 0 || b >= z || s < 0 || s >= z || !open[b] || !open[s] || dist[b0 + b] !== INF) continue; dist[b0 + b] = td + 1; q[tl++] = b; } } });
  return dist; };
const LV = (L, dist, ng) => { const live = new Uint8Array(L.z); for (let s = 0; s < L.z; s++) for (let g = 0; g < ng; g++) if (dist[g * L.z + s] < INF) { live[s] = 1; break; } return live; };
const WK = (L, open, occ, from, to) => { if (from === to) return '';
  const {z, D} = L, prev = new Int32Array(z).fill(-1), q = new Int32Array(z); let hd = 0, tl = 0; q[tl++] = from; prev[from] = from * 4;
  while (hd < tl) { const p = q[hd++]; if (p === to) break; for (let d = 0; d < 4; d++) { const n = p + D[d]; if (n < 0 || n >= z || !open[n] || occ[n] || prev[n] !== -1) continue; prev[n] = p * 4 + d; q[tl++] = n; } }
  if (prev[to] === -1) return null; let s = ''; for (let p = to; p !== from; p = prev[p] >> 2) s = LU[prev[p] & 3] + s; return s; };
const PM = (n) => { const o = [], c = [], u = new Array(n).fill(false); const rec = () => { if (c.length === n) { o.push(c.slice()); return; } for (let i = 0; i < n; i++) if (!u[i]) { u[i] = true; c.push(i); rec(); c.pop(); u[i] = false; } }; rec(); return o; };
// SP: push-level A* on one room board; returns the push-optimal move string or null.
const SP = (L, open, bx0, goals, pl0) => { const {z, D} = L, k = bx0.length;
  const dist = PD(L, open, goals), pm = PM(k);
  const heur = (bx) => { let best = INF; for (const p of pm) { let s = 0; for (let i = 0; i < k; i++) { const d = dist[p[i] * z + bx[i]]; if (d >= INF) { s = INF; break; } s += d; } if (s < best) best = s; } return best; };
  const h0 = heur(bx0); if (h0 >= INF) return null;
  const sC = new Int32Array(z), sN = new Int32Array(z), st = new Int32Array(z), occ = new Uint8Array(z); let tC = 0, tN = 0;
  const flood = (seen, stamp, from) => { let n = 0, low = from; st[n++] = from; seen[from] = stamp;
    while (n) { const p = st[--n]; if (p < low) low = p; for (let d = 0; d < 4; d++) { const q = p + D[d]; if (q < 0 || q >= z || !open[q] || occ[q] || seen[q] === stamp) continue; seen[q] = stamp; st[n++] = q; } } return low; };
  const keyOf = (bx, low) => { let key = low; for (const b of bx) key = key * z + b; return key; };
  const NB = [bx0.slice()], NP = [pl0], NG = [0], PA = [-1], best = new Map();
  for (const b of bx0) occ[b] = 1; best.set(keyOf(bx0, flood(sN, ++tN, pl0)), 0); for (const b of bx0) occ[b] = 0;
  const BQ = []; let bf = h0; // bucket queue on f = g + h, which never decreases along a path
  const push = (f, n) => { (BQ[f] ??= []).push(n); if (f < bf) bf = f; };
  push(bf, 0);
  let found = -1;
  while (found < 0) { while (bf < BQ.length && (!BQ[bf] || !BQ[bf].length)) bf++; if (bf >= BQ.length) break;
    const s = BQ[bf].pop(), bx = NB[s], g = NG[s];
    if (bx.every((b) => goals.includes(b))) { found = s; break; }
    for (const b of bx) occ[b] = 1; flood(sC, ++tC, NP[s]); const here = tC;
    for (let bi = 0; bi < k; bi++) { const b = bx[bi];
      for (let d = 0; d < 4; d++) { const dd = D[d], stand = b - dd, t = b + dd;
        if (stand < 0 || stand >= z || t < 0 || t >= z || sC[stand] !== here || !open[t] || occ[t]) continue;
        occ[b] = 0; occ[t] = 1; const nx = bx.slice(); nx[bi] = t; nx.sort((a, c) => a - c); const key = keyOf(nx, flood(sN, ++tN, b)); occ[t] = 0; occ[b] = 1;
        const ng = g + 1, sg = best.get(key); if (sg !== undefined && sg <= ng) continue;
        if (NB.length >= 1e6) { for (const x of bx) occ[x] = 0; return null; }
        best.set(key, ng); const id = NB.length; NB.push(nx); NP.push(b); NG.push(ng); PA.push(s);
        const hh = heur(nx); if (hh < INF) push(ng + hh, id); } }
    for (const x of bx) occ[x] = 0; }
  if (found < 0) return null;
  const path = []; for (let s = found; s > 0; s = PA[s]) path.push(s); path.reverse();
  let moves = '', pl = pl0, bx = bx0;
  for (const s of path) { const nx = NB[s], from = bx.find((b) => !nx.includes(b)), to = nx.find((b) => !bx.includes(b)), dd = to - from;
    for (const b of bx) occ[b] = 1; const wk = WK(L, open, occ, pl, from - dd); for (const b of bx) occ[b] = 0;
    if (wk === null) return null; moves += wk + UU[D.indexOf(dd)]; pl = from; bx = nx; }
  return moves; };
// RM: cut the hallway row's dead squares; each part holding boxes is a room, entry = hallway square beyond its door.
const RM = (L) => { const {w, z, wall, gl, bx, pl, D} = L, open = new Uint8Array(z);
  for (let s = 0; s < z; s++) open[s] = wall[s] ? 0 : 1;
  L.ao = open;
  const live = LV(L, PD(L, open, gl), gl.length), row = Math.floor(pl / w), cut = new Uint8Array(z);
  for (let x = 0; x < w; x++) { const i = row * w + x; if (!wall[i] && !live[i]) cut[i] = 1; }
  if (bx.some((b) => cut[b] === 1)) return null;
  const part = new Int32Array(z).fill(-1), rooms = [], st = [];
  for (let s = 0; s < z; s++) { if (wall[s] || cut[s] || part[s] >= 0) continue;
    const id = rooms.length, sq = []; part[s] = id; st.push(s);
    while (st.length) { const p = st.pop(); sq.push(p); for (let d = 0; d < 4; d++) { const q = p + D[d]; if (q < 0 || q >= z || wall[q] || cut[q] || part[q] >= 0) continue; part[q] = id; st.push(q); } }
    rooms.push({sq, bx: [], gl: [], entry: -1}); }
  for (const b of bx) { if (part[b] < 0) return null; rooms[part[b]].bx.push(b); }
  for (const g of gl) { if (part[g] < 0) return null; rooms[part[g]].gl.push(g); }
  const kept = [];
  for (const r of rooms) { if (!r.bx.length) continue; if (r.bx.length !== r.gl.length) return null; r.sq.sort((a, b) => a - b);
    for (const s of r.sq) { for (let d = 0; d < 4; d++) { const q = s + D[d]; if (q >= 0 && q < z && Math.floor(q / w) === row && !wall[q]) { r.entry = q; break; } } if (r.entry >= 0) break; }
    if (r.entry < 0) return null; kept.push(r); }
  return kept; };
const BR = (L, rooms) => { const {z} = L;
  const set = new Set(L.bx), occ = new Uint8Array(z); let pl = L.pl, mv = '';
  for (const r of rooms) { for (const b of set) occ[b] = 1; const wk = WK(L, L.ao, occ, pl, r.entry); for (const b of set) occ[b] = 0;
    if (wk === null) return null; mv += wk; pl = r.entry;
    const open = new Uint8Array(z); for (const s of r.sq) open[s] = 1; open[r.entry] = 1;
    const sol = SP(L, open, r.bx, r.gl, r.entry);
    if (sol === null) return null; mv += sol;
    let p = pl; for (const ch of sol) { const d = LU.indexOf(ch.toLowerCase()); if (d < 0) continue; const q = p + L.D[d]; if (set.has(q)) { set.delete(q); set.add(q + L.D[d]); } p = q; } pl = p;
    if (!r.gl.every((g) => set.has(g))) return null; }
  return L.gl.every((g) => set.has(g)) ? mv : null; };
for (const id of readdirSync(I).sort()) { const L = PS(readFileSync(join(I, id, 'level.txt'), 'utf8')); let mv = '';
  if (L.bx.length && L.pl >= 0) { const rooms = RM(L); if (rooms && rooms.length) { const m = BR(L, rooms); if (m !== null) mv = m; } }
  mkdirSync(join(O, id), {recursive: true}); writeFileSync(join(O, id, 'solution.txt'), mv + '\n'); }
