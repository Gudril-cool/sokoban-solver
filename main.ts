// Sokoban solver: room-decomposed push-optimal A* search.
//
// The generator's levels are a one-wide hallway with up to four rooms off
// it, each room holding 3 or 4 boxes and as many goals, opening onto the
// hallway through a single door. A box pushed through a door into the
// hallway can never come back, so every box stays in its room and a
// level's push optimum is the sum of its rooms' optima. This solver
// exploits exactly that: it cuts the hallway out of the board, solves
// each room on its own with a push-level A* search whose heuristic is a
// minimum-cost assignment of boxes to goals over true single-box push
// distances (admissible, so the first solution found is push-optimal),
// and stitches the rooms together with shortest player walks along the
// hallway. Dead squares (a box there can reach no goal) and frozen 2x2
// blocks prune the search. Everything is budgeted by node counts, never
// by the clock, and every tie is broken by a fixed order, so two runs
// produce byte-identical output.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Directions in a fixed order: up, down, left, right.
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const DL = ['u', 'd', 'l', 'r'];
const DU = ['U', 'D', 'L', 'R'];

interface Level {
  w: number;
  h: number;
  size: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const size = w * h;
  const wall = new Uint8Array(size).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x]!;
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, size, wall, goals, boxes, player };
}

// Per-goal push distances: dist[g][s] is the fewest pushes that move one
// box from square s onto goal g, ignoring the other boxes, over squares
// where `open` is 1. Infinity where impossible; those squares are dead.
function pushDistances(lv: Level, open: Uint8Array, goals: number[]): Int32Array {
  const { w, size } = lv;
  const INF = 1 << 28;
  const dist = new Int32Array(size * goals.length).fill(INF);
  const queue = new Int32Array(size);
  goals.forEach((g, gi) => {
    const base = gi * size;
    let head = 0;
    let tail = 0;
    queue[tail++] = g;
    dist[base + g] = 0;
    while (head < tail) {
      const t = queue[head++]!;
      const td = dist[base + t]!;
      for (let dir = 0; dir < 4; dir++) {
        const d = DY[dir]! * w + DX[dir]!;
        const b = t - d; // the box's square before the push that made t
        const stand = t - 2 * d; // where the player stood for that push
        if (b < 0 || b >= size || stand < 0 || stand >= size) continue;
        if (!open[b] || !open[stand]) continue;
        if (dist[base + b] !== INF) continue;
        dist[base + b] = td + 1;
        queue[tail++] = b;
      }
    }
  });
  return dist;
}

function permutations(n: number): number[][] {
  const out: number[][] = [];
  const cur: number[] = [];
  const used = new Array<boolean>(n).fill(false);
  const rec = (): void => {
    if (cur.length === n) {
      out.push(cur.slice());
      return;
    }
    for (let i = 0; i < n; i++) {
      if (used[i]) continue;
      used[i] = true;
      cur.push(i);
      rec();
      cur.pop();
      used[i] = false;
    }
  };
  rec();
  return out;
}

// Whether the box just pushed onto t completes a frozen 2x2 block of
// walls and boxes with some box off its goal: such a box can never move.
function frozenBlock(
  lv: Level,
  open: Uint8Array,
  occupied: Uint8Array,
  goal: Uint8Array,
  t: number,
): boolean {
  const { w } = lv;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (a < 0 || d >= lv.size) continue;
    const blocked = (s: number): boolean => !open[s] || occupied[s] === 1;
    if (!blocked(a) || !blocked(b) || !blocked(c) || !blocked(d)) continue;
    if (
      (occupied[a] && !goal[a]) ||
      (occupied[b] && !goal[b]) ||
      (occupied[c] && !goal[c]) ||
      (occupied[d] && !goal[d])
    ) {
      return true;
    }
  }
  return false;
}

// The shortest walk of the player from `from` to `to` avoiding walls and
// the squares in `occupied`, as lower-case LURD letters, or null.
function walkTo(
  lv: Level,
  open: Uint8Array,
  occupied: Uint8Array,
  from: number,
  to: number,
): string | null {
  if (from === to) return '';
  const { w, size } = lv;
  const prev = new Int32Array(size).fill(-1);
  const how = new Int32Array(size).fill(-1);
  const queue = new Int32Array(size);
  let head = 0;
  let tail = 0;
  queue[tail++] = from;
  prev[from] = from;
  while (head < tail) {
    const p = queue[head++]!;
    if (p === to) break;
    for (let dir = 0; dir < 4; dir++) {
      const q = p + DY[dir]! * w + DX[dir]!;
      if (q < 0 || q >= size || !open[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = dir;
      queue[tail++] = q;
    }
  }
  if (prev[to] === -1) return null;
  let s = '';
  for (let p = to; p !== from; p = prev[p]!) s = DL[how[p]!]! + s;
  return s;
}

interface PushSolution {
  pushes: number;
  moves: string;
}

// Push-level search over one sub-board: squares where `open` is 1, the
// given boxes and goals, the player starting at `playerStart`. With
// useAStar the search is A* over pushes with the assignment heuristic;
// without it, plain breadth-first over pushes. Either way the first
// solution returned is push-optimal. Null when the node budget runs out
// or the sub-board is unsolvable.
function solvePushes(
  lv: Level,
  open: Uint8Array,
  startBoxes: number[],
  goals: number[],
  playerStart: number,
  useAStar: boolean,
  maxNodes: number,
): PushSolution | null {
  const { w, size } = lv;
  const INF = 1 << 28;
  const k = startBoxes.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const dist = pushDistances(lv, open, goals);
  const live = new Uint8Array(size);
  for (let s = 0; s < size; s++) {
    if (!open[s]) continue;
    for (let gi = 0; gi < goals.length; gi++) {
      if (dist[gi * size + s]! < INF) {
        live[s] = 1;
        break;
      }
    }
  }
  if (startBoxes.some((b) => !live[b])) return null;
  const perms = k <= 5 ? permutations(k) : null;
  const heuristic = (boxes: number[]): number => {
    if (perms) {
      let best = INF;
      for (const perm of perms) {
        let sum = 0;
        for (let i = 0; i < k; i++) {
          const d = dist[perm[i]! * size + boxes[i]!]!;
          if (d >= INF) {
            sum = INF;
            break;
          }
          sum += d;
        }
        if (sum < best) best = sum;
      }
      return best;
    }
    let sum = 0;
    for (const b of boxes) {
      let m = INF;
      for (let gi = 0; gi < goals.length; gi++) m = Math.min(m, dist[gi * size + b]!);
      if (m >= INF) return INF;
      sum += m;
    }
    return sum;
  };
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b] === 1);

  // Flood-fill scratch: two mark arrays, one for the region of the state
  // being expanded and one for the region a candidate push leads to, so
  // computing a candidate's region never clobbers the current one's.
  const seenCur = new Int32Array(size);
  const seenNxt = new Int32Array(size);
  const stack = new Int32Array(size);
  let stampCur = 0;
  let stampNxt = 0;
  const occupied = new Uint8Array(size);
  const flood = (seen: Int32Array, stamp: number, from: number): number => {
    let n = 0;
    let low = from;
    stack[n++] = from;
    seen[from] = stamp;
    while (n > 0) {
      const p = stack[--n]!;
      if (p < low) low = p;
      for (let dir = 0; dir < 4; dir++) {
        const q = p + DY[dir]! * w + DX[dir]!;
        if (q < 0 || q >= size || !open[q] || occupied[q] || seen[q] === stamp) continue;
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
    return low;
  };
  const reachFrom = (from: number): number => flood(seenNxt, ++stampNxt, from);

  const numericKey = k <= 5;
  const keyOf = (boxes: number[], low: number): string | number => {
    if (numericKey) {
      let key = low;
      for (const b of boxes) key = key * size + b;
      return key;
    }
    return String.fromCharCode(low, ...boxes);
  };

  // Node store.
  const nodeBoxes: number[][] = [startBoxes.slice()];
  const nodePlayer: number[] = [playerStart];
  const nodeG: number[] = [0];
  const nodeParent: number[] = [-1];
  const bestG = new Map<string | number, number>();
  for (const b of startBoxes) occupied[b] = 1;
  const startLow = reachFrom(playerStart);
  for (const b of startBoxes) occupied[b] = 0;
  bestG.set(keyOf(startBoxes, startLow), 0);

  // Priority order: A* by f = g + h, ties to the deeper node, then to
  // the earlier node; breadth-first is plain FIFO order.
  const heapF: number[] = [];
  const heapNode: number[] = [];
  let seq = 0;
  const heapSeq: number[] = [];
  const before = (a: number, b: number): boolean => {
    if (!useAStar) return heapSeq[a]! < heapSeq[b]!;
    if (heapF[a] !== heapF[b]) return heapF[a]! < heapF[b]!;
    const ga = nodeG[heapNode[a]!]!;
    const gb = nodeG[heapNode[b]!]!;
    if (ga !== gb) return ga > gb;
    return heapSeq[a]! < heapSeq[b]!;
  };
  const heapPush = (f: number, node: number): void => {
    let i = heapF.length;
    heapF.push(f);
    heapNode.push(node);
    heapSeq.push(seq++);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!before(i, p)) break;
      [heapF[i], heapF[p]] = [heapF[p]!, heapF[i]!];
      [heapNode[i], heapNode[p]] = [heapNode[p]!, heapNode[i]!];
      [heapSeq[i], heapSeq[p]] = [heapSeq[p]!, heapSeq[i]!];
      i = p;
    }
  };
  const heapPop = (): number => {
    const top = heapNode[0]!;
    const lf = heapF.pop()!;
    const ln = heapNode.pop()!;
    const ls = heapSeq.pop()!;
    if (heapF.length > 0) {
      heapF[0] = lf;
      heapNode[0] = ln;
      heapSeq[0] = ls;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heapF.length) break;
        if (c + 1 < heapF.length && before(c + 1, c)) c++;
        if (!before(c, i)) break;
        [heapF[i], heapF[c]] = [heapF[c]!, heapF[i]!];
        [heapNode[i], heapNode[c]] = [heapNode[c]!, heapNode[i]!];
        [heapSeq[i], heapSeq[c]] = [heapSeq[c]!, heapSeq[i]!];
        i = c;
      }
    }
    return top;
  };

  heapPush(useAStar ? heuristic(startBoxes) : 0, 0);
  let found = solved(startBoxes) ? 0 : -1;
  while (heapF.length > 0 && found < 0) {
    const s = heapPop();
    const boxes = nodeBoxes[s]!;
    const g = nodeG[s]!;
    for (const b of boxes) occupied[b] = 1;
    flood(seenCur, ++stampCur, nodePlayer[s]!);
    const here = stampCur;
    for (let bi = 0; bi < k && found < 0; bi++) {
      const b = boxes[bi]!;
      for (let dir = 0; dir < 4; dir++) {
        const d = DY[dir]! * w + DX[dir]!;
        const stand = b - d;
        const t = b + d;
        if (stand < 0 || stand >= size || t < 0 || t >= size) continue;
        if (seenCur[stand] !== here || !open[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(lv, open, occupied, goal, t);
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen) continue;
        const next = boxes.slice();
        next[bi] = t;
        next.sort((a, c) => a - c);
        occupied[b] = 0;
        occupied[t] = 1;
        const low = reachFrom(b);
        occupied[t] = 0;
        occupied[b] = 1;
        const key = keyOf(next, low);
        const ng = g + 1;
        const seenG = bestG.get(key);
        if (seenG !== undefined && seenG <= ng) continue;
        if (nodeBoxes.length >= maxNodes) {
          for (const x of boxes) occupied[x] = 0;
          return null;
        }
        bestG.set(key, ng);
        const id = nodeBoxes.length;
        nodeBoxes.push(next);
        nodePlayer.push(b);
        nodeG.push(ng);
        nodeParent.push(s);
        if (solved(next)) {
          found = id;
          break;
        }
        const h = useAStar ? heuristic(next) : 0;
        if (h < INF) heapPush(ng + h, id);
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;

  // Rebuild the move string: walk to each push's stand square, then push.
  const path: number[] = [];
  for (let s = found; s > 0; s = nodeParent[s]!) path.push(s);
  path.reverse();
  let moves = '';
  let player = playerStart;
  let boxes = startBoxes;
  for (const s of path) {
    const nextBoxes = nodeBoxes[s]!;
    const from = boxes.find((b) => !nextBoxes.includes(b))!;
    const to = nextBoxes.find((b) => !boxes.includes(b))!;
    const d = to - from;
    const dir = DX.findIndex((_, i) => DY[i]! * w + DX[i]! === d);
    for (const b of boxes) occupied[b] = 1;
    const walk = walkTo(lv, open, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    if (walk === null) return null;
    moves += walk + DU[dir]!;
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

interface Room {
  squares: number[];
  boxes: number[];
  goals: number[];
  entry: number; // the hallway square outside this room's door
}

// Cut the dead squares of the player's hallway row out of the floor;
// each remaining component that holds boxes is a room. The room's door
// is its square beside the hallway row, and the hallway square beyond
// it is the room's entry. Null when the level is not such a set of rooms.
function roomsOf(lv: Level): Room[] | null {
  const { w, size, wall, goals, boxes, player } = lv;
  const open = new Uint8Array(size);
  for (let s = 0; s < size; s++) open[s] = wall[s] ? 0 : 1;
  const dist = pushDistances(lv, open, goals);
  const INF = 1 << 28;
  const live = new Uint8Array(size);
  for (let s = 0; s < size; s++) {
    for (let gi = 0; gi < goals.length; gi++) {
      if (dist[gi * size + s]! < INF) {
        live[s] = 1;
        break;
      }
    }
  }
  const row = Math.floor(player / w);
  const cut = new Uint8Array(size);
  for (let x = 0; x < w; x++) {
    const i = row * w + x;
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b] === 1)) return null;
  const part = new Int32Array(size).fill(-1);
  const rooms: Room[] = [];
  const stack: number[] = [];
  for (let s = 0; s < size; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const id = rooms.length;
    const squares: number[] = [];
    part[s] = id;
    stack.push(s);
    while (stack.length > 0) {
      const p = stack.pop()!;
      squares.push(p);
      for (let dir = 0; dir < 4; dir++) {
        const q = p + DY[dir]! * w + DX[dir]!;
        if (q < 0 || q >= size || wall[q] || cut[q] || part[q] >= 0) continue;
        part[q] = id;
        stack.push(q);
      }
    }
    rooms.push({ squares, boxes: [], goals: [], entry: -1 });
  }
  for (const b of boxes) {
    if (part[b]! < 0) return null;
    rooms[part[b]!]!.boxes.push(b);
  }
  for (const g of goals) {
    if (part[g]! < 0) return null;
    rooms[part[g]!]!.goals.push(g);
  }
  const kept: Room[] = [];
  for (const room of rooms) {
    if (room.boxes.length === 0) continue;
    if (room.boxes.length !== room.goals.length) return null;
    room.squares.sort((a, b) => a - b);
    // The door: a room square beside the hallway row; entry is beyond it.
    for (const s of room.squares) {
      for (let dir = 0; dir < 4; dir++) {
        const q = s + DY[dir]! * w + DX[dir]!;
        if (q >= 0 && q < size && Math.floor(q / w) === row && !wall[q]) {
          room.entry = q;
          break;
        }
      }
      if (room.entry >= 0) break;
    }
    if (room.entry < 0) return null;
    kept.push(room);
  }
  return kept;
}

// Apply a move string to a box set and player square; returns the new
// player square. Assumes every move is legal.
function applyMoves(lv: Level, boxes: Set<number>, player: number, moves: string): number {
  const { w } = lv;
  let p = player;
  for (const ch of moves) {
    const dir = DL.indexOf(ch.toLowerCase());
    if (dir < 0) continue;
    const d = DY[dir]! * w + DX[dir]!;
    const q = p + d;
    if (boxes.has(q)) {
      boxes.delete(q);
      boxes.add(q + d);
    }
    p = q;
  }
  return p;
}

function solveByRooms(lv: Level, rooms: Room[]): string | null {
  const { size, wall } = lv;
  const allOpen = new Uint8Array(size);
  for (let s = 0; s < size; s++) allOpen[s] = wall[s] ? 0 : 1;
  const boxes = new Set(lv.boxes);
  const occupied = new Uint8Array(size);
  let player = lv.player;
  let moves = '';
  for (const room of rooms) {
    for (const b of boxes) occupied[b] = 1;
    const walk = walkTo(lv, allOpen, occupied, player, room.entry);
    for (const b of boxes) occupied[b] = 0;
    if (walk === null) return null;
    moves += walk;
    player = room.entry;
    // The room's own board: its squares plus the entry square outside
    // its door, exactly the configuration the generator solved it from.
    const open = new Uint8Array(size);
    for (const s of room.squares) open[s] = 1;
    open[room.entry] = 1;
    const roomBoxes = room.boxes.slice().sort((a, b) => a - b);
    const roomGoals = room.goals.slice().sort((a, b) => a - b);
    let sol = solvePushes(lv, open, roomBoxes, roomGoals, room.entry, true, 1_000_000);
    if (sol === null) {
      sol = solvePushes(lv, open, roomBoxes, roomGoals, room.entry, false, 1_000_000);
    }
    if (sol === null) return null;
    moves += sol.moves;
    player = applyMoves(lv, boxes, player, sol.moves);
    if (!roomGoals.every((g) => boxes.has(g))) return null;
  }
  if (!lv.goals.every((g) => boxes.has(g))) return null;
  return moves;
}

function solve(text: string): string {
  const lv = parseLevel(text);
  if (lv.boxes.length === 0 || lv.player < 0) return '';
  const rooms = roomsOf(lv);
  if (rooms !== null && rooms.length > 0) {
    const byRooms = solveByRooms(lv, rooms);
    if (byRooms !== null) return byRooms;
  }
  // Fallback for a level that is not a set of rooms: one push search
  // over the whole board, A* first, then breadth-first.
  const open = new Uint8Array(lv.size);
  for (let s = 0; s < lv.size; s++) open[s] = lv.wall[s] ? 0 : 1;
  const astar = solvePushes(lv, open, lv.boxes, lv.goals, lv.player, true, 800_000);
  if (astar !== null) return astar.moves;
  const bfs = solvePushes(lv, open, lv.boxes, lv.goals, lv.player, false, 800_000);
  return bfs === null ? '' : bfs.moves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
