// @ts-nocheck
// ゲームルール・状態遷移のロジック
import { PC, TR } from "./constants";
import { createBoard, shuf } from "./board";

// ─── Firebase から読んだデータの正規化 ─────────────────────────────
export function normalizeGS(data) {
  if (!data) return null;
  const toA = (x) => {
    if (!x) return [];
    if (Array.isArray(x)) return x;
    return Object.entries(x).sort(([a], [b]) => Number(a) - Number(b)).map(([, v]) => v);
  };
  data.players = toA(data.players).map(p => ({
    ...p,
    res: p.res || { lumber: 0, brick: 0, wool: 0, grain: 0, ore: 0 },
    devCards: toA(p.devCards || []),
    newDevCards: toA(p.newDevCards || []),
    knightsPlayed: p.knightsPlayed || 0,
  }));
  data.hexes = toA(data.hexes).map(h => ({ ...h, vertexIds: toA(h.vertexIds) }));
  data.vertices = toA(data.vertices).map(v => ({ ...v, adjIds: toA(v.adjIds), hexIds: toA(v.hexIds) }));
  data.edges = toA(data.edges);
  data.log = toA(data.log);
  data.setupOrder = toA(data.setupOrder);
  data.dice = data.dice ? toA(data.dice) : null;
  data.ports = toA(data.ports || []);
  data.devDeck = toA(data.devDeck || []);
  data.discardQueue = toA(data.discardQueue || []).map(d => ({ idx: Number(d.idx), amount: Number(d.amount) }));
  data.pendingRobberSteal = data.pendingRobberSteal
    ? { ...data.pendingRobberSteal, eligible: toA(data.pendingRobberSteal.eligible || []) }
    : null;
  data.pendingTrade = data.pendingTrade
    ? {
        ...data.pendingTrade,
        from: Number(data.pendingTrade.from),
        to: (data.pendingTrade.to === undefined || data.pendingTrade.to === null) ? null : Number(data.pendingTrade.to),
        declined: toA(data.pendingTrade.declined || []).map(Number),
        give: data.pendingTrade.give || {},
        want: data.pendingTrade.want || {},
      }
    : null;
  data.pendingAction = data.pendingAction || null;
  data.largestArmy = (data.largestArmy !== undefined && data.largestArmy !== null) ? Number(data.largestArmy) : null;
  data.longestRoad = (data.longestRoad !== undefined && data.longestRoad !== null) ? Number(data.longestRoad) : null;
  data.playedDevCardThisTurn = data.playedDevCardThisTurn || false;
  data.quick = data.quick || false;
  if (data.players.length > 0 && (data.curPlayer === undefined || !data.players[data.curPlayer])) data.curPlayer = 0;
  return data;
}

// ─── 発展カード ─────────────────────────────────────────────
export const createDevDeck = () => shuf([
  ...Array(14).fill('knight'),
  ...Array(5).fill('vp'),
  ...Array(2).fill('roadBuilding'),
  ...Array(2).fill('yearOfPlenty'),
  ...Array(2).fill('monopoly'),
]);

// ─── 汎用ヘルパー ────────────────────────────────────────────
export const canAfford = (p, cost) => Object.entries(cost).every(([r, n]) => (p.res[r] || 0) >= n);
export const canPlaceSett = (vid, verts) => {
  const v = verts.find(v => v.id === vid);
  if (!v || v.building) return false;
  return v.adjIds.every(aid => !verts.find(a => a.id === aid)?.building);
};
export const isConnRoad = (vid, edges, pid) => edges.some(e => (Number(e.v1) === Number(vid) || Number(e.v2) === Number(vid)) && e.road === pid);
export const genCode = () => { const c = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; return Array.from({ length: 4 }, () => c[(Math.random() * c.length) | 0]).join(""); };
export const addLog = (s, msg) => ({ ...s, log: [msg, ...(s.log || []).slice(0, 29)] });
export const initPlayer = (id, name) => ({ id, name, color: PC[id], res: { lumber: 0, brick: 0, wool: 0, grain: 0, ore: 0 }, vp: 0, settlementsLeft: 5, citiesLeft: 4, roadsLeft: 15, devCards: [], newDevCards: [], knightsPlayed: 0 });
export const emptyRes = () => ({ lumber: 0, brick: 0, wool: 0, grain: 0, ore: 0 });
export const removeOne = (arr, val) => { const i = arr.indexOf(val); if (i === -1) return arr; return [...arr.slice(0, i), ...arr.slice(i + 1)]; };

export function getPortRates(playerIdx, vertices) {
  const rates = { lumber: 4, brick: 4, wool: 4, grain: 4, ore: 4 };
  vertices.forEach(v => {
    if (v.building?.player === playerIdx && v.port) {
      if (v.port === 'generic') { Object.keys(rates).forEach(r => { if (rates[r] > 3) rates[r] = 3; }); }
      else { if (rates[v.port] > 2) rates[v.port] = 2; }
    }
  });
  return rates;
}

// ─── 最長交易路 ──────────────────────────────────────────────
export function calcLongestRoad(playerIdx, edges, vertices) {
  const playerEdges = edges.filter(e => e.road === playerIdx);
  if (playerEdges.length === 0) return 0;
  const adj = new Map();
  playerEdges.forEach(e => {
    if (!adj.has(e.v1)) adj.set(e.v1, new Set());
    if (!adj.has(e.v2)) adj.set(e.v2, new Set());
    adj.get(e.v1).add(e.v2);
    adj.get(e.v2).add(e.v1);
  });
  const vertMap = new Map(vertices.map(v => [v.id, v]));
  let maxLen = 0;
  function dfs(cur, visited) {
    maxLen = Math.max(maxLen, visited.size);
    for (const next of (adj.get(cur) || new Set())) {
      const ek = cur < next ? `${cur}-${next}` : `${next}-${cur}`;
      if (!visited.has(ek)) {
        const nextV = vertMap.get(next);
        const blocked = nextV?.building && nextV.building.player !== playerIdx;
        visited.add(ek);
        if (!blocked) dfs(next, visited);
        else maxLen = Math.max(maxLen, visited.size);
        visited.delete(ek);
      }
    }
  }
  for (const v of adj.keys()) dfs(v, new Set());
  return maxLen;
}

// ─── 勝利点・特殊カード ───────────────────────────────────────
export function calcTotalVP(player, gs) {
  const vpCards = [...(player.devCards || []), ...(player.newDevCards || [])].filter(c => c === 'vp').length;
  const la = gs.largestArmy === player.id ? 2 : 0;
  const lr = gs.longestRoad === player.id ? 2 : 0;
  return player.vp + vpCards + la + lr;
}

export function updateLongestRoad(state) {
  const { players, edges, vertices } = state;
  const lengths = players.map((_, i) => calcLongestRoad(i, edges, vertices));
  const maxLen = Math.max(...lengths);
  if (maxLen < 5) {
    return state.longestRoad !== null ? { ...state, longestRoad: null } : state;
  }
  const cur = state.longestRoad;
  if (cur === null) {
    const first = lengths.findIndex(l => l >= 5);
    return first !== -1 ? { ...state, longestRoad: first } : state;
  }
  // 現保持者より厳密に長い場合のみ奪取
  if (lengths.some((l, i) => i !== cur && l > lengths[cur])) {
    const newHolder = lengths.indexOf(Math.max(...lengths));
    return { ...state, longestRoad: newHolder };
  }
  // 現保持者が5本未満に落ちた場合
  if (lengths[cur] < 5) {
    const next = lengths.findIndex((l, i) => i !== cur && l >= 5);
    return { ...state, longestRoad: next !== -1 ? next : null };
  }
  return state;
}

export function updateLargestArmy(state) {
  const { players } = state;
  const counts = players.map(p => p.knightsPlayed || 0);
  const maxK = Math.max(...counts);
  if (maxK < 3) return state;
  const cur = state.largestArmy;
  if (cur === null) {
    const first = counts.findIndex(k => k >= 3);
    return first !== -1 ? { ...state, largestArmy: first } : state;
  }
  if (counts.some((k, i) => i !== cur && k > counts[cur])) {
    const newHolder = counts.indexOf(Math.max(...counts));
    return { ...state, largestArmy: newHolder };
  }
  return state;
}

// ─── 初期状態・ゲーム開始 ──────────────────────────────────────
export function createInitialState(code, hostName) {
  const board = createBoard();
  return {
    code, phase: "lobby", numPlayersTarget: 3,
    players: [initPlayer(0, hostName)],
    hexes: board.hexes, vertices: board.vertices, edges: board.edges, ports: board.ports,
    curPlayer: 0, setupStep: 0, setupSub: "settlement", setupOrder: [],
    dice: null, diceRolled: false, robberMode: false, lastVid: null,
    log: [`${hostName}がゲームを作成しました`], winner: null, updatedAt: Date.now(),
    pendingTrade: null,
    devDeck: createDevDeck(),
    discardQueue: [],
    pendingRobberSteal: null,
    pendingAction: null,
    largestArmy: null,
    longestRoad: null,
    playedDevCardThisTurn: false,
    quick: false,
  };
}

// ロビー状態 → セットアップフェーズ開始
export function startGameState(s) {
  const n = s.players.length;
  const f = Array.from({ length: n }, (_, i) => i);
  const setupOrder = [...f, ...[...f].reverse()];
  return addLog(
    { ...s, phase: "setup", setupOrder, curPlayer: setupOrder[0], setupStep: 0, setupSub: "settlement", updatedAt: Date.now() },
    "ゲーム開始！セットアップフェーズ — " + s.players[setupOrder[0]].name + "が最初に定住地を置いてください"
  );
}

// 資源の内訳を「🪵×2 🌾×1」形式の文字列に
export function resItemsStr(res, RI) {
  return Object.entries(res).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" ");
}
