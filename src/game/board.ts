// @ts-nocheck
// 盤面の幾何計算と生成
import { SQ3, HS, BCX, BCY } from "./constants";

export const shuf = (a) => {
  const b = [...a];
  for (let i = b.length - 1; i > 0; i--) {
    const j = (Math.random() * (i + 1)) | 0;
    [b[i], b[j]] = [b[j], b[i]];
  }
  return b;
};

export const h2xy = (q, r) => ({ x: BCX + HS * 1.5 * q, y: BCY + HS * SQ3 * (r + q * 0.5) });

export const hexCorners = (cx, cy) =>
  Array.from({ length: 6 }, (_, i) => ({ x: cx + HS * Math.cos(Math.PI / 3 * i), y: cy + HS * Math.sin(Math.PI / 3 * i) }));

const vKey = (x, y) => `${Math.round(x / 2) * 2}_${Math.round(y / 2) * 2}`;

export function createBoard() {
  const coords = [];
  for (let q = -2; q <= 2; q++) for (let r = Math.max(-2, -q - 2); r <= Math.min(2, -q + 2); r++) coords.push({ q, r });
  const terrains = shuf(["forest", "forest", "forest", "forest", "pasture", "pasture", "pasture", "pasture", "fields", "fields", "fields", "fields", "hills", "hills", "hills", "mountains", "mountains", "mountains", "desert"]);
  const nums = shuf([2, 3, 3, 4, 4, 5, 5, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12]);
  let ni = 0;
  const hexes = coords.map((c, i) => {
    const { x, y } = h2xy(c.q, c.r);
    const t = terrains[i];
    return { id: i, q: c.q, r: c.r, cx: x, cy: y, terrain: t, number: t === "desert" ? null : nums[ni++], hasRobber: t === "desert", vertexIds: [] };
  });
  const vMap = new Map();
  hexes.forEach(hex => {
    const cs = hexCorners(hex.cx, hex.cy);
    cs.forEach(c => {
      const k = vKey(c.x, c.y);
      if (!vMap.has(k)) vMap.set(k, { x: c.x, y: c.y, hexIds: [], adjKeys: new Set(), building: null, port: null });
      vMap.get(k).hexIds.push(hex.id);
    });
    for (let i = 0; i < 6; i++) {
      const k1 = vKey(cs[i].x, cs[i].y), k2 = vKey(cs[(i + 1) % 6].x, cs[(i + 1) % 6].y);
      vMap.get(k1).adjKeys.add(k2);
      vMap.get(k2).adjKeys.add(k1);
    }
  });
  const keyToId = {}, vertices = [];
  let vid = 0;
  vMap.forEach((v, k) => { v.id = vid; keyToId[k] = vid++; vertices.push(v); });
  vertices.forEach(v => { v.adjIds = [...v.adjKeys].map(k => keyToId[k]); delete v.adjKeys; });
  const eSet = new Set(), edges = [];
  vertices.forEach(v => {
    v.adjIds.forEach(aid => {
      const ek = [v.id, aid].sort((a, b) => a - b).join("-");
      if (!eSet.has(ek)) { eSet.add(ek); edges.push({ id: edges.length, v1: v.id, v2: aid, road: null }); }
    });
  });
  hexes.forEach(hex => {
    const cs = hexCorners(hex.cx, hex.cy);
    hex.vertexIds = cs.map(c => keyToId[vKey(c.x, c.y)]);
  });
  // 港：海沿いの隣接頂点ペアからランダムに9つ
  const coastal = vertices.filter(v => v.hexIds.length < 3);
  const pairs = []; const seen = new Set();
  for (const v of coastal) {
    for (const adjId of v.adjIds) {
      const adj = vertices.find(v2 => v2.id === adjId);
      if (adj && adj.hexIds.length < 3) {
        const key = [v.id, adjId].sort((a, b) => a - b).join('-');
        if (!seen.has(key)) { seen.add(key); pairs.push([v.id, adjId]); }
      }
    }
  }
  // "generic"を使う（nullはFirebase保存時にキーごと消えてしまうため使わない）
  const portTypes = shuf(["generic", "generic", "generic", "generic", "lumber", "brick", "wool", "grain", "ore"]);
  const ports = shuf(pairs).slice(0, 9).map((vids, i) => ({ v1: vids[0], v2: vids[1], resource: portTypes[i] }));
  ports.forEach(port => {
    const v1 = vertices.find(v => v.id === port.v1); if (v1) v1.port = port.resource;
    const v2 = vertices.find(v => v.id === port.v2); if (v2) v2.port = port.resource;
  });
  return { hexes, vertices, edges, ports };
}
