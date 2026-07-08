// @ts-nocheck
// 盤面SVG：航海図スタイル
// （波の海・羅針盤・テクスチャ付きタイル・手描き風アイコン・家/城の駒）
import { useState } from "react";
import { hexCorners } from "../game/board";
import { TERRAIN_GRAD, PC, PC_DARK, NUM_PIPS, COSTS } from "../game/constants";
import { canPlaceSett, isConnRoad, canAfford } from "../game/logic";

// 資源 → 地形アイコンの対応（港の表示に使う）
const RES_ICON = { lumber: "forest", brick: "hills", wool: "pasture", grain: "fields", ore: "mountains" };

// ─── 手描き風の地形アイコン（<symbol>定義）───────────────────
function IconDefs() {
  return (
    <>
      <symbol id="ic-forest" viewBox="0 0 24 24">
        <path d="M12 2.5 L17 10.5 H14.5 L19 18 H5 L9.5 10.5 H7 Z" fill="#14501f" stroke="#0a3012" strokeWidth="1" strokeLinejoin="round" />
        <rect x="10.7" y="18" width="2.6" height="3.5" fill="#5a3a1a" />
      </symbol>
      <symbol id="ic-hills" viewBox="0 0 24 24">
        <g stroke="#5f1d0c" strokeWidth="1">
          <rect x="2.5" y="13" width="8.5" height="5.5" rx="1" fill="#b34a22" />
          <rect x="13" y="13" width="8.5" height="5.5" rx="1" fill="#b34a22" />
          <rect x="7.5" y="7" width="8.5" height="5.5" rx="1" fill="#c25628" />
        </g>
      </symbol>
      <symbol id="ic-pasture" viewBox="0 0 24 24">
        <rect x="6.5" y="15" width="1.8" height="4.5" fill="#3a332c" />
        <rect x="13" y="15" width="1.8" height="4.5" fill="#3a332c" />
        <ellipse cx="11" cy="12" rx="7" ry="5" fill="#f5f2e6" stroke="#8a8570" strokeWidth="1" />
        <circle cx="17.8" cy="10" r="2.7" fill="#3a332c" />
        <circle cx="18.7" cy="9.3" r="0.6" fill="#f5f2e6" />
      </symbol>
      <symbol id="ic-fields" viewBox="0 0 24 24">
        <g stroke="#7a5a10" strokeWidth="1.4" fill="none">
          <path d="M12 21 V8" /><path d="M6.5 21 V11" /><path d="M17.5 21 V11" />
        </g>
        <g fill="#d9a92c" stroke="#8a6a12" strokeWidth="0.6">
          <ellipse cx="12" cy="5.6" rx="2" ry="3.4" />
          <ellipse cx="6.5" cy="8.6" rx="1.8" ry="3" />
          <ellipse cx="17.5" cy="8.6" rx="1.8" ry="3" />
        </g>
      </symbol>
      <symbol id="ic-mountains" viewBox="0 0 24 24">
        <path d="M2 20 L9 6.5 L13 13.5 L16.5 7.5 L22 20 Z" fill="#6b7284" stroke="#3f4454" strokeWidth="1" strokeLinejoin="round" />
        <path d="M7.4 9.6 L9 6.5 L10.6 9.6 L9.6 9 L9 10 L8.2 9 Z" fill="#e8ecf2" />
        <path d="M15.4 9.4 L16.5 7.5 L17.7 9.6 L16.8 9.1 L16.1 10 Z" fill="#e8ecf2" />
      </symbol>
      <symbol id="ic-desert" viewBox="0 0 24 24">
        <circle cx="16" cy="7.5" r="3" fill="#d9a92c" stroke="#8a6a12" strokeWidth="0.8" />
        <path d="M2 19 Q7 15 12 19 T22 19" fill="none" stroke="#9a7d46" strokeWidth="1.7" strokeLinecap="round" />
        <path d="M4 15.5 Q7 13.5 10 15.5" fill="none" stroke="#9a7d46" strokeWidth="1.2" strokeLinecap="round" />
      </symbol>
      <symbol id="ic-anchor" viewBox="0 0 24 24">
        <circle cx="12" cy="5" r="2.2" fill="none" stroke="#2c3e50" strokeWidth="1.7" />
        <path d="M12 7.2 V17.5 M6.5 11.5 H17.5 M12 17.5 C8.5 17.5 5.8 15 5.2 12.2 M12 17.5 C15.5 17.5 18.2 15 18.8 12.2"
          fill="none" stroke="#2c3e50" strokeWidth="1.7" strokeLinecap="round" />
      </symbol>
    </>
  );
}

// ─── 地形のテクスチャパターン ─────────────────────────────
function PatternDefs() {
  return (
    <>
      <pattern id="pt-forest" width="18" height="16" patternUnits="userSpaceOnUse">
        <path d="M4 12 L7 6 L10 12 Z" fill="#0d3a15" opacity="0.45" />
        <path d="M12 9 L14.5 4 L17 9 Z" fill="#0d3a15" opacity="0.35" />
      </pattern>
      <pattern id="pt-hills" width="20" height="12" patternUnits="userSpaceOnUse">
        <rect x="0.5" y="0.5" width="9" height="5" fill="none" stroke="#7a2a12" strokeWidth="1" opacity="0.5" />
        <rect x="10.5" y="6.5" width="9" height="5" fill="none" stroke="#7a2a12" strokeWidth="1" opacity="0.5" />
      </pattern>
      <pattern id="pt-pasture" width="16" height="12" patternUnits="userSpaceOnUse">
        <path d="M2 9 Q4 7 6 9 M9 4 Q11 2 13 4" fill="none" stroke="#2e6b1e" strokeWidth="1.2" opacity="0.45" />
      </pattern>
      <pattern id="pt-fields" width="14" height="9" patternUnits="userSpaceOnUse">
        <path d="M0 2 H14 M0 6.5 H14" stroke="#8a6a1a" strokeWidth="1.4" opacity="0.4" />
      </pattern>
      <pattern id="pt-mountains" width="16" height="14" patternUnits="userSpaceOnUse">
        <path d="M0 14 L8 3 L16 14" fill="none" stroke="#3f4454" strokeWidth="1.1" opacity="0.4" />
      </pattern>
      <pattern id="pt-desert" width="18" height="14" patternUnits="userSpaceOnUse">
        <circle cx="4" cy="4" r="0.9" fill="#9a7d46" opacity="0.55" />
        <circle cx="12" cy="10" r="0.9" fill="#9a7d46" opacity="0.45" />
      </pattern>
      <pattern id="pt-waves" width="46" height="24" patternUnits="userSpaceOnUse">
        <path d="M0 8 Q6 3.5 12 8 T24 8" fill="none" stroke="#cfe8ef" strokeWidth="1.1" opacity="0.12" strokeLinecap="round" />
        <path d="M22 19 Q28 14.5 34 19 T46 19" fill="none" stroke="#cfe8ef" strokeWidth="1.1" opacity="0.09" strokeLinecap="round" />
      </pattern>
    </>
  );
}

// ヘックスの縁を6つの台形に割って、光源(左上)に応じて明暗を付ける立体ベベル
function hexBevelFacets(hex) {
  const cs = hexCorners(hex.cx, hex.cy);
  const inset = cs.map(c => ({ x: hex.cx + (c.x - hex.cx) * 0.85, y: hex.cy + (c.y - hex.cy) * 0.85 }));
  const lx = -0.55, ly = -0.83; // 左上からの光
  return cs.map((c, i) => {
    const c2 = cs[(i + 1) % 6];
    const i1 = inset[i], i2 = inset[(i + 1) % 6];
    const mx = (c.x + c2.x) / 2 - hex.cx, my = (c.y + c2.y) / 2 - hex.cy;
    const len = Math.hypot(mx, my) || 1;
    const light = (mx / len) * lx + (my / len) * ly;
    const fill = light > 0.25 ? `rgba(255,255,255,${0.1 + light * 0.22})` : light < -0.25 ? `rgba(0,0,0,${0.08 + -light * 0.26})` : "rgba(0,0,0,0.03)";
    return { key: i, pts: `${c.x},${c.y} ${c2.x},${c2.y} ${i2.x},${i2.y} ${i1.x},${i1.y}`, fill };
  });
}

// 羅針盤（装飾）
function CompassRose({ x, y, size = 26 }) {
  const s = size, s2 = size * 0.6;
  return (
    <g transform={`translate(${x},${y})`} opacity="0.55" style={{ pointerEvents: "none" }}>
      <path d={`M0 ${-s2} L${s2 * 0.2} ${-s2 * 0.2} L${s2} 0 L${s2 * 0.2} ${s2 * 0.2} L0 ${s2} L${-s2 * 0.2} ${s2 * 0.2} L${-s2} 0 L${-s2 * 0.2} ${-s2 * 0.2} Z`}
        fill="#caa84f" transform="rotate(45)" opacity="0.7" />
      <path d={`M0 ${-s} L${s * 0.18} ${-s * 0.18} L${s} 0 L${s * 0.18} ${s * 0.18} L0 ${s} L${-s * 0.18} ${s * 0.18} L${-s} 0 L${-s * 0.18} ${-s * 0.18} Z`}
        fill="#e3c26a" stroke="#8a6a2a" strokeWidth="0.8" />
      <circle r="2.6" fill="#8a6a2a" />
      <text y={-s - 5} textAnchor="middle" fontSize="9" fill="#e3c26a" fontFamily='"Shippori Mincho B1",serif' fontWeight="700">N</text>
    </g>
  );
}

function Settlement({ x, y, color, dark, mine }) {
  return (
    <g style={{ filter: "drop-shadow(0 2px 2px #0009)" }}>
      <path d={`M ${x - 7} ${y + 6} L ${x - 7} ${y - 1.5} L ${x + 7} ${y - 1.5} L ${x + 7} ${y + 6} Z`}
        fill={color} stroke="#26170c" strokeWidth="1" />
      <path d={`M ${x - 8.2} ${y - 1} L ${x} ${y - 9} L ${x + 8.2} ${y - 1} Z`}
        fill={dark} stroke="#26170c" strokeWidth="1" strokeLinejoin="round" />
      {mine && <path d={`M ${x - 7} ${y + 6} L ${x - 7} ${y - 1.5} L ${x + 7} ${y - 1.5} L ${x + 7} ${y + 6} Z`} fill="none" stroke="#f7efd9" strokeWidth="1.2" />}
    </g>
  );
}

function City({ x, y, color, dark, mine }) {
  return (
    <g style={{ filter: "drop-shadow(0 2px 3px #000a)" }}>
      <path d={`M ${x - 10} ${y + 7} L ${x - 10} ${y - 2} L ${x + 10} ${y - 2} L ${x + 10} ${y + 7} Z`}
        fill={color} stroke="#26170c" strokeWidth="1" />
      <path d={`M ${x - 10} ${y - 2} L ${x - 10} ${y - 8} L ${x - 6.5} ${y - 11.5} L ${x - 3} ${y - 8} L ${x - 3} ${y - 2} Z`}
        fill={dark} stroke="#26170c" strokeWidth="1" strokeLinejoin="round" />
      <path d={`M ${x - 1} ${y - 2} L ${x + 10} ${y - 2} L ${x + 10} ${y - 6} L ${x - 1} ${y - 6} Z`}
        fill={dark} stroke="#26170c" strokeWidth="1" />
      {mine && <path d={`M ${x - 10} ${y + 7} L ${x - 10} ${y - 2} L ${x + 10} ${y - 2} L ${x + 10} ${y + 7} Z`} fill="none" stroke="#f7efd9" strokeWidth="1.2" />}
    </g>
  );
}

function Robber({ x, y }) {
  return (
    <path
      d={`M ${x - 7} ${y + 11} C ${x - 7} ${y + 3} ${x - 3.5} ${y + 1} ${x - 3.5} ${y - 2} A 4.6 4.6 0 1 1 ${x + 3.5} ${y - 2} C ${x + 3.5} ${y + 1} ${x + 7} ${y + 3} ${x + 7} ${y + 11} Z`}
      fill="#2a2422" stroke="#e8dfc8" strokeWidth="1.4"
      style={{ filter: "drop-shadow(0 2px 2px #000b)" }}
    />
  );
}

function NumberToken({ hex, dimmed }) {
  const n = hex.number;
  const hot = n === 6 || n === 8;
  const color = hot ? "#9e3323" : "#2f2618";
  const pips = NUM_PIPS[n] || 0;
  const cy = hex.cy + 10;
  return (
    <g opacity={dimmed ? 0.4 : 1} style={{ pointerEvents: "none", filter: "drop-shadow(0 2.5px 2px #00000070)" }}>
      <circle cx={hex.cx} cy={cy} r={15} fill="url(#tokenGrad)" stroke="#5c4319" strokeWidth="1.6" />
      <circle cx={hex.cx} cy={cy} r={12.3} fill="none" stroke={hot ? "#c76a52" : "#c9b280"} strokeWidth="0.9" opacity="0.8" />
      <path d={`M ${hex.cx - 10} ${cy - 8} A 12 12 0 0 1 ${hex.cx + 7} ${cy - 10.5}`} fill="none" stroke="#fffdf2" strokeWidth="1.6" opacity="0.55" strokeLinecap="round" />
      <text x={hex.cx} y={cy + 4.5} textAnchor="middle" fontSize={hot ? 15 : 13.5} fontWeight="800"
        fill={color} fontFamily='"Shippori Mincho B1",serif'>{n}</text>
      {Array.from({ length: pips }, (_, i) => (
        <circle key={i} cx={hex.cx - (pips - 1) * 2.4 + i * 4.8} cy={cy + 9.5} r={1.3} fill={color} />
      ))}
    </g>
  );
}

export default function BoardView({ gs, myIndex, onVertex, onEdge, onHex }) {
  const [hovV, setHovV] = useState(null);
  const [hovE, setHovE] = useState(null);
  const isMyTurn = gs.curPlayer === myIndex;
  const phase = gs.phase;
  const myP = gs.players?.[myIndex];
  const isSetupSett = phase === "setup" && gs.setupSub === "settlement";
  const isSetupRoad = phase === "setup" && gs.setupSub === "road";
  const isRB = gs.pendingAction?.type === 'roadBuilding';
  // ボタンでモードを選ばず、サイコロを振った後はいつでも置ける場所をダブルクリックで建設できる
  const blockedByOtherAction = !!gs.pendingAction || gs.robberMode || !!gs.pendingRobberSteal || (gs.discardQueue?.length || 0) > 0;
  const canActNow = isMyTurn && phase === "main" && gs.diceRolled && !blockedByOtherAction;
  const canBuildRoadNow = canActNow && canAfford(myP, COSTS.road);
  const canBuildSettNow = canActNow && canAfford(myP, COSTS.settlement);
  const canBuildCityNow = canActNow && canAfford(myP, COSTS.city);
  const canRoadPlace = isMyTurn && (isSetupRoad || isRB || canBuildRoadNow);

  return (
    <svg width={580} height={580} viewBox="0 0 580 580"
      style={{ maxWidth: "min(96vw, 580px)", height: "auto", display: "block", filter: "drop-shadow(0 12px 30px #000000aa)" }}>
      <defs>
        <radialGradient id="seaG" cx="42%" cy="35%">
          <stop offset="0%" stopColor="#2d7686" />
          <stop offset="45%" stopColor="#1c5568" />
          <stop offset="78%" stopColor="#123f50" />
          <stop offset="100%" stopColor="#081e2a" />
        </radialGradient>
        <radialGradient id="seaGlint" cx="50%" cy="50%" r="50%">
          <stop offset="0%" stopColor="#e8f8ff" stopOpacity="0.5" />
          <stop offset="100%" stopColor="#e8f8ff" stopOpacity="0" />
        </radialGradient>
        <radialGradient id="frameWood" cx="35%" cy="18%" r="95%">
          <stop offset="0%" stopColor="#9a7143" />
          <stop offset="45%" stopColor="#6b4726" />
          <stop offset="100%" stopColor="#2a1911" />
        </radialGradient>
        <pattern id="pt-woodgrain" width="14" height="290" patternUnits="userSpaceOnUse">
          <path d="M0 0 Q7 145 2 290 M8 0 Q13 145 10 290" stroke="#1c1008" strokeWidth="0.8" opacity="0.35" fill="none" />
        </pattern>
        <radialGradient id="tokenGrad" cx="35%" cy="25%" r="85%">
          <stop offset="0%" stopColor="#fffaee" />
          <stop offset="50%" stopColor="#f3e8cd" />
          <stop offset="100%" stopColor="#d6bf8c" />
        </radialGradient>
        {Object.entries(TERRAIN_GRAD).map(([t, [a, b]]) => (
          <linearGradient key={t} id={`tg-${t}`} x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor={a} />
            <stop offset="100%" stopColor={b} />
          </linearGradient>
        ))}
        <PatternDefs />
        <IconDefs />
      </defs>

      {/* 木製の外枠（艶出しリム + 木目 + 鋲） */}
      <circle cx={290} cy={290} r={289} fill="url(#frameWood)" stroke="#140b06" strokeWidth="1.5" />
      <circle cx={290} cy={290} r={289} fill="url(#pt-woodgrain)" opacity="0.6" />
      <circle cx={290} cy={290} r={289} fill="none" stroke="#ffdca0" strokeWidth="0.8" opacity="0.25" />
      {Array.from({ length: 16 }, (_, i) => {
        const a = (Math.PI * 2 * i) / 16;
        const rx = 290 + Math.cos(a) * 286.5, ry = 290 + Math.sin(a) * 286.5;
        return (
          <g key={i}>
            <circle cx={rx} cy={ry} r={2.1} fill="#3a2a16" opacity="0.9" />
            <circle cx={rx - 0.5} cy={ry - 0.5} r="0.9" fill="#d8b56c" opacity="0.7" />
          </g>
        );
      })}
      <circle cx={290} cy={290} r={283.5} fill="none" stroke="#000" strokeWidth="4" opacity="0.35" />

      {/* 海 */}
      <circle cx={290} cy={290} r={281} fill="url(#seaG)" stroke="#8a6a3a" strokeWidth="2" />
      <circle cx={290} cy={290} r={281} fill="url(#pt-waves)" />
      <ellipse cx={195} cy={165} rx={110} ry={70} fill="url(#seaGlint)" style={{ pointerEvents: "none" }} />
      <circle cx={290} cy={290} r={274} fill="none" stroke="#c9a84f" strokeWidth="1" strokeDasharray="1 6" opacity="0.5" strokeLinecap="round" />
      <CompassRose x={462} y={122} />

      {/* ヘックス */}
      {gs.hexes.map(hex => {
        const cs = hexCorners(hex.cx, hex.cy);
        const pts = cs.map(c => `${c.x},${c.y}`).join(" ");
        const inner = cs.map(c => `${hex.cx + (c.x - hex.cx) * 0.93},${hex.cy + (c.y - hex.cy) * 0.93}`).join(" ");
        const robTarget = gs.robberMode && isMyTurn && !hex.hasRobber;
        return (
          <g key={hex.id} onClick={() => onHex(hex.id)} style={{ cursor: robTarget ? "pointer" : "default" }}>
            <polygon points={pts} fill={`url(#tg-${hex.terrain})`} stroke="#132630" strokeWidth="2.5" strokeLinejoin="round" />
            <polygon points={pts} fill={`url(#pt-${hex.terrain})`} style={{ pointerEvents: "none" }} />
            {hexBevelFacets(hex).map(f => (
              <polygon key={f.key} points={f.pts} fill={f.fill} style={{ pointerEvents: "none" }} />
            ))}
            <polygon points={inner} fill="none" stroke="#ffffff2a" strokeWidth="1.2" style={{ pointerEvents: "none" }} />
            {gs.robberMode && !robTarget && !hex.hasRobber && <polygon points={pts} fill="#000" opacity="0.25" style={{ pointerEvents: "none" }} />}
            {robTarget && <polygon points={pts} fill="#fff" opacity="0.13" className="pulse-spot" style={{ pointerEvents: "none" }} />}
            <use href={`#ic-${hex.terrain}`} x={hex.cx - 11} y={hex.cy - 27} width="22" height="22" style={{ pointerEvents: "none" }} />
            {hex.number && <NumberToken hex={hex} dimmed={hex.hasRobber} />}
            {hex.hasRobber && <Robber x={hex.cx} y={hex.cy + 8} />}
          </g>
        );
      })}

      {/* 港（ロープ + 羊皮紙の札） */}
      {(gs.ports || []).map((port, i) => {
        const v1 = gs.vertices.find(v => v.id === port.v1), v2 = gs.vertices.find(v => v.id === port.v2);
        if (!v1 || !v2) return null;
        const mx = (v1.x + v2.x) / 2, my = (v1.y + v2.y) / 2;
        // 札を少し沖側にずらす
        const dx = mx - 290, dy = my - 290;
        const len = Math.sqrt(dx * dx + dy * dy) || 1;
        const ox = mx + (dx / len) * 14, oy = my + (dy / len) * 14;
        const icon = (!port.resource || port.resource === "generic") ? "anchor" : RES_ICON[port.resource];
        const rate = (!port.resource || port.resource === "generic") ? "3:1" : "2:1";
        return (
          <g key={i} style={{ pointerEvents: "none" }}>
            <line x1={v1.x} y1={v1.y} x2={ox} y2={oy} stroke="#8a6a3a" strokeWidth="2.5" strokeDasharray="3 3" />
            <line x1={v2.x} y1={v2.y} x2={ox} y2={oy} stroke="#8a6a3a" strokeWidth="2.5" strokeDasharray="3 3" />
            <circle cx={ox} cy={oy} r={12.5} fill="#f3e8cd" stroke="#7a5a2e" strokeWidth="1.8" />
            <use href={`#ic-${icon}`} x={ox - 7.5} y={oy - 9.5} width="15" height="15" />
            <text x={ox} y={oy + 9.5} textAnchor="middle" fontSize="6" fontWeight="700" fill="#5a4420">{rate}</text>
          </g>
        );
      })}

      {/* 道（置ける辺はダブルクリックで建設） */}
      {gs.edges.map(edge => {
        const v1 = gs.vertices.find(v => v.id === edge.v1), v2 = gs.vertices.find(v => v.id === edge.v2);
        if (!v1 || !v2) return null;
        const connected = isSetupRoad
          ? (Number(edge.v1) === Number(gs.lastVid) || Number(edge.v2) === Number(gs.lastVid))
          : (v1.building?.player === myIndex || v2.building?.player === myIndex || isConnRoad(edge.v1, gs.edges, myIndex) || isConnRoad(edge.v2, gs.edges, myIndex));
        const canPlaceHere = canRoadPlace && edge.road == null && connected;
        const isHov = hovE === edge.id && canPlaceHere;
        return (
          <g key={edge.id} onDoubleClick={() => onEdge(edge.id)}
            onMouseEnter={() => setHovE(edge.id)} onMouseLeave={() => setHovE(null)}
            style={{ cursor: canPlaceHere ? "pointer" : "default" }}>
            {edge.road != null && <line x1={v1.x} y1={v1.y} x2={v2.x} y2={v2.y} stroke="#1b0f08" strokeWidth="8" strokeLinecap="round" />}
            <line x1={v1.x} y1={v1.y} x2={v2.x} y2={v2.y}
              stroke={edge.road != null ? PC[edge.road] : isHov ? "#ffe9a8" : "transparent"}
              strokeWidth={edge.road != null ? 4.5 : 4} strokeLinecap="round"
              strokeDasharray={isHov ? "6 5" : undefined} opacity={isHov ? 0.9 : 1} />
            {canPlaceHere && !isHov && (
              <line x1={v1.x} y1={v1.y} x2={v2.x} y2={v2.y} stroke="#ffe9a8" strokeWidth="3" strokeLinecap="round"
                strokeDasharray="3 6" opacity="0.55" className="pulse-spot" style={{ pointerEvents: "none" }} />
            )}
            <line x1={v1.x} y1={v1.y} x2={v2.x} y2={v2.y} stroke="transparent" strokeWidth="14" />
          </g>
        );
      })}

      {/* 頂点（定住地・都市・建設可能スポットはダブルクリックで建設） */}
      {gs.vertices.map(v => {
        const b = v.building;
        const canSett = isMyTurn && (isSetupSett || canBuildSettNow)
          && canPlaceSett(v.id, gs.vertices) && (isSetupSett || isConnRoad(v.id, gs.edges, myIndex));
        const canCity = canBuildCityNow && b?.player === myIndex && b?.type === "settlement";
        return (
          <g key={v.id} onDoubleClick={() => onVertex(v.id)}
            onMouseEnter={() => setHovV(v.id)} onMouseLeave={() => setHovV(null)}
            style={{ cursor: (canSett || canCity) ? "pointer" : "default" }}>
            {(canSett || canCity) && hovV === v.id && <circle cx={v.x} cy={v.y} r={11} fill="#ffffff2a" />}
            {b ? (
              b.type === "city"
                ? <City x={v.x} y={v.y} color={PC[b.player]} dark={PC_DARK[b.player]} mine={b.player === myIndex} />
                : <Settlement x={v.x} y={v.y} color={PC[b.player]} dark={PC_DARK[b.player]} mine={b.player === myIndex} />
            ) : (
              canSett && <circle cx={v.x} cy={v.y} r={7} className="pulse-spot" fill="#ffe9a8" fillOpacity="0.4" stroke="#ffe9a8" strokeWidth="1.5" />
            )}
            {canCity && <circle cx={v.x} cy={v.y} r={13} className="pulse-spot" fill="none" stroke="#ffe9a8" strokeWidth="2" />}
            <circle cx={v.x} cy={v.y} r={11} fill="transparent" />
          </g>
        );
      })}
    </svg>
  );
}
