// @ts-nocheck
import { PC, RI } from "../game/constants";
import { calcTotalVP } from "../game/logic";
import { panelStyle, C, FONT_HEAD } from "./styles";

export default function PlayerCard({ p, gs, myIndex }) {
  const totalVP = calcTotalVP(p, gs);
  const hasLA = gs.largestArmy === p.id;
  const hasLR = gs.longestRoad === p.id;
  const vpCards = [...(p.devCards || []), ...(p.newDevCards || [])].filter(c => c === 'vp').length;
  const isCur = p.id === gs.curPlayer;
  return (
    <div style={{
      ...panelStyle,
      borderLeft: `4px solid ${PC[p.id]}`,
      background: isCur ? "linear-gradient(170deg, #f9efd2, #eddcb2)" : panelStyle.background,
      boxShadow: isCur ? `0 0 0 1px ${PC[p.id]}55, 0 3px 12px #00000066` : panelStyle.boxShadow,
    }}>
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: "5px" }}>
        <div style={{ display: "flex", alignItems: "center", gap: "6px" }}>
          <span style={{ color: PC[p.id], fontWeight: 700, fontSize: "13.5px", fontFamily: FONT_HEAD }}>{p.name}</span>
          {p.id === myIndex && <span style={{ fontSize: "10px", color: C.inkSub, border: `1px solid ${C.lineSoft}`, borderRadius: "3px", padding: "0 5px" }}>あなた</span>}
          {isCur && <span style={{ fontSize: "10px", color: C.red, fontWeight: 700 }}>▶手番</span>}
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: "5px" }}>
          {hasLA && <span title="最大騎士軍(+2点)" style={{ fontSize: "12px" }}>⚔️</span>}
          {hasLR && <span title="最長交易路(+2点)" style={{ fontSize: "12px" }}>🛤️</span>}
          <span style={{ color: C.red, fontSize: "14px", fontWeight: 800, fontFamily: FONT_HEAD }}>{totalVP}<span style={{ fontSize: "10px", color: C.inkSub }}>点</span></span>
        </div>
      </div>
      <div style={{ display: "flex", flexWrap: "wrap", gap: "3px", marginBottom: "3px" }}>
        {Object.entries(p.res).map(([r, n]) => (
          <span key={r} style={{
            background: n > 0 ? "#faf2dc" : "#e6d6ae",
            border: `1px solid ${n > 0 ? C.line : C.lineSoft}`,
            borderRadius: "4px", padding: "2px 6px", fontSize: "11px",
            color: n > 0 ? C.ink : C.inkDim, fontWeight: 700,
          }}>
            {RI[r]}{n}
          </span>
        ))}
      </div>
      <div style={{ display: "flex", flexWrap: "wrap", gap: "3px" }}>
        {(p.devCards?.length || 0) + (p.newDevCards?.length || 0) > 0 && (
          <span style={{ background: "#e2d5c2", border: `1px solid ${C.line}`, borderRadius: "4px", padding: "1px 6px", fontSize: "10px", color: C.navy, fontWeight: 700 }}>
            発展カード {(p.devCards?.length || 0) + (p.newDevCards?.length || 0)}枚
          </span>
        )}
        {vpCards > 0 && (
          <span style={{ background: "#f0e0b0", border: "1px solid #b89a4a", borderRadius: "4px", padding: "1px 6px", fontSize: "10px", color: "#7a5a10", fontWeight: 700 }}>
            勝利点×{vpCards}
          </span>
        )}
        {(p.knightsPlayed || 0) > 0 && (
          <span style={{ background: "#e8d0d0", border: "1px solid #a06a6a", borderRadius: "4px", padding: "1px 6px", fontSize: "10px", color: "#7a2a2a", fontWeight: 700 }}>
            騎士×{p.knightsPlayed}
          </span>
        )}
      </div>
    </div>
  );
}
