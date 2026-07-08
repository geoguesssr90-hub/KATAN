// @ts-nocheck
// 交易パネル：銀行交易 / プレイヤー間交渉（相手指定・逆提案）
import { useState } from "react";
import { PC, RI, RN, RES_KEYS } from "../game/constants";
import { emptyRes } from "../game/logic";
import { panelStyle, stepBtn, C, FONT_HEAD } from "./styles";

export default function TradePanel({ gs, myIndex, myP, portRates, counterOf, onClose, onBankTrade, onProposeTrade }) {
  // counterOf: 逆提案元の pendingTrade（あれば逆提案モード）
  const isCounter = !!counterOf;
  const [mode, setMode] = useState(isCounter ? "player" : "bank");
  // 逆提案は「相手のwant→自分がgive」を初期値に（そこから編集して交渉）
  const [give, setGive] = useState(isCounter ? { ...emptyRes(), ...counterOf.want } : emptyRes());
  const [want, setWant] = useState(isCounter ? { ...emptyRes(), ...counterOf.give } : emptyRes());
  const [target, setTarget] = useState(isCounter ? counterOf.from : null); // null = 全員

  const bankValid =
    Object.entries(give).every(([r, n]) => n === 0 || (n % portRates[r] === 0 && (myP?.res[r] || 0) >= n)) &&
    Object.values(want).some(n => n > 0) &&
    Math.abs(Object.entries(give).reduce((a, [r, n]) => a + (n > 0 ? n / portRates[r] : 0), 0) - Object.values(want).reduce((a, b) => a + b, 0)) < 0.001;

  const playerValid =
    Object.values(give).some(n => n > 0) && Object.values(want).some(n => n > 0) &&
    Object.entries(give).every(([r, n]) => !myP || (myP.res[r] || 0) >= n);

  const chipStyle = (active, color) => ({
    padding: "5px 12px",
    background: active ? "#faf2dc" : "#e6d6ae",
    color: color || C.ink,
    border: active ? `2px solid ${color || C.red}` : `1px solid ${C.lineSoft}`,
    borderRadius: "4px", cursor: "pointer", fontSize: "12px", fontWeight: 700, fontFamily: "inherit",
    opacity: active ? 1 : 0.75,
  });

  // 銀行交易で「渡す」側は、レート分（例:4:1なら4個）を1クリックでまとめて増減
  const stepperRow = (r, val, setter, maxed) => {
    const step = mode === "bank" && setter === setGive ? portRates[r] : 1;
    return (
      <div key={r} style={{ display: "flex", alignItems: "center", gap: "7px", marginBottom: "5px" }}>
        <span style={{ width: "18px" }}>{RI[r]}</span>
        <span style={{ fontSize: "11.5px", color: C.inkSub, flex: 1 }}>{RN[r]}</span>
        <span style={{ fontSize: "10.5px", color: C.inkDim, width: "38px", textAlign: "right" }}>{setter === setGive ? `持:${myP?.res[r] || 0}` : ""}</span>
        {mode === "bank" && <span style={{ fontSize: "10.5px", color: portRates[r] < 4 ? C.red : C.inkDim, width: "28px", textAlign: "center", fontWeight: 700 }}>{setter === setGive ? `${portRates[r]}:1` : ""}</span>}
        <button className="btn" style={stepBtn} onClick={() => setter(o => ({ ...o, [r]: Math.max(0, o[r] - step) }))}>−</button>
        <span style={{ width: "22px", textAlign: "center", fontSize: "13px", fontWeight: 800, color: val > 0 ? C.red : C.inkDim }}>{val}</span>
        <button className="btn" style={stepBtn} onClick={() => setter(o => {
          const next = o[r] + step;
          if (maxed !== undefined && next > maxed) return o;
          return { ...o, [r]: next };
        })}>+</button>
      </div>
    );
  };

  return (
    <div style={{ position: "fixed", inset: 0, background: "#160d08bb", display: "flex", alignItems: "center", justifyContent: "center", zIndex: 100, backdropFilter: "blur(2px)" }} onClick={onClose}>
      <div className="modal-pop" style={{ ...panelStyle, padding: "20px", width: "410px", maxWidth: "94vw", maxHeight: "90vh", overflowY: "auto", boxShadow: "0 0 0 4px #3b2a1c, 0 12px 40px #000000aa" }} onClick={e => e.stopPropagation()}>
        <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: "14px" }}>
          <span style={{ color: C.ink, fontSize: "16px", fontWeight: 700, fontFamily: FONT_HEAD, letterSpacing: "2px" }}>
            {isCounter ? "逆提案をつくる" : "交易"}
          </span>
          {!isCounter && (
            <div style={{ display: "flex", gap: "6px" }}>
              {[["bank", "銀行と"], ["player", "プレイヤーと"]].map(([m, label]) => (
                <button key={m} className="btn" onClick={() => setMode(m)} style={chipStyle(mode === m)}>{label}</button>
              ))}
            </div>
          )}
        </div>

        {mode === "bank" && (
          <div style={{ fontSize: "11.5px", color: C.inkSub, marginBottom: "12px", padding: "7px 10px", background: "#faf2dc", borderRadius: "5px", border: `1px solid ${C.lineSoft}` }}>
            交換レート: {Object.entries(portRates).map(([r, n]) => `${RI[r]}${n}:1`).join("  ")}
          </div>
        )}

        {mode === "player" && !isCounter && (
          <div style={{ marginBottom: "12px" }}>
            <div style={{ fontSize: "11.5px", color: C.inkSub, marginBottom: "6px" }}>提案する相手</div>
            <div style={{ display: "flex", gap: "6px", flexWrap: "wrap" }}>
              <button className="btn" onClick={() => setTarget(null)} style={chipStyle(target === null)}>全員</button>
              {gs.players.map((p, i) => i !== myIndex && (
                <button key={i} className="btn" onClick={() => setTarget(i)} style={chipStyle(target === i, PC[i])}>{p.name}</button>
              ))}
            </div>
          </div>
        )}

        {isCounter && (
          <div style={{ fontSize: "11.5px", color: C.inkSub, marginBottom: "12px", padding: "7px 10px", background: "#faf2dc", borderRadius: "5px", border: `1px solid ${C.lineSoft}` }}>
            <b style={{ color: PC[counterOf.from] }}>{gs.players[counterOf.from]?.name}</b> へ条件を変えて提案し直します
          </div>
        )}

        <div style={{ marginBottom: "12px" }}>
          <div style={{ fontSize: "12.5px", color: C.red, marginBottom: "8px", fontWeight: 700, borderBottom: `1px solid ${C.lineSoft}`, paddingBottom: "3px" }}>渡す資源</div>
          {RES_KEYS.map(r => stepperRow(r, give[r], setGive, myP?.res[r] || 0))}
        </div>

        <div style={{ marginBottom: "16px" }}>
          <div style={{ fontSize: "12.5px", color: C.green, marginBottom: "8px", fontWeight: 700, borderBottom: `1px solid ${C.lineSoft}`, paddingBottom: "3px" }}>もらう資源</div>
          {RES_KEYS.map(r => stepperRow(r, want[r], setWant))}
        </div>

        <div style={{ display: "flex", gap: "8px" }}>
          {mode === "bank" ? (
            <button className="btn" onClick={() => bankValid && onBankTrade(give, want)} disabled={!bankValid}
              style={{ flex: 1, padding: "11px", background: bankValid ? "linear-gradient(#3e7a34, #2c5a24)" : "#d9c9a4", color: bankValid ? "#eaf5dc" : "#a3906a", border: `1px solid ${bankValid ? "#1e3e16" : "#c0ab7e"}`, borderRadius: "4px", cursor: bankValid ? "pointer" : "not-allowed", fontWeight: 700, fontFamily: "inherit" }}>
              銀行と交換する
            </button>
          ) : (
            <button className="btn" onClick={() => playerValid && onProposeTrade(give, want, target)} disabled={!playerValid}
              style={{ flex: 1, padding: "11px", background: playerValid ? "linear-gradient(#3e7a34, #2c5a24)" : "#d9c9a4", color: playerValid ? "#eaf5dc" : "#a3906a", border: `1px solid ${playerValid ? "#1e3e16" : "#c0ab7e"}`, borderRadius: "4px", cursor: playerValid ? "pointer" : "not-allowed", fontWeight: 700, fontFamily: "inherit" }}>
              {isCounter ? "逆提案を送る" : target === null ? "全員に提案する" : `${gs.players[target]?.name}に提案する`}
            </button>
          )}
          <button className="btn" onClick={onClose}
            style={{ padding: "11px 16px", background: "none", color: C.inkSub, border: `1px solid ${C.line}`, borderRadius: "4px", cursor: "pointer", fontFamily: "inherit" }}>
            閉じる
          </button>
        </div>
      </div>
    </div>
  );
}
