// @ts-nocheck
import { useState } from "react";
import { PC } from "../game/constants";
import { screenWrap, panelStyle, primaryBtn, C, FONT_HEAD } from "../ui/styles";

export default function LobbyScreen({ gs, myIndex, onSetTarget, onStart, onLeave }) {
  const [copied, setCopied] = useState(false);
  const isHost = myIndex === 0;
  const canStart = gs.players.length >= 2 && gs.players.length <= 4;
  const isQuick = !!gs.quick;

  const copy = () => {
    navigator.clipboard.writeText(gs.code).catch(() => {});
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  };

  return (
    <div style={{ ...screenWrap, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px" }}>
      <div style={{ ...panelStyle, padding: "28px", width: "440px", maxWidth: "95vw", boxShadow: "0 0 0 4px #3b2a1c, 0 14px 40px #000000aa" }}>
        <div style={{ textAlign: "center", marginBottom: "6px" }}>
          <h2 style={{ margin: 0, color: C.ink, letterSpacing: "4px", fontSize: "20px", fontWeight: 700, fontFamily: FONT_HEAD }}>
            {isQuick ? "航海士を探しています" : "出航前の点呼"}
          </h2>
          <div style={{ fontSize: "10px", color: C.line, letterSpacing: "3px", marginTop: "4px" }}>― ⚓ ―</div>
        </div>

        {isQuick ? (
          <div style={{ textAlign: "center", margin: "20px 0 22px" }}>
            <div className="spinner" style={{ marginBottom: "12px" }} />
            <div style={{ fontSize: "14px", color: C.ink, fontWeight: 700 }}>対戦相手を探しています...</div>
            <div style={{ fontSize: "11.5px", color: C.inkDim, marginTop: "6px" }}>相手が見つかると自動でゲームが始まります</div>
          </div>
        ) : (
          <div style={{ textAlign: "center", marginBottom: "20px", marginTop: "14px" }}>
            <div style={{ fontSize: "11.5px", color: C.inkSub, marginBottom: "7px" }}>友達にこの合言葉を伝えてください</div>
            <div style={{ display: "inline-flex", alignItems: "center", gap: "12px", background: "#faf2dc", border: `1px solid ${C.line}`, borderRadius: "6px", padding: "10px 22px", boxShadow: "inset 0 2px 4px #00000015" }}>
              <span style={{ fontSize: "30px", fontWeight: 800, color: C.red, letterSpacing: "10px", fontFamily: FONT_HEAD }}>{gs.code}</span>
              <button className="btn" onClick={copy} style={{ background: "none", border: `1px solid ${C.line}`, borderRadius: "4px", cursor: "pointer", color: copied ? C.green : C.inkSub, fontSize: "11px", padding: "4px 8px", fontFamily: "inherit", fontWeight: 700 }}>
                {copied ? "✓ 済" : "写す"}
              </button>
            </div>
          </div>
        )}

        {isHost && !isQuick && (
          <div style={{ marginBottom: "16px" }}>
            <div style={{ fontSize: "11.5px", color: C.inkSub, marginBottom: "6px" }}>目標プレイヤー数</div>
            <div style={{ display: "flex", gap: "8px" }}>
              {[2, 3, 4].map(n => (
                <button key={n} className="btn" onClick={() => onSetTarget(n)}
                  style={{ flex: 1, padding: "9px", background: gs.numPlayersTarget === n ? "#faf2dc" : "#e6d6ae", color: gs.numPlayersTarget === n ? C.red : C.inkSub, border: gs.numPlayersTarget === n ? `2px solid ${C.red}` : `1px solid ${C.lineSoft}`, borderRadius: "5px", cursor: "pointer", fontSize: "15px", fontWeight: 800, fontFamily: FONT_HEAD }}>
                  {n}人
                </button>
              ))}
            </div>
          </div>
        )}

        <div style={{ marginBottom: "18px" }}>
          <div style={{ fontSize: "11.5px", color: C.inkSub, marginBottom: "8px" }}>乗組員（{gs.players.length}/{gs.numPlayersTarget}）</div>
          {gs.players.map(p => (
            <div key={p.id} style={{ display: "flex", alignItems: "center", gap: "10px", padding: "10px 13px", marginBottom: "5px", background: "#faf2dc", border: `1px solid ${C.lineSoft}`, borderLeft: `4px solid ${PC[p.id]}`, borderRadius: "5px" }}>
              <span style={{ color: PC[p.id], fontSize: "14px", flex: 1, fontWeight: 700, fontFamily: FONT_HEAD }}>{p.name}</span>
              {p.id === 0 && <span style={{ fontSize: "10.5px", color: C.brass, border: `1px solid ${C.line}`, borderRadius: "3px", padding: "1px 7px" }}>船長</span>}
              {p.id === myIndex && <span style={{ fontSize: "11px", color: C.green, fontWeight: 700 }}>あなた</span>}
            </div>
          ))}
          {Array.from({ length: Math.max(0, gs.numPlayersTarget - gs.players.length) }, (_, i) => (
            <div key={i} style={{ padding: "10px 13px", marginBottom: "5px", background: "none", border: `1px dashed ${C.line}`, borderRadius: "5px", color: C.inkDim, fontSize: "13px" }}>
              待機中...
            </div>
          ))}
        </div>

        {!isQuick && (isHost ? (
          <button className="btn" onClick={onStart} disabled={!canStart} style={primaryBtn(canStart)}>
            {gs.players.length < 2 ? `あと${2 - gs.players.length}人必要...` : `出航する（${gs.players.length}人）`}
          </button>
        ) : (
          <div style={{ textAlign: "center", padding: "12px", background: "#faf2dc", border: `1px solid ${C.lineSoft}`, borderRadius: "5px", color: C.inkSub, fontSize: "13px" }}>
            船長が出航の号令を出すのを待っています...
          </div>
        ))}

        <div style={{ textAlign: "center", marginTop: "12px" }}>
          <button className="btn" onClick={onLeave} style={{ background: "none", border: "none", color: C.inkDim, fontSize: "11.5px", cursor: "pointer", textDecoration: "underline", fontFamily: "inherit" }}>
            ← {isQuick ? "マッチングをやめる" : "下船する"}
          </button>
        </div>
      </div>
    </div>
  );
}
