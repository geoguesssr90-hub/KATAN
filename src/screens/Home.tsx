// @ts-nocheck
import { useState } from "react";
import { screenWrap, panelStyle, inputStyle, primaryBtn, C, FONT_HEAD } from "../ui/styles";

export default function HomeScreen({ loading, error, onCreate, onJoin, onQuickMatch }) {
  const [name, setName] = useState("");
  const [code, setCode] = useState("");
  return (
    <div style={{ ...screenWrap, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px" }}>
      <div style={{ width: "430px", maxWidth: "94vw" }}>

        {/* 羊皮紙の一枚地図 */}
        <div style={{ ...panelStyle, padding: "30px 26px 26px", transform: "rotate(-0.4deg)", boxShadow: "0 0 0 4px #3b2a1c, 0 14px 40px #000000aa" }}>
          <div style={{ textAlign: "center", marginBottom: "22px" }}>
            <div style={{ fontSize: "10px", color: C.inkDim, letterSpacing: "6px", marginBottom: "6px" }}>— 開 拓 者 た ち の 島 —</div>
            <h1 style={{ margin: 0, fontSize: "34px", color: C.ink, letterSpacing: "6px", fontWeight: 800, fontFamily: FONT_HEAD }}>
              カタン航海記
            </h1>
            <div style={{ fontSize: "10px", color: C.brass, letterSpacing: "4px", marginTop: "6px" }}>ONLINE — 2〜4人</div>
            <div style={{ fontSize: "11px", color: C.line, letterSpacing: "3px", marginTop: "10px" }}>―――― ⚓ ――――</div>
          </div>

          <label style={{ fontSize: "12px", color: C.inkSub, display: "block", marginBottom: "5px", fontWeight: 500 }}>航海士の名（省略可）</label>
          <input value={name} onChange={e => setName(e.target.value)} placeholder="名前を入力" style={inputStyle}
            onKeyDown={e => e.key === "Enter" && onQuickMatch(name)} />

          <button className="btn" onClick={() => onQuickMatch(name)} disabled={loading}
            style={{ ...primaryBtn(!loading), marginBottom: "6px" }}>
            ランダム対戦に出航
          </button>
          <div style={{ fontSize: "11px", color: C.inkDim, textAlign: "center", marginBottom: "18px" }}>
            待っている誰かとすぐマッチング（3人戦）。相手がいなければ募集を始めます
          </div>

          <div style={{ display: "flex", alignItems: "center", gap: "10px", marginBottom: "16px" }}>
            <div style={{ flex: 1, height: "1px", background: C.lineSoft }} />
            <span style={{ fontSize: "11px", color: C.inkDim, letterSpacing: "2px" }}>友と航海する</span>
            <div style={{ flex: 1, height: "1px", background: C.lineSoft }} />
          </div>

          <button className="btn" onClick={() => onCreate(name)} disabled={loading}
            style={{ display: "block", width: "100%", padding: "11px", background: "linear-gradient(#54402e, #3b2a1c)", color: "#f0e2c0", border: "1px solid #2c1d12", borderRadius: "4px", fontSize: "14px", fontWeight: 700, letterSpacing: "2px", cursor: "pointer", marginBottom: "14px", fontFamily: FONT_HEAD }}>
            部屋を作る
          </button>

          <div style={{ display: "flex", gap: "8px" }}>
            <input value={code} onChange={e => setCode(e.target.value.toUpperCase())} placeholder="コード" maxLength={4}
              style={{ ...inputStyle, marginBottom: 0, flex: 1, fontSize: "18px", letterSpacing: "6px", textAlign: "center", fontFamily: FONT_HEAD }}
              onKeyDown={e => e.key === "Enter" && onJoin(name, code)} />
            <button className="btn" onClick={() => onJoin(name, code)} disabled={loading}
              style={{ padding: "10px 20px", background: "linear-gradient(#3e7a34, #2c5a24)", color: "#eaf5dc", border: "1px solid #1e3e16", borderRadius: "4px", fontSize: "13px", fontWeight: 700, cursor: "pointer", whiteSpace: "nowrap", fontFamily: FONT_HEAD, letterSpacing: "1px" }}>
              参加
            </button>
          </div>

          {error && (
            <div style={{ marginTop: "12px", padding: "9px 12px", background: "#f3ddd4", border: `1px solid ${C.red}88`, borderRadius: "5px", color: C.red, fontSize: "12px", fontWeight: 500 }}>
              {error}
            </div>
          )}

          <div style={{ marginTop: "20px", paddingTop: "12px", borderTop: `1px dashed ${C.lineSoft}`, fontSize: "11px", color: C.inkDim, lineHeight: 1.8, textAlign: "center" }}>
            定住地1点・都市2点・最大騎士/最長交易路2点<br />先に10点に達した者が島の覇者となる
          </div>
        </div>
      </div>
    </div>
  );
}
