// @ts-nocheck
// 各種モーダル（羊皮紙スタイル）
import { useState } from "react";
import { PC, RI, RN, RES_KEYS } from "../game/constants";
import { emptyRes } from "../game/logic";
import { panelStyle, stepBtn, C, FONT_HEAD } from "./styles";

function Backdrop({ children, z = 170 }) {
  return (
    <div style={{ position: "fixed", inset: 0, background: "#160d08cc", display: "flex", alignItems: "center", justifyContent: "center", zIndex: z, backdropFilter: "blur(2px)" }}>
      {children}
    </div>
  );
}

function ModalBox({ children, width = 340 }) {
  return (
    <div className="modal-pop" style={{ ...panelStyle, padding: "22px", width, maxWidth: "93vw", maxHeight: "90vh", overflowY: "auto", boxShadow: "0 0 0 4px #3b2a1c, 0 12px 40px #000000aa" }}>
      {children}
    </div>
  );
}

// 見出し（明朝 + 飾り罫）
function ModalTitle({ children, color = C.ink }) {
  return (
    <div style={{ textAlign: "center", marginBottom: "14px" }}>
      <div style={{ fontSize: "16px", color, fontWeight: 700, fontFamily: FONT_HEAD, letterSpacing: "2px" }}>{children}</div>
      <div style={{ fontSize: "9px", color: C.line, letterSpacing: "3px", marginTop: "3px" }}>― ✦ ―</div>
    </div>
  );
}

// ─── 勝者オーバーレイ ─────────────────────────────────────
export function WinnerOverlay({ gs, myIndex, onLeave }) {
  const w = gs.winner;
  const isMe = w === myIndex;
  return (
    <Backdrop z={200}>
      <div className="modal-pop" style={{ ...panelStyle, padding: "36px 52px", textAlign: "center", boxShadow: "0 0 0 4px #3b2a1c, 0 0 60px #c9a84f44" }}>
        <div style={{ fontSize: "13px", color: C.inkSub, letterSpacing: "4px", marginBottom: "10px" }}>― 勝敗決す ―</div>
        <div style={{ color: PC[w], fontSize: "30px", fontWeight: 800, fontFamily: FONT_HEAD, marginBottom: "4px" }}>{gs.players[w].name}</div>
        <div style={{ color: C.red, fontSize: "20px", marginBottom: "24px", fontWeight: 700, fontFamily: FONT_HEAD, letterSpacing: "3px" }}>
          {isMe ? "勝利！見事なり！" : "の勝利"}
        </div>
        <button className="btn" onClick={onLeave}
          style={{ padding: "11px 32px", background: "linear-gradient(#a83a28, #7e2417)", color: "#f7ead0", border: "1px solid #5c180e", borderRadius: "4px", fontSize: "14px", cursor: "pointer", fontWeight: 700, fontFamily: FONT_HEAD, letterSpacing: "2px" }}>
          ホームへ戻る
        </button>
      </div>
    </Backdrop>
  );
}

// ─── 資源選択の行（+/−ステッパー）──────────────────────────
function ResStepper({ r, value, max, onChange, extra }) {
  return (
    <div style={{ display: "flex", alignItems: "center", gap: "7px", marginBottom: "6px" }}>
      <span style={{ width: "18px" }}>{RI[r]}</span>
      <span style={{ fontSize: "12px", color: C.inkSub, flex: 1 }}>{RN[r]}</span>
      {extra}
      <button className="btn" style={stepBtn} onClick={() => onChange(Math.max(0, value - 1))}>−</button>
      <span style={{ width: "22px", textAlign: "center", fontSize: "13px", fontWeight: 800, color: value > 0 ? C.red : C.inkDim }}>{value}</span>
      <button className="btn" style={stepBtn} onClick={() => onChange(max === undefined ? value + 1 : Math.min(max, value + 1))}>+</button>
    </div>
  );
}

// ─── 資源破棄モーダル ─────────────────────────────────────
export function DiscardModal({ myP, needed, onConfirm }) {
  const [sel, setSel] = useState(emptyRes());
  const total = Object.values(sel).reduce((a, b) => a + b, 0);
  const ok = total === needed;
  return (
    <Backdrop z={180}>
      <ModalBox width={360}>
        <ModalTitle color={C.red}>資源を捨てよ</ModalTitle>
        <div style={{ fontSize: "12px", color: C.inkSub, marginBottom: "14px", textAlign: "center" }}>
          7が出ました。{needed}枚捨ててください（選択中: {total}/{needed}）
        </div>
        {RES_KEYS.map(r => (
          <ResStepper key={r} r={r} value={sel[r]} max={myP?.res[r] || 0}
            onChange={v => setSel(s => ({ ...s, [r]: v }))}
            extra={<span style={{ fontSize: "11px", color: C.inkDim, width: "40px", textAlign: "right" }}>持:{myP?.res[r] || 0}</span>} />
        ))}
        <button className="btn" onClick={() => ok && onConfirm(sel)} disabled={!ok}
          style={{ marginTop: "12px", display: "block", width: "100%", padding: "11px", background: ok ? "linear-gradient(#a83a28, #7e2417)" : "#d9c9a4", color: ok ? "#f7ead0" : "#a3906a", border: `1px solid ${ok ? "#5c180e" : "#c0ab7e"}`, borderRadius: "4px", cursor: ok ? "pointer" : "not-allowed", fontWeight: 700, fontSize: "13px", fontFamily: "inherit" }}>
          {ok ? "確定して捨てる" : `あと${needed - total}枚選んでください`}
        </button>
      </ModalBox>
    </Backdrop>
  );
}

// ─── 略奪相手選択 ────────────────────────────────────────
export function StealModal({ eligible, onSteal, onSkip }) {
  return (
    <Backdrop>
      <ModalBox width={320}>
        <ModalTitle>略奪する相手を選べ</ModalTitle>
        <div style={{ display: "flex", flexDirection: "column", gap: "8px", marginBottom: "14px" }}>
          {eligible.map(({ idx, name }) => (
            <button key={idx} className="btn" onClick={() => onSteal(idx)}
              style={{ padding: "11px", background: "#faf2dc", border: `2px solid ${PC[idx]}`, borderRadius: "5px", color: PC[idx], cursor: "pointer", fontSize: "14px", fontWeight: 700, fontFamily: FONT_HEAD }}>
              {name} から略奪
            </button>
          ))}
        </div>
        <div style={{ textAlign: "center" }}>
          <button className="btn" onClick={onSkip}
            style={{ padding: "7px 18px", background: "none", color: C.inkSub, border: `1px solid ${C.line}`, borderRadius: "4px", cursor: "pointer", fontSize: "12px", fontFamily: "inherit" }}>
            略奪しない
          </button>
        </div>
      </ModalBox>
    </Backdrop>
  );
}

// ─── 年の実り ───────────────────────────────────────────
export function YearOfPlentyModal({ onConfirm }) {
  const [sel, setSel] = useState({ res1: 'lumber', res2: 'lumber' });
  return (
    <Backdrop>
      <ModalBox width={330}>
        <ModalTitle>年の実り — 資源を2つ選択</ModalTitle>
        {['res1', 'res2'].map((key, i) => (
          <div key={key} style={{ marginBottom: "12px", textAlign: "center" }}>
            <div style={{ fontSize: "12px", color: C.inkSub, marginBottom: "5px" }}>{i + 1}つ目の資源</div>
            <div style={{ display: "flex", gap: "5px", justifyContent: "center", flexWrap: "wrap" }}>
              {RES_KEYS.map(r => (
                <button key={r} className="btn" onClick={() => setSel(s => ({ ...s, [key]: r }))}
                  style={{ padding: "7px 10px", background: sel[key] === r ? "#faf2dc" : "#e6d6ae", border: `2px solid ${sel[key] === r ? C.green : C.lineSoft}`, borderRadius: "5px", cursor: "pointer", fontSize: "15px", fontFamily: "inherit" }}>
                  {RI[r]}
                </button>
              ))}
            </div>
          </div>
        ))}
        <div style={{ textAlign: "center" }}>
          <button className="btn" onClick={() => onConfirm(sel.res1, sel.res2)}
            style={{ marginTop: "6px", padding: "11px 26px", background: "linear-gradient(#54402e, #3b2a1c)", color: "#f0e2c0", border: "1px solid #2c1d12", borderRadius: "4px", cursor: "pointer", fontWeight: 700, fontSize: "13px", fontFamily: "inherit" }}>
            {RI[sel.res1]} + {RI[sel.res2]} を獲得する
          </button>
        </div>
      </ModalBox>
    </Backdrop>
  );
}

// ─── 独占 ──────────────────────────────────────────────
export function MonopolyModal({ onConfirm }) {
  const [sel, setSel] = useState('lumber');
  return (
    <Backdrop>
      <ModalBox width={310}>
        <ModalTitle>独占する資源を選べ</ModalTitle>
        <div style={{ display: "flex", gap: "6px", justifyContent: "center", flexWrap: "wrap", marginBottom: "16px" }}>
          {RES_KEYS.map(r => (
            <button key={r} className="btn" onClick={() => setSel(r)}
              style={{ padding: "11px 13px", background: sel === r ? "#faf2dc" : "#e6d6ae", border: `2px solid ${sel === r ? C.red : C.lineSoft}`, borderRadius: "5px", cursor: "pointer", fontSize: "16px", fontFamily: "inherit" }}>
              {RI[r]}
            </button>
          ))}
        </div>
        <div style={{ textAlign: "center" }}>
          <button className="btn" onClick={() => onConfirm(sel)}
            style={{ padding: "11px 26px", background: "linear-gradient(#a83a28, #7e2417)", color: "#f7ead0", border: "1px solid #5c180e", borderRadius: "4px", cursor: "pointer", fontWeight: 700, fontSize: "13px", fontFamily: "inherit" }}>
            {RI[sel]}を独占する
          </button>
        </div>
      </ModalBox>
    </Backdrop>
  );
}

// ─── 交易オファー（受け手側：承諾 / 逆提案 / 断る）──────────────
export function TradeOfferModal({ gs, myIndex, onAccept, onDecline, onCounter }) {
  const pt = gs.pendingTrade;
  const myP = gs.players[myIndex];
  const fromP = gs.players[pt.from];
  const canAcc = myP && Object.entries(pt.want).every(([r, n]) => (myP.res[r] || 0) >= n);
  const proposerHas = fromP && Object.entries(pt.give).every(([r, n]) => (fromP.res[r] || 0) >= n);
  const boxStyle = { background: "#faf2dc", border: `1px solid ${C.line}`, borderRadius: "6px", padding: "10px 16px", minWidth: "92px" };
  return (
    <Backdrop z={150}>
      <ModalBox width={370}>
        <ModalTitle>{pt.counter ? "逆提案が届いた" : "交易の申し出"}</ModalTitle>
        <div style={{ fontSize: "12px", color: C.inkSub, marginBottom: "14px", textAlign: "center" }}>
          <b style={{ color: PC[pt.from], fontFamily: FONT_HEAD }}>{fromP?.name}</b> より{pt.to === myIndex ? "あなたへ" : "全員へ"}
        </div>
        <div style={{ display: "flex", justifyContent: "center", gap: "20px", marginBottom: "16px" }}>
          <div style={boxStyle}>
            <div style={{ color: C.green, fontSize: "12px", marginBottom: "6px", fontWeight: 700 }}>もらえる</div>
            {Object.entries(pt.give).filter(([, n]) => n > 0).map(([r, n]) => (
              <div key={r} style={{ fontSize: "14px", marginBottom: "2px", color: C.ink }}>{RI[r]} ×{n}</div>
            ))}
          </div>
          <div style={{ color: C.inkDim, fontSize: "22px", alignSelf: "center" }}>⇄</div>
          <div style={boxStyle}>
            <div style={{ color: C.red, fontSize: "12px", marginBottom: "6px", fontWeight: 700 }}>渡す</div>
            {Object.entries(pt.want).filter(([, n]) => n > 0).map(([r, n]) => (
              <div key={r} style={{ fontSize: "14px", marginBottom: "2px", color: C.ink }}>{RI[r]} ×{n}</div>
            ))}
          </div>
        </div>
        {!canAcc && <div style={{ color: C.red, fontSize: "12px", textAlign: "center", marginBottom: "10px" }}>渡す資源が足りないため承諾できません</div>}
        {!proposerHas && <div style={{ color: C.red, fontSize: "12px", textAlign: "center", marginBottom: "10px" }}>相手の資源が不足しています</div>}
        <div style={{ display: "flex", gap: "8px", justifyContent: "center" }}>
          <button className="btn" onClick={onAccept} disabled={!canAcc || !proposerHas}
            style={{ padding: "10px 18px", background: (canAcc && proposerHas) ? "linear-gradient(#3e7a34, #2c5a24)" : "#d9c9a4", color: (canAcc && proposerHas) ? "#eaf5dc" : "#a3906a", border: `1px solid ${(canAcc && proposerHas) ? "#1e3e16" : "#c0ab7e"}`, borderRadius: "4px", cursor: (canAcc && proposerHas) ? "pointer" : "not-allowed", fontWeight: 700, fontFamily: "inherit" }}>
            承諾する
          </button>
          <button className="btn" onClick={onCounter}
            style={{ padding: "10px 18px", background: "linear-gradient(#54402e, #3b2a1c)", color: "#f0e2c0", border: "1px solid #2c1d12", borderRadius: "4px", cursor: "pointer", fontWeight: 700, fontFamily: "inherit" }}>
            逆提案する
          </button>
          <button className="btn" onClick={onDecline}
            style={{ padding: "10px 18px", background: "none", color: C.red, border: `1px solid ${C.red}88`, borderRadius: "4px", cursor: "pointer", fontWeight: 700, fontFamily: "inherit" }}>
            断る
          </button>
        </div>
      </ModalBox>
    </Backdrop>
  );
}
