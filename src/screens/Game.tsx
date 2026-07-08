// @ts-nocheck
// ゲーム画面：盤面 + サイドパネル + 各種モーダル
import { useState } from "react";
import { PC, RI, COSTS, DEV_NAMES } from "../game/constants";
import { canAfford, getPortRates } from "../game/logic";
import { screenWrap, panelStyle, btnStyle, sectionHead, C, FONT_HEAD } from "../ui/styles";
import BoardView from "../ui/BoardView";
import DieFace from "../ui/DieFace";
import PlayerCard from "../ui/PlayerCard";
import TradePanel from "../ui/TradePanel";
import { WinnerOverlay, DiscardModal, StealModal, YearOfPlentyModal, MonopolyModal, TradeOfferModal } from "../ui/modals";

export default function GameScreen({ gs, myIndex, diceDisplay, diceRolling, sfxOn, bgmOn, onToggleSfx, onToggleBgm, actions }) {
  // showTrade: null | {counter: pendingTrade|null}
  const [showTrade, setShowTrade] = useState(null);

  if (!gs.players || gs.players.length === 0 || gs.players[gs.curPlayer] === undefined) {
    return <div style={{ ...screenWrap, display: "flex", alignItems: "center", justifyContent: "center" }}>読み込み中...</div>;
  }

  const P = gs.players[gs.curPlayer];
  const myP = myIndex !== null ? gs.players[myIndex] : null;
  const isMyTurn = gs.curPlayer === myIndex;
  const phase = gs.phase;
  const portRates = myP ? getPortRates(myIndex, gs.vertices) : { lumber: 4, brick: 4, wool: 4, grain: 4, ore: 4 };
  const canTrade = isMyTurn && gs.diceRolled && !gs.robberMode && phase === "main" && !gs.pendingTrade && !gs.pendingAction;

  const needsToDiscard = gs.discardQueue?.length > 0 && gs.discardQueue[0]?.idx === myIndex;
  const discardNeeded = needsToDiscard ? gs.discardQueue[0].amount : 0;

  // 発展カード
  const myPlayableCards = myP ? (myP.devCards || []).filter(c => c !== 'vp') : [];
  const canPlayDevCard = isMyTurn && phase === 'main' && !gs.playedDevCardThisTurn && !gs.pendingAction;
  const canPlayKnight = canPlayDevCard && myPlayableCards.includes('knight');
  const canPlayOther = (c) => canPlayDevCard && gs.diceRolled && myPlayableCards.includes(c);

  // 交易オファーモーダルを出すか（受け手側）
  const pt = gs.pendingTrade;
  const showOffer = pt && pt.from !== myIndex &&
    (pt.to === null ? !(pt.declined || []).includes(myIndex) : pt.to === myIndex) &&
    !showTrade; // 逆提案編集中は隠す

  const statusMsg =
    gs.winner != null && gs.players[gs.winner] ? `${gs.players[gs.winner].name}が勝利！` :
    needsToDiscard ? `資源を${discardNeeded}枚捨ててください` :
    (gs.discardQueue?.length || 0) > 0 ? `${gs.players[gs.discardQueue[0].idx]?.name}が資源を捨てています...` :
    gs.pendingRobberSteal && isMyTurn ? "略奪する相手を選んでください" :
    gs.pendingRobberSteal ? `${P.name}が略奪相手を選んでいます...` :
    gs.robberMode ? (isMyTurn ? "山賊を移動するタイルを選択" : `${P.name}が山賊を移動中...`) :
    gs.pendingAction?.type === 'roadBuilding' ? (isMyTurn ? `道路建設: 道をあと${gs.pendingAction.roadsLeft}本置けます` : `${P.name}が道路建設中...`) :
    gs.pendingAction?.type === 'yearOfPlenty' ? (isMyTurn ? "年の実り: 資源を2つ選んでください" : `${P.name}が資源を選んでいます...`) :
    gs.pendingAction?.type === 'monopoly' ? (isMyTurn ? "独占: 資源を選んでください" : `${P.name}が独占する資源を選んでいます...`) :
    pt ? (pt.from === myIndex ? "交易の返事を待っています..." : "交易の申し出が届いています") :
    phase === "setup" ? (isMyTurn ? `セットアップ: ${gs.setupSub === "settlement" ? "定住地を置ける場所をダブルクリック" : "道を置ける場所をダブルクリック"}` : `${P.name}がセットアップ中...`) :
    !isMyTurn ? `${P.name}の手番を待っています` :
    !gs.diceRolled ? "サイコロを振ってください（騎士カードは振る前でも使用可）" :
    "盤面の光る場所をダブルクリックすると定住地・道・都市を建設できます";

  const endTurnDisabled = !gs.diceRolled || gs.robberMode || !!gs.pendingAction || !!gs.pendingRobberSteal || (gs.discardQueue?.length || 0) > 0;

  // 木のテーブル上の小さなチップ
  const woodChip = (active) => ({
    padding: "3px 10px",
    background: active ? "#e8d9b0" : "rgba(0,0,0,0.25)",
    color: active ? "#3d2f1e" : C.creamDim,
    border: `1px solid ${active ? "#b89d6a" : "#00000055"}`,
    borderRadius: "3px", fontSize: "11px",
    cursor: "pointer", fontFamily: "inherit", fontWeight: 700,
  });

  return (
    <div style={{ ...screenWrap, display: "flex", flexDirection: "column", alignItems: "center", padding: "10px", gap: "10px" }}>

      {/* ヘッダー */}
      <div style={{ display: "flex", alignItems: "center", justifyContent: "space-between", width: "100%", maxWidth: "1000px", padding: "0 4px", flexWrap: "wrap", gap: "6px" }}>
        <h1 style={{ margin: 0, fontSize: "19px", color: "#d9b96a", letterSpacing: "4px", fontWeight: 700, fontFamily: FONT_HEAD }}>カタン航海記</h1>
        <div style={{ display: "flex", alignItems: "center", gap: "7px", flexWrap: "wrap", justifyContent: "flex-end" }}>
          {gs.largestArmy !== null && (
            <div style={{ ...woodChip(false), cursor: "default", color: "#d9b96a" }}>⚔️最大騎士 {gs.players[gs.largestArmy]?.name}</div>
          )}
          {gs.longestRoad !== null && (
            <div style={{ ...woodChip(false), cursor: "default", color: "#d9b96a" }}>🛤️最長交易路 {gs.players[gs.longestRoad]?.name}</div>
          )}
          <button className="btn" onClick={onToggleBgm} style={woodChip(bgmOn)}>♪ BGM {bgmOn ? "ON" : "OFF"}</button>
          <button className="btn" onClick={onToggleSfx} style={woodChip(sfxOn)}>♪ 効果音 {sfxOn ? "ON" : "OFF"}</button>
          {!gs.quick && <span style={{ fontSize: "11px", color: C.creamDim }}>合言葉 <b style={{ color: "#d9b96a", fontFamily: FONT_HEAD, letterSpacing: "2px" }}>{gs.code}</b></span>}
          <div style={{ ...woodChip(isMyTurn), cursor: "default" }}>
            {isMyTurn ? "あなたの手番" : `${P.name}の手番`}
          </div>
          <button className="btn" onClick={actions.leave} style={{ background: "none", border: "none", color: C.creamDim, fontSize: "11px", cursor: "pointer", textDecoration: "underline", fontFamily: "inherit" }}>退室</button>
        </div>
      </div>

      {/* モーダル群 */}
      {gs.winner != null && gs.players[gs.winner] && <WinnerOverlay gs={gs} myIndex={myIndex} onLeave={actions.leave} />}
      {needsToDiscard && <DiscardModal key={`d${gs.discardQueue.length}`} myP={myP} needed={discardNeeded} onConfirm={actions.discard} />}
      {gs.pendingRobberSteal && isMyTurn && <StealModal eligible={gs.pendingRobberSteal.eligible} onSteal={actions.steal} onSkip={actions.skipSteal} />}
      {gs.pendingAction?.type === 'yearOfPlenty' && isMyTurn && <YearOfPlentyModal onConfirm={actions.yearOfPlenty} />}
      {gs.pendingAction?.type === 'monopoly' && isMyTurn && <MonopolyModal onConfirm={actions.monopoly} />}
      {showOffer && (
        <TradeOfferModal gs={gs} myIndex={myIndex}
          onAccept={actions.acceptTrade}
          onDecline={actions.declineTrade}
          onCounter={() => setShowTrade({ counter: pt })} />
      )}

      {/* 他プレイヤーの破棄待ちトースト */}
      {(gs.discardQueue?.length || 0) > 0 && !needsToDiscard && (
        <div className="toast" style={{ position: "fixed", top: "18px", left: "50%", transform: "translateX(-50%)", background: "#f4e9cb", border: "1px solid #b89d6a", borderRadius: "6px", padding: "10px 22px", zIndex: 160, fontSize: "13px", color: C.red, fontWeight: 700, boxShadow: "0 6px 20px #000a" }}>
          {gs.players[gs.discardQueue[0]?.idx]?.name}が資源を捨てています...
        </div>
      )}

      <div style={{ display: "flex", gap: "14px", flexWrap: "wrap", justifyContent: "center", width: "100%", maxWidth: "1000px" }}>

        {/* 盤面 */}
        <div style={{ flexShrink: 0 }}>
          <BoardView gs={gs} myIndex={myIndex}
            onVertex={actions.vertexClick} onEdge={actions.edgeClick} onHex={actions.hexClick} />
        </div>

        {/* サイドパネル */}
        <div style={{ flex: "1 1 250px", maxWidth: "295px", display: "flex", flexDirection: "column", gap: "8px" }}>

          {/* ステータス + サイコロ */}
          <div style={{ ...panelStyle, borderLeft: `4px solid ${PC[gs.curPlayer]}` }}>
            <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: "7px" }}>
              <span style={{ color: PC[gs.curPlayer], fontWeight: 700, fontSize: "14px", fontFamily: FONT_HEAD }}>{P.name}の手番</span>
              <div style={{ display: "flex", gap: "5px", alignItems: "center" }}>
                <DieFace value={diceDisplay[0]} size={32} rolling={diceRolling} />
                <DieFace value={diceDisplay[1]} size={32} rolling={diceRolling} />
              </div>
            </div>
            <div style={{ fontSize: "11.5px", background: "#faf2dc", border: `1px solid ${C.lineSoft}`, borderRadius: "4px", padding: "6px 9px", color: isMyTurn ? C.red : C.inkSub, lineHeight: 1.5, fontWeight: isMyTurn ? 700 : 400 }}>
              {statusMsg}
            </div>
          </div>

          {/* プレイヤー一覧 */}
          {gs.players.map(p => <PlayerCard key={p.id} p={p} gs={gs} myIndex={myIndex} />)}

          {/* 使用可能な発展カード */}
          {myP && (myP.devCards?.length || 0) > 0 && (
            <div style={panelStyle}>
              <div style={sectionHead}>発展カード（使用可）</div>
              <div style={{ display: "flex", flexDirection: "column", gap: "3px" }}>
                {Object.entries((myP.devCards || []).reduce((acc, c) => ({ ...acc, [c]: (acc[c] || 0) + 1 }), {})).map(([c, n]) => {
                  if (c === 'vp') return (
                    <div key={c} style={{ fontSize: "11.5px", color: C.inkSub, padding: "5px 9px", background: "#faf2dc", border: `1px solid ${C.lineSoft}`, borderRadius: "4px" }}>
                      {DEV_NAMES[c]} ×{n}（自動計上）
                    </div>
                  );
                  const canPlay = c === 'knight' ? canPlayKnight : canPlayOther(c);
                  return (
                    <button key={c} className="btn" onClick={() => actions.playDevCard(c)} disabled={!canPlay}
                      style={{ ...btnStyle(!canPlay, false), textAlign: "left", padding: "6px 9px" }}>
                      {DEV_NAMES[c]} ×{n}
                      {c === 'knight' && !gs.diceRolled && isMyTurn && " （サイコロ前OK）"}
                    </button>
                  );
                })}
              </div>
            </div>
          )}

          {/* 今ターン購入したカード */}
          {myP && (myP.newDevCards?.length || 0) > 0 && (
            <div style={{ ...panelStyle, padding: "7px 11px", opacity: 0.85 }}>
              <div style={{ fontSize: "10.5px", color: C.inkDim, marginBottom: "3px" }}>今ターン購入（次ターンから使用可）</div>
              {Object.entries((myP.newDevCards || []).reduce((acc, c) => ({ ...acc, [c]: (acc[c] || 0) + 1 }), {})).map(([c, n]) => (
                <div key={c} style={{ fontSize: "11.5px", color: C.inkSub }}>{DEV_NAMES[c]} ×{n}</div>
              ))}
            </div>
          )}

          {/* アクション */}
          {phase === "main" && isMyTurn && (
            <div style={panelStyle}>
              <div style={sectionHead}>アクション</div>
              <div style={{ display: "flex", flexDirection: "column", gap: "4px" }}>
                <button className="btn" onClick={actions.rollDice} disabled={gs.diceRolled || diceRolling} style={btnStyle(gs.diceRolled || diceRolling, false)}>
                  サイコロを振る
                </button>
                <button className="btn" onClick={actions.buyDevCard} disabled={!gs.diceRolled || !myP || !canAfford(myP, COSTS.devCard) || !gs.devDeck?.length}
                  style={btnStyle(!gs.diceRolled || !myP || !canAfford(myP, COSTS.devCard) || !gs.devDeck?.length, false)}>
                  発展カード購入（残{gs.devDeck?.length || 0}） <span style={{ float: "right", fontSize: "10px", opacity: 0.8 }}>⛏️🌾🐑</span>
                </button>
                <button className="btn" onClick={() => setShowTrade({ counter: null })} disabled={!canTrade} style={btnStyle(!canTrade, !!showTrade)}>
                  交易・交渉
                </button>
                <button className="btn" onClick={() => { setShowTrade(null); actions.endTurn(); }} disabled={endTurnDisabled}
                  style={{ ...btnStyle(endTurnDisabled, false), marginTop: "4px", background: endTurnDisabled ? "#d9c9a4" : "linear-gradient(#a83a28, #7e2417)", border: `1px solid ${endTurnDisabled ? "#c0ab7e" : "#5c180e"}`, fontFamily: FONT_HEAD, letterSpacing: "2px" }}>
                  手番を終える
                </button>
              </div>
            </div>
          )}

          {/* 建設コスト早見表（ボタンではなく盤面のダブルクリックで建設） */}
          {phase === "main" && isMyTurn && (
            <div style={{ ...panelStyle, padding: "8px 11px" }}>
              <div style={{ ...sectionHead, marginBottom: "5px" }}>建設（盤面の光る場所をダブルクリック）</div>
              <div style={{ display: "flex", flexDirection: "column", gap: "4px" }}>
                {[
                  ["🛤️ 道", "🪵🧱", COSTS.road],
                  ["🏠 定住地", "🪵🧱🐑🌾", COSTS.settlement],
                  ["🏰 都市に昇格", "🌾🌾⛏️⛏️⛏️", COSTS.city],
                ].map(([label, icons, cost]) => {
                  const ok = !!(gs.diceRolled && myP && !gs.pendingAction && canAfford(myP, cost));
                  return (
                    <div key={label} style={{
                      display: "flex", justifyContent: "space-between", alignItems: "center",
                      fontSize: "11.5px", padding: "5px 9px", borderRadius: "4px", fontWeight: 700,
                      background: ok ? "#faf2dc" : "#e6d6ae", border: `1px solid ${ok ? C.line : C.lineSoft}`,
                      color: ok ? C.ink : C.inkDim, opacity: ok ? 1 : 0.65,
                    }}>
                      <span>{label}</span>
                      <span style={{ fontSize: "12px" }}>{icons}</span>
                    </div>
                  );
                })}
              </div>
            </div>
          )}

          {/* 自分が出した交易提案の状況 */}
          {pt && pt.from === myIndex && (
            <div style={{ ...panelStyle, textAlign: "center" }}>
              <div style={{ fontSize: "12.5px", color: C.ink, marginBottom: "6px", fontWeight: 700, fontFamily: FONT_HEAD }}>交易提案中...</div>
              {(pt.declined || []).length > 0 && (
                <div style={{ fontSize: "11px", color: C.red, marginBottom: "6px" }}>
                  断られた: {(pt.declined || []).map(i => gs.players[i]?.name).join("、")}
                </div>
              )}
              <button className="btn" onClick={actions.cancelTrade}
                style={{ padding: "7px 18px", background: "none", color: C.red, border: `1px solid ${C.red}88`, borderRadius: "4px", cursor: "pointer", fontSize: "12px", fontFamily: "inherit", fontWeight: 700 }}>
                提案を取り下げる
              </button>
            </div>
          )}

          {/* 港レート */}
          <div style={{ ...panelStyle, padding: "8px 11px" }}>
            <div style={{ fontSize: "10.5px", color: C.inkSub, marginBottom: "4px", fontWeight: 700 }}>港レート（あなた）</div>
            <div style={{ display: "flex", flexWrap: "wrap", gap: "4px" }}>
              {Object.entries(portRates).map(([r, n]) => (
                <span key={r} style={{ fontSize: "10.5px", color: n < 4 ? C.red : C.inkDim, background: n < 4 ? "#faf2dc" : "none", border: `1px solid ${n < 4 ? C.line : C.lineSoft}`, borderRadius: "3px", padding: "1px 5px", fontWeight: 700 }}>
                  {RI[r]}{n}:1
                </span>
              ))}
            </div>
          </div>

          {/* ログ（航海日誌） */}
          <div style={{ ...panelStyle, padding: "9px 11px", maxHeight: "150px", overflowY: "auto", flex: 1 }}>
            <div style={sectionHead}>航海日誌</div>
            {(gs.log || []).map((l, i) => (
              <div key={i} style={{
                fontSize: "11px", color: i === 0 ? C.ink : C.inkDim, padding: "2px 0 2px 7px", lineHeight: 1.5,
                borderLeft: i === 0 ? `3px solid ${C.red}` : "3px solid transparent",
                fontWeight: i === 0 ? 700 : 400,
              }}>{l}</div>
            ))}
          </div>

          <div style={{ fontSize: "10px", color: C.creamDim, lineHeight: 1.7, textAlign: "center" }}>
            定住地1点・都市2点・最大騎士2点・最長交易路2点 — 10点で勝利
          </div>
        </div>
      </div>

      {/* 交易パネル（通常 / 逆提案） */}
      {showTrade && (showTrade.counter ? (gs.pendingTrade && gs.pendingTrade.from !== myIndex) : canTrade) && (
        <TradePanel
          key={showTrade.counter ? `c${showTrade.counter.from}` : "t"}
          gs={gs} myIndex={myIndex} myP={myP} portRates={portRates}
          counterOf={showTrade.counter}
          onClose={() => setShowTrade(null)}
          onBankTrade={(give, want) => { actions.bankTrade(give, want); setShowTrade(null); }}
          onProposeTrade={(give, want, target) => { actions.proposeTrade(give, want, target); setShowTrade(null); }}
        />
      )}
    </div>
  );
}
