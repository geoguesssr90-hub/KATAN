// @ts-nocheck
// アプリ本体：画面遷移・Firebase同期・ゲームアクション
import { useState, useEffect, useCallback, useRef } from "react";
import { db, ref, set, get, onValue, off, runTransaction } from "./firebase";
import {
  normalizeGS, createInitialState, initPlayer, addLog, genCode, emptyRes, removeOne,
  startGameState, updateLongestRoad, updateLargestArmy, calcTotalVP,
  canAfford, canPlaceSett, isConnRoad, getPortRates,
} from "./game/logic";
import { TR, RI, COSTS } from "./game/constants";
import { playSfx, toggleSfx, isSfxOn, toggleBgm, isBgmOn, ensureBgmPref } from "./sound";
import HomeScreen from "./screens/Home";
import LobbyScreen from "./screens/Lobby";
import GameScreen from "./screens/Game";
import { screenWrap } from "./ui/styles";
import "./App.css";

const QUICK_REF = "quickmatch/waiting";
const QUICK_TTL = 10 * 60 * 1000; // 募集エントリの有効期限

export default function CatanOnline() {
  const [screen, setScreen] = useState("home");
  const [myIndex, setMyIndex] = useState(null);
  const [gs, setGs] = useState(null);
  const [error, setError] = useState("");
  const [loading, setLoading] = useState(false);
  const [diceRolling, setDiceRolling] = useState(false);
  const [diceDisplay, setDiceDisplay] = useState([1, 1]);
  const [sfxOn, setSfxOn] = useState(isSfxOn());
  const [bgmOn, setBgmOn] = useState(isBgmOn());

  const pollRef = useRef(null);
  const diceTimer = useRef(null);
  const prevWinner = useRef(null);

  // ── Firebase入出力 ──
  const loadGame = async (code) => {
    try { const snap = await get(ref(db, "games/" + code)); if (!snap.exists()) return null; return normalizeGS(snap.val()); } catch { return null; }
  };
  const saveGame = async (state) => {
    try { await set(ref(db, "games/" + state.code), state); } catch (e) { console.error(e); }
  };
  const loadMyInfo = () => {
    try { const r = localStorage.getItem("catan:me"); return r ? JSON.parse(r) : null; } catch { return null; }
  };
  const saveMyInfo = (info) => {
    try { localStorage.setItem("catan:me", JSON.stringify(info)); } catch { /* noop */ }
  };

  // ── リアルタイム購読 ──
  const startPolling = useCallback((code) => {
    if (pollRef.current) off(pollRef.current);
    const gameRef = ref(db, "games/" + code);
    onValue(gameRef, (snap) => {
      if (snap.exists()) {
        const s = normalizeGS(snap.val()); if (!s) return;
        setGs(s);
        if (s.phase === "main" || s.phase === "setup" || s.phase === "ended") setScreen("game");
        else if (s.phase === "lobby") setScreen("lobby");
      }
    });
    pollRef.current = gameRef;
  }, []);

  useEffect(() => {
    (async () => {
      const info = loadMyInfo();
      if (info) {
        const s = await loadGame(info.code);
        if (s) { setMyIndex(info.index); setGs(s); setScreen(s.phase === "lobby" ? "lobby" : "game"); startPolling(info.code); }
      }
    })();
    return () => { if (pollRef.current) off(pollRef.current); if (diceTimer.current) clearInterval(diceTimer.current); };
  }, []);

  // 勝敗が決まった瞬間に効果音
  useEffect(() => {
    const w = gs?.winner;
    if (w != null && prevWinner.current == null) playSfx(w === myIndex ? "win" : "lose");
    prevWinner.current = w ?? null;
  }, [gs?.winner]);

  // ── サウンド切替 ──
  const handleToggleSfx = () => { toggleSfx(); setSfxOn(isSfxOn()); };
  const handleToggleBgm = () => { toggleBgm(); setBgmOn(isBgmOn()); };

  // ── ホーム画面のアクション ──
  async function handleCreate(name0) {
    ensureBgmPref(); setBgmOn(isBgmOn());
    setLoading(true); setError("");
    const name = (name0 || "").trim() || "ホスト";
    const code = genCode();
    const state = createInitialState(code, name);
    await saveGame(state);
    saveMyInfo({ code, index: 0 });
    setMyIndex(0); setGs(state); setScreen("lobby"); startPolling(code); setLoading(false);
  }

  // 参加処理の共通部分（通常参加・ランダムマッチ両方から使う）
  async function joinGameState(state, name) {
    const idx = state.players.length;
    let ns = addLog({ ...state, players: [...state.players, initPlayer(idx, name)], updatedAt: Date.now() }, `${name}が参加しました`);
    // ランダムマッチは人数が揃ったら自動スタート
    if (ns.quick && ns.players.length >= ns.numPlayersTarget) {
      ns = startGameState(ns);
      playSfx("gameStart");
    }
    await saveGame(ns);
    saveMyInfo({ code: ns.code, index: idx });
    setMyIndex(idx); setGs(ns); setScreen(ns.phase === "lobby" ? "lobby" : "game"); startPolling(ns.code);
  }

  async function handleJoin(name0, code0) {
    ensureBgmPref(); setBgmOn(isBgmOn());
    setLoading(true); setError("");
    const code = (code0 || "").trim().toUpperCase();
    if (!code) { setError("ゲームコードを入力してください"); setLoading(false); return; }
    const state = await loadGame(code);
    if (!state) { setError("ゲームが見つかりません"); playSfx("error"); setLoading(false); return; }
    if (state.phase !== "lobby") { setError("ゲームはすでに開始しています"); playSfx("error"); setLoading(false); return; }
    if (state.players.length >= state.numPlayersTarget) { setError("満員です"); playSfx("error"); setLoading(false); return; }
    const name = (name0 || "").trim() || `プレイヤー${state.players.length + 1}`;
    await joinGameState(state, name);
    setLoading(false);
  }

  // ── ランダム対戦（マッチング）──
  async function handleQuickMatch(name0) {
    ensureBgmPref(); setBgmOn(isBgmOn());
    setLoading(true); setError("");
    const name = (name0 || "").trim() || "プレイヤー";

    // 募集中エントリをトランザクションで安全に取得（先着1名が取る）
    let claimed = null;
    try {
      const res = await runTransaction(ref(db, QUICK_REF), (cur) => {
        claimed = null;
        // 初回はローカルキャッシュ(null)で呼ばれることがある。
        // ここで undefined(中断) を返すとサーバー未確認のまま終わるので、
        // null をコミットしてサーバー値での再実行を促す。
        if (!cur) return null;
        if (cur.code && Date.now() - (cur.at || 0) < QUICK_TTL) {
          claimed = cur.code;
          return null; // エントリを消費
        }
        return undefined; // 期限切れエントリには触らない（この後の募集登録で上書きされる）
      });
      if (!res.committed) claimed = null;
    } catch { claimed = null; }

    if (claimed) {
      const state = await loadGame(claimed);
      if (state && state.phase === "lobby" && state.players.length < state.numPlayersTarget) {
        await joinGameState(state, name);
        setLoading(false);
        return;
      }
      // 募集ゲームが消えていた/埋まっていた → 自分が募集側になる
    }

    // 誰も待っていない → 自分がゲームを作って募集を出す
    const code = genCode();
    const state = { ...createInitialState(code, name), quick: true, numPlayersTarget: 2 };
    await saveGame(state);
    try { await set(ref(db, QUICK_REF), { code, at: Date.now() }); } catch { /* noop */ }
    saveMyInfo({ code, index: 0 });
    setMyIndex(0); setGs(state); setScreen("lobby"); startPolling(code); setLoading(false);
  }

  // ── ロビー ──
  async function handleSetTarget(n) {
    const s = await loadGame(gs.code); if (!s) return;
    await saveGame({ ...s, numPlayersTarget: n, updatedAt: Date.now() });
  }

  async function handleStart() {
    ensureBgmPref(); setBgmOn(isBgmOn());
    const s = await loadGame(gs.code); if (!s || s.phase !== "lobby" || s.players.length < 2) return;
    playSfx("gameStart");
    const ns = startGameState(s);
    await saveGame(ns); setGs(ns); setScreen("game");
  }

  async function handleLeave() {
    // ランダムマッチ待機中に抜けたら募集エントリも消す
    if (gs?.quick && gs.phase === "lobby") {
      try {
        await runTransaction(ref(db, QUICK_REF), (cur) => {
          if (!cur) return null; // 初回null対策：コミットしてサーバー値で再実行させる
          return cur.code === gs.code ? null : undefined; // 自分の募集だけ消す
        });
      } catch { /* noop */ }
    }
    if (pollRef.current) off(pollRef.current);
    localStorage.removeItem("catan:me");
    setScreen("home"); setGs(null); setMyIndex(null);
  }

  // ── ゲーム内アクション共通：最新状態を読んで更新して書き戻す ──
  async function doAction(fn) {
    const s = await loadGame(gs.code); if (!s) return null;
    const ns = fn(s);
    if (ns) { ns.updatedAt = Date.now(); await saveGame(ns); setGs(ns); return ns; }
    return null;
  }

  async function handleVertexClick(vid) {
    if (!gs || gs.curPlayer !== myIndex) return;
    const result = await doAction(s => {
      const { phase, setupSub, vertices, edges, players, curPlayer, setupStep } = s;
      const P = players[curPlayer];
      if (phase === "setup" && setupSub === "settlement") {
        if (!canPlaceSett(vid, vertices)) return null;
        const isR2 = setupStep >= players.length;
        const nv = vertices.map(v => v.id === vid ? { ...v, building: { player: curPlayer, type: "settlement" } } : v);
        let np = players.map((p, i) => i !== curPlayer ? p : { ...p, vp: p.vp + 1, settlementsLeft: p.settlementsLeft - 1 });
        let extra = "";
        if (isR2) {
          const rg = emptyRes();
          const vert = vertices.find(v => v.id === vid);
          vert?.hexIds.forEach(hid => { const r = TR[s.hexes.find(h => h.id === hid)?.terrain]; if (r) rg[r]++; });
          np = np.map((p, i) => i !== curPlayer ? p : { ...p, res: Object.fromEntries(Object.entries(p.res).map(([r, n]) => [r, n + (rg[r] || 0)])) });
          const items = Object.entries(rg).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" ");
          if (items) extra = `（${items}獲得）`;
        }
        return addLog({ ...s, vertices: nv, players: np, setupSub: "road", lastVid: vid }, `${P.name}が定住地を配置${extra}。次に道を置いてください`);
      }
      if (phase === "main" && s.diceRolled && s.buildMode === "settlement") {
        if (!canPlaceSett(vid, vertices) || !isConnRoad(vid, edges, curPlayer) || !canAfford(P, COSTS.settlement)) return null;
        const nv = vertices.map(v => v.id === vid ? { ...v, building: { player: curPlayer, type: "settlement" } } : v);
        const np = players.map((p, i) => i !== curPlayer ? p : { ...p, vp: p.vp + 1, settlementsLeft: p.settlementsLeft - 1, res: Object.fromEntries(Object.entries(p.res).map(([r, n]) => [r, n - (COSTS.settlement[r] || 0)])) });
        let ns = addLog({ ...s, vertices: nv, players: np, buildMode: null }, `${P.name}が定住地を建設！`);
        ns = updateLongestRoad(ns); // 相手の道が分断される可能性がある
        const totalVP = calcTotalVP(np[curPlayer], ns);
        if (totalVP >= 10) ns = { ...ns, winner: curPlayer, phase: "ended" };
        return ns;
      }
      if (phase === "main" && s.diceRolled && s.buildMode === "city") {
        const v = vertices.find(v => v.id === vid);
        if (!v?.building || v.building.player !== curPlayer || v.building.type !== "settlement" || !canAfford(P, COSTS.city)) return null;
        const nv = vertices.map(v => v.id === vid ? { ...v, building: { player: curPlayer, type: "city" } } : v);
        const np = players.map((p, i) => i !== curPlayer ? p : { ...p, vp: p.vp + 1, citiesLeft: p.citiesLeft - 1, settlementsLeft: p.settlementsLeft + 1, res: Object.fromEntries(Object.entries(p.res).map(([r, n]) => [r, n - (COSTS.city[r] || 0)])) });
        let ns = addLog({ ...s, vertices: nv, players: np, buildMode: null }, `${P.name}が都市を建設！`);
        const totalVP = calcTotalVP(np[curPlayer], ns);
        if (totalVP >= 10) ns = { ...ns, winner: curPlayer, phase: "ended" };
        return ns;
      }
      return null;
    });
    if (result) playSfx("build");
  }

  async function handleEdgeClick(eid) {
    if (!gs || gs.curPlayer !== myIndex) return;
    const result = await doAction(s => {
      const { phase, setupSub, vertices, edges, players, curPlayer, setupStep, setupOrder } = s;
      const edge = edges.find(e => Number(e.id) === Number(eid));
      const P = players[curPlayer];
      if (!P || !edge || edge.road != null) return null;
      const v1b = vertices.find(v => v.id === edge.v1), v2b = vertices.find(v => v.id === edge.v2);

      if (phase === "setup" && setupSub === "road") {
        if (Number(edge.v1) !== Number(s.lastVid) && Number(edge.v2) !== Number(s.lastVid)) return null;
        const ne = edges.map(e => e.id === eid ? { ...e, road: curPlayer } : e);
        const np = players.map((p, i) => i !== curPlayer ? p : { ...p, roadsLeft: p.roadsLeft - 1 });
        const next = setupStep + 1; const done = next >= setupOrder.length;
        let ns = { ...s, edges: ne, players: np, setupStep: next, setupSub: "settlement", buildMode: null, lastVid: null };
        if (done) { ns = addLog({ ...ns, phase: "main", curPlayer: 0, diceRolled: false, dice: null }, "セットアップ完了！" + players[0].name + "のターン"); }
        else { const ncp = setupOrder[next]; ns = addLog({ ...ns, curPlayer: ncp }, `${players[ncp].name}が定住地を置いてください`); }
        return updateLongestRoad(ns);
      }

      // 道路建設カード（無料、サイコロ前後どちらでも）
      if (phase === "main" && s.pendingAction?.type === "roadBuilding") {
        const connected = v1b?.building?.player === curPlayer || v2b?.building?.player === curPlayer || isConnRoad(edge.v1, edges, curPlayer) || isConnRoad(edge.v2, edges, curPlayer);
        if (!connected) return null;
        const ne = edges.map(e => e.id === eid ? { ...e, road: curPlayer } : e);
        const np = players.map((p, i) => i !== curPlayer ? p : { ...p, roadsLeft: p.roadsLeft - 1 });
        const roadsLeft = s.pendingAction.roadsLeft - 1;
        let ns = { ...s, edges: ne, players: np, pendingAction: roadsLeft > 0 ? { type: 'roadBuilding', roadsLeft } : null };
        ns = updateLongestRoad(ns);
        const totalVP = calcTotalVP(np[curPlayer], ns);
        if (totalVP >= 10) ns = { ...ns, winner: curPlayer, phase: "ended" };
        return addLog(ns, `${P.name}が道を建設！（道路建設カード、残り${roadsLeft}本）`);
      }

      if (phase === "main" && s.buildMode === "road" && s.diceRolled && canAfford(P, COSTS.road)) {
        const connected = v1b?.building?.player === curPlayer || v2b?.building?.player === curPlayer || isConnRoad(edge.v1, edges, curPlayer) || isConnRoad(edge.v2, edges, curPlayer);
        if (!connected) return null;
        const ne = edges.map(e => e.id === eid ? { ...e, road: curPlayer } : e);
        const np = players.map((p, i) => i !== curPlayer ? p : { ...p, roadsLeft: p.roadsLeft - 1, res: Object.fromEntries(Object.entries(p.res).map(([r, n]) => [r, n - (COSTS.road[r] || 0)])) });
        const ns = addLog({ ...s, edges: ne, players: np, buildMode: null }, `${P.name}が道を建設！`);
        return updateLongestRoad(ns);
      }
      return null;
    });
    if (result) playSfx("build");
  }

  async function handleHexClick(hid) {
    if (!gs || gs.curPlayer !== myIndex || !gs.robberMode) return;
    await doAction(s => {
      if (!s.robberMode) return null;
      const hex = s.hexes.find(h => h.id === hid);
      if (!hex || hex.hasRobber) return null;
      const nh = s.hexes.map(h => ({ ...h, hasRobber: h.id === hid }));
      // 略奪対象（そのヘックスに建物を持つ他プレイヤー）
      const eligibleSet = new Set();
      hex.vertexIds.forEach(vid => {
        const v = s.vertices.find(v => v.id === vid);
        if (v?.building && v.building.player !== s.curPlayer) eligibleSet.add(v.building.player);
      });
      const eligible = [...eligibleSet].map(idx => ({ idx, name: s.players[idx].name }));
      const ns = { ...s, hexes: nh, robberMode: false };
      if (eligible.length > 0) {
        return addLog({ ...ns, pendingRobberSteal: { eligible } }, "山賊を移動しました。略奪する相手を選んでください");
      }
      return addLog(ns, "山賊を移動しました");
    });
  }

  async function handleSteal(targetIdx) {
    const result = await doAction(s => {
      if (!s.pendingRobberSteal) return null;
      const target = s.players[targetIdx];
      const resources = Object.entries(target.res).flatMap(([r, n]) => Array(n).fill(r));
      if (resources.length === 0) {
        return addLog({ ...s, pendingRobberSteal: null }, `${target.name}は資源を持っていませんでした`);
      }
      const stolen = resources[Math.floor(Math.random() * resources.length)];
      const P = s.players[s.curPlayer];
      const np = s.players.map((p, i) => {
        if (i === targetIdx) return { ...p, res: { ...p.res, [stolen]: p.res[stolen] - 1 } };
        if (i === s.curPlayer) return { ...p, res: { ...p.res, [stolen]: (p.res[stolen] || 0) + 1 } };
        return p;
      });
      return addLog({ ...s, players: np, pendingRobberSteal: null }, `${P.name}が${target.name}から${RI[stolen]}を奪いました！`);
    });
    if (result) playSfx("steal");
  }

  async function handleSkipSteal() {
    await doAction(s => {
      if (!s.pendingRobberSteal) return null;
      return addLog({ ...s, pendingRobberSteal: null }, "略奪をスキップしました");
    });
  }

  async function handleRollDice() {
    if (!gs || gs.curPlayer !== myIndex || gs.diceRolled || diceRolling) return;
    playSfx("dice");
    const d1 = 1 + ((Math.random() * 6) | 0), d2 = 1 + ((Math.random() * 6) | 0), total = d1 + d2;
    setDiceRolling(true);
    let count = 0;
    diceTimer.current = setInterval(() => {
      setDiceDisplay([1 + ((Math.random() * 6) | 0), 1 + ((Math.random() * 6) | 0)]);
      count++;
      if (count >= 12) {
        clearInterval(diceTimer.current);
        setDiceDisplay([d1, d2]);
        setDiceRolling(false);
        doAction(s => {
          if (s.diceRolled) return null;
          const ns = addLog({ ...s, dice: [d1, d2], diceRolled: true }, `🎲 ${d1} + ${d2} = ${total}`);
          if (total === 7) {
            // 8枚以上持っているプレイヤーは半分捨てる
            const discardQueue = s.players.map((p, i) => {
              const tot = Object.values(p.res).reduce((a, b) => a + b, 0);
              return tot > 7 ? { idx: i, amount: Math.floor(tot / 2) } : null;
            }).filter(Boolean);
            if (discardQueue.length > 0) {
              return addLog({ ...ns, discardQueue }, "7！資源8枚以上のプレイヤーは半分捨ててください");
            }
            return addLog({ ...ns, robberMode: true }, "7！山賊を移動するヘックスを選んでください");
          }
          const { hexes, vertices, players } = s;
          const gains = Array.from({ length: players.length }, () => emptyRes());
          hexes.forEach(hex => {
            if (hex.number === total && !hex.hasRobber) {
              const res = TR[hex.terrain]; if (!res) return;
              hex.vertexIds.forEach(vid => { const b = vertices.find(v => v.id === vid)?.building; if (b) gains[b.player][res] += b.type === "city" ? 2 : 1; });
            }
          });
          const newPlayers = players.map((p, i) => ({ ...p, res: Object.fromEntries(Object.entries(p.res).map(([r, n]) => [r, n + gains[i][r]])) }));
          const msgs = gains.map((g, i) => { const items = Object.entries(g).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" "); return items ? `${players[i].name}: ${items}` : null; }).filter(Boolean);
          return addLog({ ...ns, players: newPlayers }, msgs.length ? msgs.join(" | ") : "誰にも資源なし");
        });
      }
    }, 80);
  }

  async function handleDiscard(sel) {
    const result = await doAction(s => {
      if (!s.discardQueue?.length || s.discardQueue[0].idx !== myIndex) return null;
      const needed = s.discardQueue[0].amount;
      const total = Object.values(sel).reduce((a, b) => a + b, 0);
      if (total !== needed) return null;
      const P = s.players[myIndex];
      for (const [r, n] of Object.entries(sel)) { if ((P.res[r] || 0) < n) return null; }
      const newRes = { ...P.res };
      for (const [r, n] of Object.entries(sel)) newRes[r] -= n;
      const np = s.players.map((p, i) => i !== myIndex ? p : { ...p, res: newRes });
      const newQueue = s.discardQueue.slice(1);
      let ns = addLog({ ...s, players: np, discardQueue: newQueue }, `${P.name}が${total}枚を捨てました`);
      if (newQueue.length === 0) {
        ns = addLog({ ...ns, robberMode: true }, `${s.players[s.curPlayer].name}が山賊を移動します`);
      }
      return ns;
    });
    if (result) playSfx("discard");
  }

  async function handleBuyDevCard() {
    if (!gs || gs.curPlayer !== myIndex || !gs.diceRolled) return;
    const result = await doAction(s => {
      const P = s.players[s.curPlayer];
      if (!canAfford(P, COSTS.devCard) || s.devDeck.length === 0) return null;
      const [card, ...rest] = s.devDeck;
      const np = s.players.map((p, i) => i !== s.curPlayer ? p : {
        ...p,
        res: Object.fromEntries(Object.entries(p.res).map(([r, n]) => [r, n - (COSTS.devCard[r] || 0)])),
        newDevCards: [...(p.newDevCards || []), card],
      });
      let ns = addLog({ ...s, players: np, devDeck: rest }, `${P.name}が発展カードを購入（残り${rest.length}枚）`);
      const totalVP = calcTotalVP(np[s.curPlayer], ns);
      if (totalVP >= 10) ns = { ...ns, winner: s.curPlayer, phase: "ended" };
      return ns;
    });
    if (result) playSfx("buy");
  }

  async function handlePlayDevCard(cardType) {
    if (!gs || gs.curPlayer !== myIndex || gs.phase !== 'main') return;
    if (cardType !== 'knight' && !gs.diceRolled) return; // 騎士のみサイコロ前OK
    if (gs.playedDevCardThisTurn) return;
    await doAction(s => {
      const P = s.players[s.curPlayer];
      if (!P.devCards.includes(cardType)) return null;
      const newDC = removeOne(P.devCards, cardType);
      switch (cardType) {
        case 'knight': {
          const np = s.players.map((p, i) => i !== s.curPlayer ? p : { ...p, devCards: newDC, knightsPlayed: (p.knightsPlayed || 0) + 1 });
          const ns = addLog({ ...s, players: np, robberMode: true, playedDevCardThisTurn: true }, `${P.name}が騎士カードを使用！`);
          return updateLargestArmy(ns);
        }
        case 'roadBuilding': {
          const np = s.players.map((p, i) => i !== s.curPlayer ? p : { ...p, devCards: newDC });
          return addLog({ ...s, players: np, pendingAction: { type: 'roadBuilding', roadsLeft: 2 }, playedDevCardThisTurn: true },
            `${P.name}が道路建設カードを使用！道を2本無料で建設できます`);
        }
        case 'yearOfPlenty': {
          const np = s.players.map((p, i) => i !== s.curPlayer ? p : { ...p, devCards: newDC });
          return addLog({ ...s, players: np, pendingAction: { type: 'yearOfPlenty' }, playedDevCardThisTurn: true },
            `${P.name}が年の実りカードを使用！2つの資源を選んでください`);
        }
        case 'monopoly': {
          const np = s.players.map((p, i) => i !== s.curPlayer ? p : { ...p, devCards: newDC });
          return addLog({ ...s, players: np, pendingAction: { type: 'monopoly' }, playedDevCardThisTurn: true },
            `${P.name}が独占カードを使用！独占する資源を選んでください`);
        }
        default: return null;
      }
    });
  }

  async function handleYearOfPlenty(res1, res2) {
    await doAction(s => {
      if (s.pendingAction?.type !== 'yearOfPlenty') return null;
      const P = s.players[s.curPlayer];
      const np = s.players.map((p, i) => i !== s.curPlayer ? p : {
        ...p, res: { ...p.res, [res1]: (p.res[res1] || 0) + 1, [res2]: (p.res[res2] || 0) + 1 }
      });
      let ns = addLog({ ...s, players: np, pendingAction: null }, `${P.name}が年の実り: ${RI[res1]} + ${RI[res2]}を獲得`);
      const totalVP = calcTotalVP(np[s.curPlayer], ns);
      if (totalVP >= 10) ns = { ...ns, winner: s.curPlayer, phase: "ended" };
      return ns;
    });
  }

  async function handleMonopoly(res) {
    await doAction(s => {
      if (s.pendingAction?.type !== 'monopoly') return null;
      const P = s.players[s.curPlayer];
      let total = 0;
      const np = s.players.map((p, i) => {
        if (i === s.curPlayer) return p;
        const n = p.res[res] || 0; total += n;
        return { ...p, res: { ...p.res, [res]: 0 } };
      });
      np[s.curPlayer] = { ...P, res: { ...P.res, [res]: (P.res[res] || 0) + total } };
      return addLog({ ...s, players: np, pendingAction: null }, `${P.name}が独占: ${RI[res]}×${total}枚獲得！`);
    });
  }

  async function handleBuildMode(mode) {
    if (!gs || gs.curPlayer !== myIndex) return;
    await doAction(s => ({ ...s, buildMode: s.buildMode === mode ? null : mode }));
  }

  async function handleEndTurn() {
    if (!gs || gs.curPlayer !== myIndex || !gs.diceRolled || gs.robberMode || gs.pendingAction || gs.pendingRobberSteal || (gs.discardQueue?.length || 0) > 0) return;
    await doAction(s => {
      if (!s.diceRolled || s.robberMode || s.pendingAction || s.pendingRobberSteal || (s.discardQueue?.length || 0) > 0) return null;
      const next = (s.curPlayer + 1) % s.players.length;
      // 今ターン購入したカードを使用可能に
      const np = s.players.map((p, i) => i !== s.curPlayer ? p : {
        ...p,
        devCards: [...(p.devCards || []), ...(p.newDevCards || [])],
        newDevCards: [],
      });
      return addLog({ ...s, curPlayer: next, diceRolled: false, dice: null, buildMode: null, pendingTrade: null, playedDevCardThisTurn: false, players: np },
        `${s.players[next].name}のターン`);
    });
  }

  // ── 交易 ──
  async function handleBankTrade(give, want) {
    if (!gs || gs.curPlayer !== myIndex) return;
    const result = await doAction(s => {
      const P = s.players[s.curPlayer];
      const rates = getPortRates(s.curPlayer, s.vertices);
      for (const [r, n] of Object.entries(give)) { if (n === 0) continue; if (n % rates[r] !== 0 || P.res[r] < n) return null; }
      let totalGiveUnits = 0;
      for (const [r, n] of Object.entries(give)) { if (n > 0) totalGiveUnits += n / rates[r]; }
      const totalWant = Object.values(want).reduce((a, b) => a + b, 0);
      if (Math.abs(totalGiveUnits - totalWant) > 0.001 || totalWant === 0) return null;
      const newRes = { ...P.res };
      const giveItems = [], wantItems = [];
      for (const [r, n] of Object.entries(give)) { if (n > 0) { newRes[r] -= n; giveItems.push(`${RI[r]}×${n}`); } }
      for (const [r, n] of Object.entries(want)) { if (n > 0) { newRes[r] = (newRes[r] || 0) + n; wantItems.push(`${RI[r]}×${n}`); } }
      if (Object.values(newRes).some(v => v < 0)) return null;
      const np = s.players.map((p, i) => i !== s.curPlayer ? p : { ...p, res: newRes });
      return addLog({ ...s, players: np }, `${P.name}が銀行と交易: ${giveItems.join(" ")} → ${wantItems.join(" ")}`);
    });
    if (result) playSfx("buy");
  }

  // 交渉の提案（通常提案・逆提案の両方）
  async function handleProposeTrade(give, want, target) {
    await doAction(s => {
      const me = s.players[myIndex]; if (!me) return null;
      const cur = s.pendingTrade;
      // すでに提案がある場合、それを差し替えられるのは受け手（＝逆提案）だけ
      const isCounter = cur && cur.from !== myIndex && (cur.to === null || cur.to === myIndex);
      if (cur && !isCounter) return null;
      // 新規提案は自分の手番＆サイコロ後のみ
      if (!cur && (s.curPlayer !== myIndex || !s.diceRolled || s.phase !== "main")) return null;
      if (!Object.values(give).some(n => n > 0) || !Object.values(want).some(n => n > 0)) return null;
      for (const [r, n] of Object.entries(give)) { if ((me.res[r] || 0) < n) return null; }
      const to = isCounter ? cur.from : (target === undefined ? null : target);
      const gStr = Object.entries(give).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" ");
      const wStr = Object.entries(want).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" ");
      const toName = to === null ? "全員" : s.players[to]?.name;
      const msg = isCounter
        ? `${me.name}が逆提案: ${gStr} → ${wStr}`
        : `${me.name}が${toName}に交易を提案: ${gStr} → ${wStr}`;
      return addLog({ ...s, pendingTrade: { from: myIndex, to, give: { ...give }, want: { ...want }, declined: [], counter: !!isCounter } }, msg);
    });
  }

  async function handleAcceptTrade() {
    if (!gs || !gs.pendingTrade || gs.pendingTrade.from === myIndex) return;
    const result = await doAction(s => {
      const pt = s.pendingTrade;
      if (!pt) return null;
      if (pt.to !== null && pt.to !== myIndex) return null;
      const { from, give, want } = pt;
      const fromP = s.players[from]; const toP = s.players[myIndex];
      for (const [r, n] of Object.entries(give)) { if ((fromP.res[r] || 0) < n) return null; }
      for (const [r, n] of Object.entries(want)) { if ((toP.res[r] || 0) < n) return null; }
      const newPlayers = s.players.map((p, i) => {
        if (i === from) { const nr = { ...p.res }; for (const [r, n] of Object.entries(give)) nr[r] -= n; for (const [r, n] of Object.entries(want)) nr[r] = (nr[r] || 0) + n; return { ...p, res: nr }; }
        if (i === myIndex) { const nr = { ...p.res }; for (const [r, n] of Object.entries(want)) nr[r] -= n; for (const [r, n] of Object.entries(give)) nr[r] = (nr[r] || 0) + n; return { ...p, res: nr }; }
        return p;
      });
      const gStr = Object.entries(give).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" ");
      const wStr = Object.entries(want).filter(([, n]) => n > 0).map(([r, n]) => `${RI[r]}×${n}`).join(" ");
      return addLog({ ...s, players: newPlayers, pendingTrade: null }, `🤝 ${s.players[myIndex].name}が交易を承諾: ${gStr} ⇄ ${wStr}`);
    });
    if (result) playSfx("buy");
  }

  async function handleDeclineTrade() {
    await doAction(s => {
      const pt = s.pendingTrade;
      if (!pt || pt.from === myIndex) return null;
      const myName = s.players[myIndex]?.name;
      // 個別指名の提案 → 断ったら即終了
      if (pt.to !== null) {
        if (pt.to !== myIndex) return null;
        return addLog({ ...s, pendingTrade: null }, `${myName}が交易を断りました`);
      }
      // 全員向け → 全員断ったら終了
      const declined = [...(pt.declined || []).filter(i => i !== myIndex), myIndex];
      const everyone = s.players.every((_, i) => i === pt.from || declined.includes(i));
      if (everyone) return addLog({ ...s, pendingTrade: null }, "全員が交易を断りました");
      return addLog({ ...s, pendingTrade: { ...pt, declined } }, `${myName}が交易を断りました`);
    });
  }

  async function handleCancelTrade() {
    await doAction(s => {
      if (!s.pendingTrade || s.pendingTrade.from !== myIndex) return null;
      return addLog({ ...s, pendingTrade: null }, `${s.players[s.pendingTrade.from].name}が交易提案を取り下げました`);
    });
  }

  // ── 画面分岐 ──
  if (screen === "home") {
    return <HomeScreen loading={loading} error={error} onCreate={handleCreate} onJoin={handleJoin} onQuickMatch={handleQuickMatch} />;
  }

  if (screen === "lobby" && gs) {
    return <LobbyScreen gs={gs} myIndex={myIndex} onSetTarget={handleSetTarget} onStart={handleStart} onLeave={handleLeave} />;
  }

  if (screen === "game" && gs) {
    return (
      <GameScreen
        gs={gs} myIndex={myIndex}
        diceDisplay={diceDisplay} diceRolling={diceRolling}
        sfxOn={sfxOn} bgmOn={bgmOn} onToggleSfx={handleToggleSfx} onToggleBgm={handleToggleBgm}
        actions={{
          rollDice: handleRollDice,
          buildMode: handleBuildMode,
          buyDevCard: handleBuyDevCard,
          playDevCard: handlePlayDevCard,
          endTurn: handleEndTurn,
          vertexClick: handleVertexClick,
          edgeClick: handleEdgeClick,
          hexClick: handleHexClick,
          steal: handleSteal,
          skipSteal: handleSkipSteal,
          discard: handleDiscard,
          yearOfPlenty: handleYearOfPlenty,
          monopoly: handleMonopoly,
          bankTrade: handleBankTrade,
          proposeTrade: handleProposeTrade,
          acceptTrade: handleAcceptTrade,
          declineTrade: handleDeclineTrade,
          cancelTrade: handleCancelTrade,
          leave: handleLeave,
        }}
      />
    );
  }

  return (
    <div style={{ ...screenWrap, display: "flex", alignItems: "center", justifyContent: "center" }}>
      読み込み中...
    </div>
  );
}
