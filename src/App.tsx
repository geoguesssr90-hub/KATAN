// @ts-nocheck

import { db, ref, set, get, onValue, off } from "./firebase";


import { useState, useEffect, useCallback, useRef } from "react";

const toArr = (x: any) => x && !Array.isArray(x) ? Object.values(x) : x ?? [];

function normalizeGS(data: any) {
  if (!data) return null;
  const toA = (x: any) => {
    if (!x) return [];
    if (Array.isArray(x)) return x;
    const arr = Object.entries(x)
      .sort(([a],[b]) => Number(a)-Number(b))
      .map(([,v]) => v);
    return arr;
  };
  const playersArr = toA(data.players).map((p: any) => ({
    ...p, res: p.res || {lumber:0,brick:0,wool:0,grain:0,ore:0}
  }));
  data.players = playersArr;
  data.hexes = toA(data.hexes).map((h: any) => ({...h, vertexIds: toA(h.vertexIds)}));
  data.vertices = toA(data.vertices).map((v: any) => ({...v, adjIds: toA(v.adjIds), hexIds: toA(v.hexIds)}));
  data.edges = toA(data.edges);
  data.log = toA(data.log);
  data.setupOrder = toA(data.setupOrder);
  data.dice = data.dice ? toA(data.dice) : null;
  if (data.players.length > 0 && (data.curPlayer === undefined || !data.players[data.curPlayer])) {
    data.curPlayer = 0;
  }
  return data;
}

// ─── Constants ──────────────────────────────────────────────────────────────
const SQ3 = Math.sqrt(3);
const HS = 44;
const BCX = 290, BCY = 290;
const SK = "catan3:";

const TC = { forest:"#1e5c1e", hills:"#a83c1a", pasture:"#5cb83e", fields:"#d4a83a", mountains:"#5a5a70", desert:"#c9a96e" };
const TI = { forest:"🌲", hills:"🧱", pasture:"🐑", fields:"🌾", mountains:"⛏️", desert:"🏜️" };
const TR = { forest:"lumber", hills:"brick", pasture:"wool", fields:"grain", mountains:"ore", desert:null };
const RI = { lumber:"🪵", brick:"🧱", wool:"🐑", grain:"🌾", ore:"⛏️" };
const PC = ["#ef4444","#3b82f6","#22c55e","#f97316"];
const COSTS = {
  road:{ lumber:1, brick:1 },
  settlement:{ lumber:1, brick:1, wool:1, grain:1 },
  city:{ grain:2, ore:3 },
};

// ─── Geometry ───────────────────────────────────────────────────────────────
const h2xy = (q,r) => ({ x: BCX+HS*1.5*q, y: BCY+HS*SQ3*(r+q*0.5) });
const hexCorners = (cx,cy) => Array.from({length:6},(_,i)=>({ x:cx+HS*Math.cos(Math.PI/3*i), y:cy+HS*Math.sin(Math.PI/3*i) }));
const vKey = (x,y) => `${Math.round(x/2)*2}_${Math.round(y/2)*2}`;

// ─── Board generation ───────────────────────────────────────────────────────
const shuf = a => { const b=[...a]; for(let i=b.length-1;i>0;i--){const j=(Math.random()*(i+1))|0;[b[i],b[j]]=[b[j],b[i]];} return b; };

function createBoard() {
  const coords = [];
  for(let q=-2;q<=2;q++) for(let r=Math.max(-2,-q-2);r<=Math.min(2,-q+2);r++) coords.push({q,r});
  const terrains = shuf(["forest","forest","forest","forest","pasture","pasture","pasture","pasture","fields","fields","fields","fields","hills","hills","hills","mountains","mountains","mountains","desert"]);
  const nums = shuf([2,3,3,4,4,5,5,6,6,8,8,9,9,10,10,11,11,12]);
  let ni=0;
  const hexes = coords.map((c,i) => {
    const {x,y}=h2xy(c.q,c.r); const t=terrains[i];
    return {id:i,q:c.q,r:c.r,cx:x,cy:y,terrain:t,number:t==="desert"?null:nums[ni++],hasRobber:t==="desert",vertexIds:[]};
  });
  const vMap=new Map();
  hexes.forEach(hex=>{
    const cs=hexCorners(hex.cx,hex.cy);
    cs.forEach(c=>{ const k=vKey(c.x,c.y); if(!vMap.has(k)) vMap.set(k,{x:c.x,y:c.y,hexIds:[],adjKeys:new Set(),building:null}); vMap.get(k).hexIds.push(hex.id); });
    for(let i=0;i<6;i++){const k1=vKey(cs[i].x,cs[i].y),k2=vKey(cs[(i+1)%6].x,cs[(i+1)%6].y);vMap.get(k1).adjKeys.add(k2);vMap.get(k2).adjKeys.add(k1);}
  });
  const keyToId={},vertices=[];let vid=0;
  vMap.forEach((v,k)=>{v.id=vid;keyToId[k]=vid++;vertices.push(v);});
  vertices.forEach(v=>{v.adjIds=[...v.adjKeys].map(k=>keyToId[k]);delete v.adjKeys;});
  const eSet=new Set(),edges=[];
  vertices.forEach(v=>{ v.adjIds.forEach(aid=>{ const ek=[v.id,aid].sort((a,b)=>a-b).join("-"); if(!eSet.has(ek)){eSet.add(ek);edges.push({id:edges.length,v1:v.id,v2:aid,road:null});}});});
  hexes.forEach(hex=>{ const cs=hexCorners(hex.cx,hex.cy); hex.vertexIds=cs.map(c=>keyToId[vKey(c.x,c.y)]); });
  return {hexes,vertices,edges};
}

// ─── Game helpers ────────────────────────────────────────────────────────────
const canAfford = (p,cost) => Object.entries(cost).every(([r,n])=>p.res[r]>=n);
const canPlaceSett = (vid,verts) => { const v=verts[vid]; if(!v||v.building) return false; return v.adjIds.every(aid=>!verts[aid]?.building); };
const isConnRoad = (vid,edges,pid) => edges.some(e=>(e.v1===vid||e.v2===vid)&&e.road===pid);
const genCode = () => { const c="ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; return Array.from({length:4},()=>c[(Math.random()*c.length)|0]).join(""); };
const addLog = (s,msg) => ({...s, log:[msg,...(s.log||[]).slice(0,29)]});
const initPlayer = (id,name) => ({id,name,color:PC[id],res:{lumber:0,brick:0,wool:0,grain:0,ore:0},vp:0,settlementsLeft:5,citiesLeft:4,roadsLeft:15});

function createInitialState(code, hostName) {
  const board = createBoard();
  return {
    code, phase:"lobby", numPlayersTarget:3,
    players:[initPlayer(0,hostName)],
    hexes:board.hexes, vertices:board.vertices, edges:board.edges,
    curPlayer:0, setupStep:0, setupSub:"settlement", setupOrder:[],
    dice:null, diceRolled:false, robberMode:false, buildMode:null, lastVid:null,
    log:[`${hostName}がゲームを作成しました`], winner:null, updatedAt:Date.now(),
  };
}

// ─── Styles ──────────────────────────────────────────────────────────────────
const BG = "linear-gradient(135deg,#080d05 0%,#0a1208 100%)";
const panelStyle = { background:"#0f1a0b", border:"1px solid #283820", borderRadius:"10px", padding:"10px 12px" };
const btnStyle = (disabled,active) => ({
  padding:"7px 10px", background:active?"#243d18":disabled?"#060d04":"#0f1a0b",
  color:disabled?"#303d28":"#d0c080", border:`1px solid ${active?"#4a7a2a":disabled?"#182210":"#283820"}`,
  borderRadius:"6px", cursor:disabled?"not-allowed":"pointer", fontSize:"12px",
  textAlign:"left", transition:"all 0.15s", width:"100%",
});
const inputStyle = { display:"block",width:"100%",padding:"9px 12px",background:"#060d04",border:"1px solid #283820",borderRadius:"8px",color:"#f0dda0",fontSize:"14px",boxSizing:"border-box",outline:"none",marginBottom:"12px" };

// ─── Main Component ──────────────────────────────────────────────────────────
export default function CatanOnline() {
  const [screen, setScreen] = useState("home");
  const [myIndex, setMyIndex] = useState(null);
  const [gs, setGs] = useState(null);
  const [inputName, setInputName] = useState("");
  const [inputCode, setInputCode] = useState("");
  const [error, setError] = useState("");
  const [hovV, setHovV] = useState(null);
  const [hovE, setHovE] = useState(null);
  const [copied, setCopied] = useState(false);
  const [loading, setLoading] = useState(false);
  const pollRef = useRef(null);
  const myIndexRef = useRef(null);
  myIndexRef.current = myIndex;

// ── Storage ──

const loadGame = async (code: string) => {
  try {
    const snap = await get(ref(db, "games/" + code));
    if (!snap.exists()) return null;
    return normalizeGS(snap.val());
  } catch { return null; }
};
const saveGame = async (state: any) => {
  try {
    await set(ref(db, "games/" + state.code), state);
  } catch(e) { console.error(e); }
};

const loadMyInfo = async () => {
  try {
    const r = localStorage.getItem("catan:me");
    return r ? JSON.parse(r) : null;
  } catch { return null; }
};

const saveMyInfo = async (info: any) => {
  try {
    localStorage.setItem("catan:me", JSON.stringify(info));
  } catch {}
};

  // ── Polling ──
const startPolling = useCallback((code: string) => {
  if (pollRef.current) off(pollRef.current);
  const gameRef = ref(db, "games/" + code);
  onValue(gameRef, (snap) => {
    if (snap.exists()) {
      const s = normalizeGS(snap.val());
      if (!s) return;
      setGs(s);
      if (s.phase === "main" || s.phase === "setup" || s.phase === "ended") setScreen("game");
      else if (s.phase === "lobby") setScreen("lobby");
    }
  });
  pollRef.current = gameRef as any;
}, []);

  useEffect(()=>{
    (async()=>{
      const info=await loadMyInfo();
      if(info){
        const s=await loadGame(info.code);
        if(s){
          setMyIndex(info.index); setGs(s);
          setScreen(s.phase==="lobby"?"lobby":"game");
          startPolling(info.code);
        }
      }
    })();
    return () => {
    if (pollRef.current) off(pollRef.current);
    };
  },[]);

  // ── Actions ──
  async function handleCreate() {
    setLoading(true); setError("");
    const name=inputName.trim()||"ホスト";
    const code=genCode();
    const state=createInitialState(code,name);
    await saveGame(state);
    await saveMyInfo({code,index:0});
    setMyIndex(0); setGs(state); setScreen("lobby");
    startPolling(code); setLoading(false);
  }

  async function handleJoin() {
    setLoading(true); setError("");
    const code=inputCode.trim().toUpperCase();
    if(!code){setError("ゲームコードを入力してください");setLoading(false);return;}
    const state=await loadGame(code);
    if(!state){setError("ゲームが見つかりません");setLoading(false);return;}
    if(state.phase!=="lobby"){setError("ゲームはすでに開始しています");setLoading(false);return;}
    if(state.players.length>=state.numPlayersTarget){setError("満員です");setLoading(false);return;}
    const name=inputName.trim()||`プレイヤー${state.players.length+1}`;
    const idx=state.players.length;
    const ns=addLog({...state,players:[...state.players,initPlayer(idx,name)],updatedAt:Date.now()},`${name}が参加しました`);
    await saveGame(ns);
    await saveMyInfo({code,index:idx});
    setMyIndex(idx); setGs(ns); setScreen("lobby");
    startPolling(code); setLoading(false);
  }

  async function handleSetTarget(n) {
    const s=await loadGame(gs.code); if(!s) return;
    const ns={...s,numPlayersTarget:n,updatedAt:Date.now()};
    await saveGame(ns); setGs(ns);
  }

  async function handleStart() {
    const s=await loadGame(gs.code); if(!s) return;
    if(s.players.length<2) return;
    const n=s.players.length;
    const f=Array.from({length:n},(_,i)=>i);
    const setupOrder=[...f,...[...f].reverse()];
    const ns=addLog({...s,phase:"setup",setupOrder,curPlayer:setupOrder[0],setupStep:0,setupSub:"settlement",updatedAt:Date.now()},
      "ゲーム開始！セットアップフェーズ — "+s.players[setupOrder[0]].name+"が最初に定住地を置いてください");
    await saveGame(ns); setGs(ns); setScreen("game");
  }

  // Generic action: load fresh state, apply mutation, save
  async function doAction(fn) {
    const s=await loadGame(gs.code);
    console.log("doAction s:", s);
    if(!s) { console.log("doAction: loadGame returned null"); return; }
    const ns=fn(s);
    console.log("doAction ns:", ns);
    if(ns){ns.updatedAt=Date.now();await saveGame(ns);setGs(ns);}
  }

async function handleVertexClick(vid) {
    if(!gs||gs.curPlayer!==myIndex) return;
    await doAction(s=>{
      const {phase,setupSub,vertices,edges,players,curPlayer,setupStep,setupOrder}=s;
      const P=players[curPlayer];
      if(phase==="setup"&&setupSub==="settlement"){
        if(!canPlaceSett(vid,vertices)) return null;
        const isR2=setupStep>=players.length;
        const nv=vertices.map(v=>v.id===vid?{...v,building:{player:curPlayer,type:"settlement"}}:v);
        let np=players.map((p,i)=>i!==curPlayer?p:{...p,vp:p.vp+1,settlementsLeft:p.settlementsLeft-1});
        let extra="";
        if(isR2){
          const rg={lumber:0,brick:0,wool:0,grain:0,ore:0};
          const vert=vertices.find(v=>v.id===vid);
          vert?.hexIds.forEach(hid=>{const r=TR[s.hexes.find(h=>h.id===hid)?.terrain];if(r)rg[r]++;});
          np=np.map((p,i)=>i!==curPlayer?p:{...p,res:Object.fromEntries(Object.entries(p.res).map(([r,n])=>[r,n+(rg[r]||0)]))});
          const items=Object.entries(rg).filter(([,n])=>n>0).map(([r,n])=>`${RI[r]}×${n}`).join(" ");
          if(items) extra=`（${items}獲得）`;
        }
        return addLog({...s,vertices:nv,players:np,setupSub:"road",lastVid:vid},`${P.name}が定住地を配置${extra}。次に道を置いてください`);
      }
      if(phase==="main"&&s.diceRolled&&s.buildMode==="settlement"){
        if(!canPlaceSett(vid,vertices)||!isConnRoad(vid,edges,curPlayer)||!canAfford(P,COSTS.settlement)) return null;
        const nv=vertices.map(v=>v.id===vid?{...v,building:{player:curPlayer,type:"settlement"}}:v);
        const np=players.map((p,i)=>i!==curPlayer?p:{...p,vp:p.vp+1,settlementsLeft:p.settlementsLeft-1,res:Object.fromEntries(Object.entries(p.res).map(([r,n])=>[r,n-(COSTS.settlement[r]||0)]))});
        const newVP=np[curPlayer].vp;
        let ns=addLog({...s,vertices:nv,players:np,buildMode:null},`${P.name}が定住地を建設！（${newVP}VP）`);
        if(newVP>=10) ns={...ns,winner:curPlayer,phase:"ended"};
        return ns;
      }
      if(phase==="main"&&s.diceRolled&&s.buildMode==="city"){
        const v=vertices.find(v=>v.id===vid);
        if(!v?.building||v.building.player!==curPlayer||v.building.type!=="settlement"||!canAfford(P,COSTS.city)) return null;
        const nv=vertices.map(v=>v.id===vid?{...v,building:{player:curPlayer,type:"city"}}:v);
        const np=players.map((p,i)=>i!==curPlayer?p:{...p,vp:p.vp+1,citiesLeft:p.citiesLeft-1,settlementsLeft:p.settlementsLeft+1,res:Object.fromEntries(Object.entries(p.res).map(([r,n])=>[r,n-(COSTS.city[r]||0)]))});
        const newVP=np[curPlayer].vp;
        let ns=addLog({...s,vertices:nv,players:np,buildMode:null},`${P.name}が都市を建設！（${newVP}VP）`);
        if(newVP>=10) ns={...ns,winner:curPlayer,phase:"ended"};
        return ns;
      }
      return null;
    });
  }

  async function handleEdgeClick(eid) {
    if(!gs||gs.curPlayer!==myIndex) return;
    await doAction(s=>{
      const {phase,setupSub,vertices,edges,players,curPlayer,setupStep,setupOrder}=s;
      const edge=edges.find(e=>Number(e.id)===Number(eid));
      console.log("found edge:", edge, "lastVid:", s.lastVid);
      if(!edge||edge.road!=null) { console.log("blocked"); return null; }
      if(phase==="setup"&&setupSub==="road"){
        console.log("v1:", edge.v1, "v2:", edge.v2, "lastVid:", s.lastVid);
        if(Number(edge.v1)!==Number(s.lastVid)&&Number(edge.v2)!==Number(s.lastVid)) { console.log("lastVid mismatch"); return null; }
        const ne=edges.map(e=>e.id===eid?{...e,road:curPlayer}:e);
        const np=players.map((p,i)=>i!==curPlayer?p:{...p,roadsLeft:p.roadsLeft-1});
        const next=setupStep+1; const done=next>=setupOrder.length;
        let ns={...s,edges:ne,players:np,setupStep:next,setupSub:"settlement",buildMode:null,lastVid:null};
        if(done){
          ns=addLog({...ns,phase:"main",curPlayer:0,diceRolled:false,dice:null},"セットアップ完了！"+players[0].name+"のターン");
        } else {
          const ncp=setupOrder[next];
          ns=addLog({...ns,curPlayer:ncp},`${players[ncp].name}が定住地を置いてください`);
        }
        return ns;
      }
      // Main: build road
      if(phase==="main"&&s.buildMode==="road"&&s.diceRolled&&canAfford(P,COSTS.road)){
        const connected=vertices[edge.v1]?.building?.player===curPlayer||vertices[edge.v2]?.building?.player===curPlayer||isConnRoad(edge.v1,edges,curPlayer)||isConnRoad(edge.v2,edges,curPlayer);
        if(!connected) return null;
        const ne=edges.map(e=>e.id===eid?{...e,road:curPlayer}:e);
        const np=players.map((p,i)=>i!==curPlayer?p:{...p,roadsLeft:p.roadsLeft-1,res:Object.fromEntries(Object.entries(p.res).map(([r,n])=>[r,n-(COSTS.road[r]||0)]))});
        return addLog({...s,edges:ne,players:np,buildMode:null},`${P.name}が道を建設！`);
      }
      return null;
    });
  }
  async function handleHexClick(hid) {
    if(!gs||gs.curPlayer!==myIndex||!gs.robberMode) return;
    await doAction(s=>{
      if(!s.robberMode||s.hexes[hid].hasRobber) return null;
      const nh=s.hexes.map(h=>({...h,hasRobber:h.id===hid}));
      return addLog({...s,hexes:nh,robberMode:false},"山賊を移動しました");
    });
  }

  async function handleRollDice() {
    if(!gs||gs.curPlayer!==myIndex||gs.diceRolled) return;
    const d1=1+((Math.random()*6)|0), d2=1+((Math.random()*6)|0), total=d1+d2;
    await doAction(s=>{
      if(s.diceRolled) return null;
      let ns=addLog({...s,dice:[d1,d2],diceRolled:true},`🎲 ${d1} + ${d2} = ${total}`);
      if(total===7) return addLog({...ns,robberMode:true},"7！山賊を移動するヘックスを選んでください");
      const {hexes,vertices,players}=s;
      const gains=Array.from({length:players.length},()=>({lumber:0,brick:0,wool:0,grain:0,ore:0}));
      hexes.forEach(hex=>{
        if(hex.number===total&&!hex.hasRobber){
          const res=TR[hex.terrain]; if(!res) return;
          hex.vertexIds.forEach(vid=>{ const b=vertices[vid]?.building; if(b) gains[b.player][res]+=b.type==="city"?2:1; });
        }
      });
      const newPlayers=players.map((p,i)=>({...p,res:Object.fromEntries(Object.entries(p.res).map(([r,n])=>[r,n+gains[i][r]]))}));
      const msgs=gains.map((g,i)=>{const items=Object.entries(g).filter(([,n])=>n>0).map(([r,n])=>`${RI[r]}×${n}`).join(" ");return items?`${players[i].name}: ${items}`:null;}).filter(Boolean);
      return addLog({...ns,players:newPlayers},msgs.length?msgs.join(" | "):"誰にも資源なし");
    });
  }

  async function handleBuildMode(mode) {
    if(!gs||gs.curPlayer!==myIndex) return;
    await doAction(s=>({...s,buildMode:s.buildMode===mode?null:mode}));
  }

  async function handleEndTurn() {
    if(!gs||gs.curPlayer!==myIndex||!gs.diceRolled||gs.robberMode) return;
    await doAction(s=>{
      if(!s.diceRolled||s.robberMode) return null;
      const next=(s.curPlayer+1)%s.players.length;
      return addLog({...s,curPlayer:next,diceRolled:false,dice:null,buildMode:null},`${s.players[next].name}のターン`);
    });
  }

  function handleCopy() {
    if(!gs) return;
    navigator.clipboard.writeText(gs.code).catch(()=>{});
    setCopied(true); setTimeout(()=>setCopied(false),2000);
  }


  async function handleLeave() {
    if(pollRef.current) off(pollRef.current);
    localStorage.removeItem("catan:me");
    setScreen("home");
    setGs(null);
    setMyIndex(null);
  }

  // ─── Screen: Home ─────────────────────────────────────────────────────────
  if(screen==="home") return (
    <div style={{minHeight:"100vh",background:BG,display:"flex",alignItems:"center",justifyContent:"center",fontFamily:'"Noto Serif JP",Georgia,serif',color:"#f0dda0"}}>
      <div style={{background:"#0f1a0b",border:"1px solid #2a3a1a",borderRadius:"16px",padding:"36px 30px",width:"340px",maxWidth:"93vw"}}>
        <h1 style={{margin:"0 0 2px",textAlign:"center",color:"#c09030",letterSpacing:"5px",fontSize:"26px"}}>⚓ カタン</h1>
        <p style={{textAlign:"center",color:"#3a5028",fontSize:"11px",margin:"0 0 22px",letterSpacing:"3px"}}>ONLINE MULTIPLAYER</p>

        <label style={{fontSize:"11px",color:"#5a7040",display:"block",marginBottom:"4px"}}>プレイヤー名（省略可）</label>
        <input value={inputName} onChange={e=>setInputName(e.target.value)} placeholder="名前を入力" style={inputStyle} onKeyDown={e=>e.key==="Enter"&&handleCreate()}/>

        <button onClick={handleCreate} disabled={loading}
          style={{display:"block",width:"100%",padding:"11px",background:"#c09030",color:"#0f0a04",border:"none",borderRadius:"8px",fontSize:"15px",fontWeight:"bold",cursor:"pointer",marginBottom:"14px"}}>
          🏝️ ゲームを作成
        </button>

        <div style={{display:"flex",alignItems:"center",gap:"8px",marginBottom:"14px"}}>
          <div style={{flex:1,height:"1px",background:"#1e2a14"}}/>
          <span style={{fontSize:"11px",color:"#384828"}}>または</span>
          <div style={{flex:1,height:"1px",background:"#1e2a14"}}/>
        </div>

        <label style={{fontSize:"11px",color:"#5a7040",display:"block",marginBottom:"4px"}}>ゲームコード</label>
        <input value={inputCode} onChange={e=>setInputCode(e.target.value.toUpperCase())} placeholder="XXXX" maxLength={4}
          style={{...inputStyle,fontSize:"20px",letterSpacing:"6px",textAlign:"center"}}
          onKeyDown={e=>e.key==="Enter"&&handleJoin()}/>
        <button onClick={handleJoin} disabled={loading}
          style={{display:"block",width:"100%",padding:"11px",background:"#142a1a",color:"#4ab83a",border:"1px solid #2a6a2a",borderRadius:"8px",fontSize:"15px",fontWeight:"bold",cursor:"pointer"}}>
          🚢 ゲームに参加
        </button>

        {error&&<div style={{marginTop:"10px",padding:"8px 12px",background:"#2a0808",border:"1px solid #6a2020",borderRadius:"6px",color:"#ff8888",fontSize:"12px"}}>{error}</div>}
        <div style={{marginTop:"16px",padding:"10px",background:"#080e06",border:"1px solid #1a2412",borderRadius:"8px",fontSize:"11px",color:"#3a4a28",lineHeight:"1.6"}}>
          💡 <strong style={{color:"#5a7040"}}>遊び方：</strong>ゲームを作成してコードを友達に共有。3〜4人が揃ったらホストがゲームを開始できます。
        </div>
      </div>
    </div>
  );

  // ─── Screen: Lobby ────────────────────────────────────────────────────────
  if(screen==="lobby"&&gs) {
    const isHost=myIndex===0;
    const canStart=gs.players.length>=2&&gs.players.length<=4;
    return (
      <div style={{minHeight:"100vh",background:BG,display:"flex",alignItems:"center",justifyContent:"center",fontFamily:'"Noto Serif JP",Georgia,serif',color:"#f0dda0",padding:"16px"}}>
        <div style={{background:"#0f1a0b",border:"1px solid #2a3a1a",borderRadius:"16px",padding:"28px",width:"420px",maxWidth:"95vw"}}>
          <h2 style={{margin:"0 0 4px",color:"#c09030",letterSpacing:"3px",fontSize:"20px",textAlign:"center"}}>ゲームロビー</h2>

          {/* Game code */}
          <div style={{textAlign:"center",marginBottom:"20px",marginTop:"10px"}}>
            <div style={{fontSize:"11px",color:"#5a7040",marginBottom:"6px"}}>友達にこのコードを共有してください</div>
            <div style={{display:"inline-flex",alignItems:"center",gap:"10px",background:"#060d04",border:"1px solid #2a4a1a",borderRadius:"10px",padding:"10px 20px"}}>
              <span style={{fontSize:"28px",fontWeight:"bold",color:"#c09030",letterSpacing:"8px"}}>{gs.code}</span>
              <button onClick={handleCopy} title="コピー" style={{background:"none",border:"none",cursor:"pointer",color:copied?"#4ab83a":"#6a8050",fontSize:"18px",padding:"0",transition:"color 0.2s"}}>
                {copied?"✓":"copy"}
              </button>
            </div>
          </div>

          {/* Player count selector (host only) */}
          {isHost&&(
            <div style={{marginBottom:"16px"}}>
              <div style={{fontSize:"11px",color:"#5a7040",marginBottom:"6px"}}>目標プレイヤー数</div>
              <div style={{display:"flex",gap:"8px"}}>
                {[3,4].map(n=>(
                  <button key={n} onClick={()=>handleSetTarget(n)}
                    style={{flex:1,padding:"8px",background:gs.numPlayersTarget===n?"#1e3a10":"#060d04",color:gs.numPlayersTarget===n?"#4ab83a":"#5a7040",border:`1px solid ${gs.numPlayersTarget===n?"#3a7020":"#1e2a14"}`,borderRadius:"6px",cursor:"pointer",fontSize:"15px",fontWeight:"bold"}}>
                    {n}人
                  </button>
                ))}
              </div>
            </div>
          )}

          {/* Players list */}
          <div style={{marginBottom:"18px"}}>
            <div style={{fontSize:"11px",color:"#5a7040",marginBottom:"8px"}}>参加プレイヤー（{gs.players.length}/{gs.numPlayersTarget}）</div>
            {gs.players.map(p=>(
              <div key={p.id} style={{display:"flex",alignItems:"center",gap:"10px",padding:"9px 12px",marginBottom:"4px",background:"#080e06",border:`1px solid ${p.id===myIndex?"#2a4a1a":"#162010"}`,borderRadius:"8px"}}>
                <div style={{width:"12px",height:"12px",borderRadius:"50%",background:PC[p.id],boxShadow:`0 0 6px ${PC[p.id]}66`,flexShrink:0}}/>
                <span style={{color:p.id===myIndex?"#d0c080":"#7a9068",fontSize:"14px",flex:1}}>{p.name}</span>
                {p.id===0&&<span style={{fontSize:"11px",color:"#4a6030",background:"#0f1a0b",border:"1px solid #1e2a14",borderRadius:"4px",padding:"1px 6px"}}>ホスト</span>}
                {p.id===myIndex&&p.id!==0&&<span style={{fontSize:"11px",color:"#4ab83a"}}>あなた</span>}
              </div>
            ))}
            {Array.from({length:Math.max(0,gs.numPlayersTarget-gs.players.length)},(_,i)=>(
              <div key={i} style={{padding:"9px 12px",marginBottom:"4px",background:"#060d04",border:"1px dashed #162010",borderRadius:"8px",color:"#2a3820",fontSize:"13px",display:"flex",alignItems:"center",gap:"8px"}}>
                <div style={{width:"12px",height:"12px",borderRadius:"50%",background:"#1a2414",border:"1px dashed #2a3820",flexShrink:0}}/>
                <span>待機中...</span>
              </div>
            ))}
          </div>

          {/* Start / waiting */}
          {isHost?(
            <button onClick={handleStart} disabled={!canStart}
              style={{display:"block",width:"100%",padding:"12px",background:canStart?"#c09030":"#0f1208",color:canStart?"#0a0804":"#2a3020",border:"none",borderRadius:"8px",fontSize:"15px",fontWeight:"bold",cursor:canStart?"pointer":"not-allowed",transition:"all 0.2s"}}>
              {gs.players.length<2?`あと${2-gs.players.length}人必要...`:`ゲーム開始（${gs.players.length}人）`}
            </button>
          ):(
            <div style={{textAlign:"center",padding:"12px",background:"#060d04",border:"1px solid #162010",borderRadius:"8px",color:"#5a7040",fontSize:"13px"}}>
              ホストがゲームを開始するのを待っています...
            </div>
          )}
          <div style={{textAlign:"center",marginTop:"10px"}}>
            <button onClick={()=>{if(pollRef.current)clearInterval(pollRef.current);setScreen("home");setGs(null);setMyIndex(null);}} style={{background:"none",border:"none",color:"#384828",fontSize:"11px",cursor:"pointer",textDecoration:"underline"}}>
              ← ホームへ戻る
            </button>
          </div>
        </div>
      </div>
    );
  }

  // ─── Screen: Game ─────────────────────────────────────────────────────────
    if(screen==="game"&&gs) {
      console.log("gs.curPlayer:", gs.curPlayer);
      console.log("gs.players:", gs.players);
      if(!gs.players || gs.players.length === 0 || gs.players[gs.curPlayer] === undefined) return (
      <div style={{minHeight:"100vh",background:BG,display:"flex",alignItems:"center",justifyContent:"center",color:"#f0dda0",fontFamily:"Georgia,serif"}}>
        読み込み中...
      </div>
    );
    const P=gs.players[gs.curPlayer];
    const myP=myIndex!==null?gs.players[myIndex]:null;
    const isMyTurn=gs.curPlayer===myIndex;
    const phase=gs.phase;
    const isSetupSett=phase==="setup"&&gs.setupSub==="settlement";
    const isSetupRoad=phase==="setup"&&gs.setupSub==="road";

  const statusMsg=
    gs.winner!=null&&gs.players[gs.winner]?`🏆 ${gs.players[gs.winner].name}が勝利！`:
    gs.robberMode?(isMyTurn?" 山賊を移動するヘックスを選択":`${P.name}が山賊を移動中...`):
    phase==="setup"?(isMyTurn?`セットアップ: ${gs.setupSub==="settlement"?"定住地を置いてください":"道を置いてください"}`:`${P.name}がセットアップ中...`):
    !isMyTurn?`${P.name}のターンを待っています`:
    !gs.diceRolled?" サイコロを振ってください":
    gs.buildMode?`配置: ${gs.buildMode==="road"?"道":gs.buildMode==="settlement"?" 定住地":"都市"}を選択`:
    "アクションを選択";

    const diceStr=gs.dice?`${gs.dice[0]}＋${gs.dice[1]}＝${gs.dice[0]+gs.dice[1]}`:"－";

    return (
      <div style={{minHeight:"100vh",background:BG,fontFamily:'"Noto Serif JP",Georgia,serif',color:"#f0dda0",display:"flex",flexDirection:"column",alignItems:"center",padding:"8px",gap:"8px"}}>

        {/* Header */}
        <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",width:"100%",maxWidth:"980px",padding:"0 4px"}}>
          <h1 style={{margin:0,fontSize:"18px",color:"#c09030",letterSpacing:"3px"}}>⚓ カタン</h1>
          <div style={{display:"flex",alignItems:"center",gap:"8px",flexWrap:"wrap",justifyContent:"flex-end"}}>
            <span style={{fontSize:"11px",color:"#3a5028"}}>コード: <b style={{color:"#c09030"}}>{gs.code}</b></span>
            <div style={{padding:"3px 10px",background:isMyTurn?"#142a10":"#080e06",border:`1px solid ${isMyTurn?"#2a6020":"#162010"}`,borderRadius:"20px",fontSize:"11px",color:isMyTurn?"#4ab83a":"#5a7040"}}>
              {isMyTurn?"✦ あなたのターン":`${P.name}のターン`}
            </div>
            <button onClick={handleLeave} style={{background:"none",border:"none",      color:"#384828",  fontSize:"11px",cursor:"pointer",textDecoration:"underline"}}>
            ← 退室する
            </button>
          </div>
        </div>

        {/* Winner overlay */}
        {gs.winner!==null&&gs.players[gs.winner]&&(
          <div style={{position:"fixed",inset:0,background:"#000d",display:"flex",alignItems:"center",justifyContent:"center",zIndex:200}}>
            <div style={{background:"linear-gradient(135deg,#140f04,#1e1808)",border:"2px solid #c09030",borderRadius:"16px",padding:"32px 40px",textAlign:"center",boxShadow:"0 0 60px #c0903033"}}>
              <div style={{fontSize:"60px",marginBottom:"10px"}}>🏆</div>
              <div style={{color:PC[gs.winner],fontSize:"26px",fontWeight:"bold",marginBottom:"4px"}}>{gs.players[gs.winner].name}</div>
              <div style={{color:"#c09030",fontSize:"18px",marginBottom:"20px"}}>勝利！！</div>
              <button onClick={()=>{if(pollRef.current)clearInterval(pollRef.current);setScreen("home");setGs(null);setMyIndex(null);}}
                style={{padding:"10px 28px",background:"#c09030",color:"#0a0804",border:"none",borderRadius:"8px",fontSize:"15px",cursor:"pointer",fontWeight:"bold"}}>
                ホームへ戻る
              </button>
            </div>
          </div>
        )}

        <div style={{display:"flex",gap:"10px",flexWrap:"wrap",justifyContent:"center",width:"100%",maxWidth:"980px"}}>

          {/* Board SVG */}
          <div style={{flexShrink:0}}>
            <svg width={580} height={580} style={{borderRadius:"50%",display:"block",filter:"drop-shadow(0 0 24px #00000099)"}}>
              <circle cx={290} cy={290} r={288} fill="#163a5a"/>
              <circle cx={290} cy={290} r={274} fill="#1c4870" stroke="#245880" strokeWidth="1"/>
              {/* hexes */}
              {gs.hexes.map(hex=>{
                const cs=hexCorners(hex.cx,hex.cy);
                const pts=cs.map(c=>`${c.x},${c.y}`).join(" ");
                const robTarget=gs.robberMode&&isMyTurn&&!hex.hasRobber;
                return(
                  <g key={hex.id} onClick={()=>handleHexClick(hex.id)} style={{cursor:robTarget?"pointer":"default"}}>
                    <polygon points={pts} fill={TC[hex.terrain]} stroke="#080e05" strokeWidth="1.5" opacity={gs.robberMode&&!robTarget?0.55:1}/>
                    {robTarget&&<polygon points={pts} fill="white" opacity={0.1}/>}
                    <text x={hex.cx} y={hex.cy-13} textAnchor="middle" fontSize="17">{TI[hex.terrain]}</text>
                    {hex.hasRobber&&<text x={hex.cx} y={hex.cy+10} textAnchor="middle" fontSize="20">🏴</text>}
                    {hex.number&&!hex.hasRobber&&(
                      <>
                        <circle cx={hex.cx} cy={hex.cy+8} r={14} fill={hex.number===6||hex.number===8?"#7a1010":"#f0e4c0"} stroke="#080e05" strokeWidth="1.5"/>
                        <text x={hex.cx} y={hex.cy+13} textAnchor="middle" fontSize="12" fontWeight="bold" fill={hex.number===6||hex.number===8?"#ffdc90":"#100a04"}>{hex.number}</text>
                      </>
                    )}
                  </g>
                );
              })}
              {/* edges */}
              {gs.edges.map(edge=>{
                const v1=gs.vertices[edge.v1],v2=gs.vertices[edge.v2];
                if(!v1||!v2) return null;
                const canP=isMyTurn&&(isSetupRoad||(gs.phase==="main"&&gs.buildMode==="road"));
                const isHov=hovE===edge.id&&canP&&edge.road===null;
                return(
                  <g key={edge.id} onClick={()=>handleEdgeClick(edge.id)} onMouseEnter={()=>setHovE(edge.id)} onMouseLeave={()=>setHovE(null)} style={{cursor:canP?"pointer":"default"}}>
                    <line x1={v1.x} y1={v1.y} x2={v2.x} y2={v2.y} stroke={edge.road!==null?PC[edge.road]:isHov?"#ffffffaa":"transparent"} strokeWidth={edge.road!==null?5:3} strokeLinecap="round"/>
                    <line x1={v1.x} y1={v1.y} x2={v2.x} y2={v2.y} stroke="transparent" strokeWidth="14"/>
                  </g>
                );
              })}
              {/* vertices */}
              {gs.vertices.map(v=>{
                const b=v.building;
                const canSett=isMyTurn&&(isSetupSett||gs.buildMode==="settlement")&&canPlaceSett(v.id,gs.vertices)&&(isSetupSett||isConnRoad(v.id,gs.edges,myIndex));
                const canCity=isMyTurn&&gs.buildMode==="city"&&b?.player===myIndex&&b?.type==="settlement";
                const highlight=(canSett||canCity)&&hovV===v.id;
                return(
                  <g key={v.id} onClick={()=>handleVertexClick(v.id)} onMouseEnter={()=>setHovV(v.id)} onMouseLeave={()=>setHovV(null)} style={{cursor:"pointer"}}>
                    {b?(
                      <>
                        <circle cx={v.x} cy={v.y} r={b.type==="city"?13:9} fill={PC[b.player]} stroke="white" strokeWidth={b.player===myIndex?2.5:1.5}/>
                        {b.type==="city"&&<text x={v.x} y={v.y+5} textAnchor="middle" fontSize="11" fill="white">★</text>}
                      </>
                    ):(
                      <circle cx={v.x} cy={v.y} r={8} fill={highlight?"#ffffff25":"transparent"} stroke={(canSett||canCity)?"#ffffff55":"transparent"} strokeWidth="1.5"/>
                    )}
                    <circle cx={v.x} cy={v.y} r={11} fill="transparent"/>
                  </g>
                );
              })}
            </svg>
          </div>

          {/* Side panel */}
          <div style={{flex:"1 1 240px",maxWidth:"270px",display:"flex",flexDirection:"column",gap:"7px"}}>

            {/* Status bar */}
            <div style={{...panelStyle,border:`1px solid ${isMyTurn?"#2a6020":"#1e2a14"}`}}>
              <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:"4px"}}>
                <span style={{color:PC[gs.curPlayer],fontWeight:"bold",fontSize:"15px"}}>{P.name}のターン</span>
                <span style={{color:"#c09030",fontSize:"13px",letterSpacing:"1px"}}>🎲 {diceStr}</span>
              </div>
              <div style={{fontSize:"11px",background:"#060d04",border:"1px solid #1a2410",borderRadius:"5px",padding:"4px 8px",color:isMyTurn?"#b09060":"#5a7040"}}>
                {statusMsg}
              </div>
            </div>

            {/* Player cards */}
            {gs.players.map(p=>(
              <div key={p.id} style={{...panelStyle,border:`1px solid ${p.id===gs.curPlayer?PC[p.id]+"77":p.id===myIndex?"#1e3a14":"#162010"}`,background:p.id===gs.curPlayer?"#0f1c09":"#0a1208"}}>
                <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:"5px"}}>
                  <div style={{display:"flex",alignItems:"center",gap:"6px"}}>
                    <div style={{width:"10px",height:"10px",borderRadius:"50%",background:PC[p.id],boxShadow:`0 0 5px ${PC[p.id]}88`}}/>
                    <span style={{color:PC[p.id],fontWeight:"bold",fontSize:"13px"}}>{p.name}</span>
                    {p.id===myIndex&&<span style={{fontSize:"10px",color:"#3a5028",border:"1px solid #1a2a10",borderRadius:"3px",padding:"0 4px"}}>あなた</span>}
                  </div>
                  <span style={{color:"#c09030",fontSize:"12px",fontWeight:"bold"}}>⭐{p.vp}</span>
                </div>
                <div style={{display:"flex",flexWrap:"wrap",gap:"3px"}}>
                  {Object.entries(p.res).map(([r,n])=>(
                    <span key={r} style={{background:"#060d04",border:`1px solid ${n>0?"#1e3410":"#101808"}`,borderRadius:"4px",padding:"2px 5px",fontSize:"11px",color:n>0?"#e0d090":"#303820"}}>
                      {RI[r]}{n}
                    </span>
                  ))}
                </div>
              </div>
            ))}

            {/* Actions */}
            {phase==="main"&&isMyTurn&&(
              <div style={panelStyle}>
                <div style={{fontSize:"10px",color:"#3a5028",marginBottom:"6px",letterSpacing:"1px"}}>⚒ アクション</div>
                <div style={{display:"flex",flexDirection:"column",gap:"4px"}}>
                  <button onClick={handleRollDice} disabled={gs.diceRolled} style={btnStyle(gs.diceRolled,false)}>
                    🎲 サイコロを振る
                  </button>
                  <button onClick={()=>handleBuildMode("road")} disabled={!gs.diceRolled||!myP||!canAfford(myP,COSTS.road)} style={btnStyle(!gs.diceRolled||!myP||!canAfford(myP,COSTS.road),gs.buildMode==="road")}>
                    🛤️ 道を建設 <span style={{float:"right",fontSize:"10px",opacity:0.7}}>🪵🧱</span>
                  </button>
                  <button onClick={()=>handleBuildMode("settlement")} disabled={!gs.diceRolled||!myP||!canAfford(myP,COSTS.settlement)} style={btnStyle(!gs.diceRolled||!myP||!canAfford(myP,COSTS.settlement),gs.buildMode==="settlement")}>
                    🏠 定住地を建設 <span style={{float:"right",fontSize:"10px",opacity:0.7}}>🪵🧱🐑🌾</span>
                  </button>
                  <button onClick={()=>handleBuildMode("city")} disabled={!gs.diceRolled||!myP||!canAfford(myP,COSTS.city)} style={btnStyle(!gs.diceRolled||!myP||!canAfford(myP,COSTS.city),gs.buildMode==="city")}>
                    🏙️ 都市に昇格 <span style={{float:"right",fontSize:"10px",opacity:0.7}}>🌾🌾⛏️⛏️⛏️</span>
                  </button>
                  <button onClick={handleEndTurn} disabled={!gs.diceRolled||gs.robberMode}
                    style={{...btnStyle(!gs.diceRolled||gs.robberMode,false),marginTop:"4px",borderTop:"1px solid #1a2410",paddingTop:"9px",color:"#90b070"}}>
                    ⏭️ ターン終了
                  </button>
                </div>
              </div>
            )}

            {/* Game log */}
            <div style={{background:"#060d04",border:"1px solid #162010",borderRadius:"9px",padding:"8px 10px",maxHeight:"170px",overflowY:"auto",flex:1}}>
              <div style={{fontSize:"10px",color:"#3a5028",marginBottom:"5px",letterSpacing:"1px"}}>📜 ゲームログ</div>
              {(gs.log||[]).map((l,i)=>(
                <div key={i} style={{fontSize:"11px",color:i===0?"#c0b070":"#384828",padding:"2px 0",borderBottom:i===0?"1px solid #162010":"none",lineHeight:"1.5"}}>
                  {l}
                </div>
              ))}
            </div>

            {/* Help */}
            <div style={{background:"#060d04",border:"1px solid #162010",borderRadius:"8px",padding:"7px 10px"}}>
              <div style={{fontSize:"10px",color:"#2a3820",lineHeight:"1.6"}}>
                🏠 定住地＝1VP ｜ 🏙️ 都市＝2VP<br/>
                ⭐ 10VPで勝利 ｜ 🏴 7でロバー移動
              </div>
            </div>
          </div>
        </div>
      </div>
    );
  }

  return (
    <div style={{minHeight:"100vh",background:BG,display:"flex",alignItems:"center",justifyContent:"center",color:"#f0dda0",fontFamily:"Georgia,serif"}}>
      読み込み中...
    </div>
  );
}