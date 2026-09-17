
const R=5,C=11,T=55;
const defs=[
{id:"blue",n:"Blau",c:"#1769d1",s:[[0,0],[0,1],[1,0],[2,0],[3,0]]},
{id:"green",n:"Grün",c:"#18b879",s:[[0,2],[0,3],[1,0],[1,1],[1,2]]},
{id:"yellow",n:"Gelb",c:"#f2d400",s:[[0,0],[0,1],[1,0],[2,0],[2,1]]},
{id:"white5",n:"Weiß +",c:"#e8edf2",s:[[0,1],[1,0],[1,1],[1,2],[2,1]]},
{id:"orange",n:"Orange",c:"#ff5a16",s:[[0,0],[0,1],[1,0],[2,0]]},
{id:"white3",n:"Weiß 3",c:"#e8edf2",s:[[0,0],[1,0],[1,1]]},
{id:"purple",n:"Lila",c:"#7045b5",s:[[0,0],[1,0],[2,0],[3,0]]},
{id:"pink",n:"Pink",c:"#e52c9b",s:[[0,1],[0,2],[1,0],[1,1],[2,0]]},
{id:"cyan",n:"Hellblau",c:"#79dbe8",s:[[0,2],[1,2],[2,0],[2,1],[2,2]]},
{id:"red",n:"Rot",c:"#e51c2a",s:[[0,1],[1,0],[1,1],[2,0],[2,1]]},
{id:"lightpink",n:"Hellrosa",c:"#f3c8c9",s:[[0,1],[1,0],[1,1],[1,2],[1,3]]},
{id:"lightgreen",n:"Hellgrün",c:"#75df43",s:[[0,0],[0,1],[1,0],[1,1]]}
];
if(defs.reduce((n,d)=>n+d.s.length,0)!==T) throw new Error("Formen ergeben nicht 55 Felder");
let pieces=[],selected=null,drag=null,toolbar=null,level=+(localStorage.lonposLevel||1),score=+(localStorage.lonposScore||0),seconds=0,timer;
const board=document.getElementById("board"),grid=document.getElementById("grid"),tray=document.getElementById("tray"),statusEl=document.getElementById("status"),levelEl=document.getElementById("level"),lv=document.getElementById("lv"),tm=document.getElementById("tm"),sc=document.getElementById("sc"),bar=document.getElementById("bar"),prog=document.getElementById("prog");
function fmt(s){return String(Math.floor(s/60)).padStart(2,"0")+":"+String(s%60).padStart(2,"0")}
function norm(a){const mr=Math.min(...a.map(x=>x[0])),mc=Math.min(...a.map(x=>x[1]));return a.map(x=>[x[0]-mr,x[1]-mc]).sort((x,y)=>x[0]-y[0]||x[1]-y[1])}
function rotate(a){return norm(a.map(x=>[x[1],-x[0]]))}
function mirrorShape(a){return norm(a.map(x=>[x[0],-x[1]]))}
function transformCells(p){let a=p.base.map(x=>[...x]);if(p.mirror)a=mirrorShape(a);for(let i=0;i<p.rot;i++)a=rotate(a);return norm(a)}
function shapeSize(a){return{w:Math.max(...a.map(x=>x[1]))+1,h:Math.max(...a.map(x=>x[0]))+1}}
function rngFactory(seed){let x=(seed*1664525+1013904223)>>>0;return()=>{x=(x*1664525+1013904223)>>>0;return x/4294967296}}
function shuffled(a,rng){a=a.slice();for(let i=a.length-1;i>0;i--){const j=Math.floor(rng()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a}
const orientCache=new Map(), placementCache=new Map();
function orientations(base){const key=JSON.stringify(base);if(orientCache.has(key))return orientCache.get(key);const out=[],seen=new Set();for(let m=0;m<2;m++){let a=m?mirrorShape(base):norm(base);for(let r=0;r<4;r++){const n=norm(a),k=JSON.stringify(n);if(!seen.has(k)){seen.add(k);out.push({cells:n,rot:r,mirror:!!m})}a=rotate(a)}}orientCache.set(key,out);return out}
function allPlacements(p){if(placementCache.has(p.id))return placementCache.get(p.id);const out=[];for(const o of orientations(p.base)){const sz=shapeSize(o.cells);for(let r=0;r<=R-sz.h;r++)for(let c=0;c<=C-sz.w;c++){const cells=o.cells.map(([rr,cc])=>(r+rr)*C+c+cc);out.push({r,c,rot:o.rot,mirror:o.mirror,cells})}}placementCache.set(p.id,out);return out}
function canPlacement(pl,used){for(const cell of pl.cells)if(used[cell])return false;return true}
function solveTiling(input,rng){const byCell=Array.from({length:T},()=>[]);for(const p of input)for(const pl of allPlacements(p))for(const cell of pl.cells)byCell[cell].push([p,pl]);const used=new Uint8Array(T),chosen=new Map();let nodes=0;
 function dfs(rem){if(rem.length===0)return true;if(++nodes>120000)return false;let bestCell=-1,best=[];for(let cell=0;cell<T;cell++){if(used[cell])continue;const opts=[];for(const [p,pl] of byCell[cell]){if(!rem.includes(p))continue;if(canPlacement(pl,used))opts.push([p,pl])}if(!opts.length)return false;if(bestCell<0||opts.length<best.length){bestCell=cell;best=opts;if(opts.length===1)break}}
  for(const [p,pl] of shuffled(best,rng)){for(const cell of pl.cells)used[cell]=1;chosen.set(p.id,pl);const next=rem.filter(x=>x!==p);if(dfs(next))return true;chosen.delete(p.id);for(const cell of pl.cells)used[cell]=0}return false}
 return dfs(input.slice())?input.map(p=>({id:p.id,...chosen.get(p.id)})):null}
// Guaranteed fallback tiling for the 12 photographed pieces. It prevents a slow search from ever causing a blank screen.
const FALLBACK={
blue:{r:0,c:0,rot:0,mirror:false}, green:{r:3,c:0,rot:0,mirror:false}, orange:{r:1,c:1,rot:0,mirror:false}, yellow:{r:0,c:2,rot:0,mirror:false}, purple:{r:4,c:3,rot:1,mirror:false}, white3:{r:0,c:4,rot:0,mirror:false}, lightpink:{r:0,c:5,rot:1,mirror:false}, red:{r:2,c:4,rot:1,mirror:false}, white5:{r:2,c:6,rot:0,mirror:false}, lightgreen:{r:0,c:9,rot:0,mirror:false}, pink:{r:1,c:7,rot:1,mirror:false}, cyan:{r:2,c:8,rot:0,mirror:false}
};
function makePieces(){return defs.map(d=>({id:d.id,name:d.n,color:d.c,base:d.s.map(x=>[...x]),rot:0,mirror:false,placed:false,fixed:false,row:0,col:0,pos:[]}))}
function cellsAt(p,row,col){return transformCells(p).map(([r,c])=>[row+r,col+c])}
function validAt(p,row,col,except){if(row<0||col<0)return false;const a=transformCells(p),sz=shapeSize(a);if(row+sz.h>R||col+sz.w>C)return false;const used=occupied(except);return a.every(([r,c])=>!used.has((row+r)+","+(col+c)))}
function occupied(except){const s=new Set();for(const p of pieces){if(p!==except&&p.placed)for(const [r,c] of p.pos)s.add(r+","+c)}return s}
function setPosition(p,row,col){p.row=row;p.col=col;p.pos=cellsAt(p,row,col)}
function buildLevel(){const rng=rngFactory(level);let base=makePieces();let solution=solveTiling(shuffled(base,rng),rng);if(!solution)solution=base.map(p=>({id:p.id,...FALLBACK[p.id],cells:[]}));const fixedIndex=Math.floor(rng()*solution.length),fixedId=solution[fixedIndex].id;
 for(const p of base){const s=solution.find(x=>x.id===p.id);p.rot=s.rot;p.mirror=s.mirror;setPosition(p,s.r,s.c);p.placed=p.id===fixedId;p.fixed=p.id===fixedId;if(!p.fixed){p.rot=0;p.mirror=false;p.placed=false;p.pos=[]}}
 pieces=shuffled(base,rng);selected=null;removeToolbar();seconds=0;clearInterval(timer);tm.textContent="00:00";timer=setInterval(()=>{seconds++;tm.textContent=fmt(seconds)},1000);statusEl.className="";statusEl.textContent="Eine Figur ist bereits platziert. Ziehe die anderen Teile ins Feld.";render();updateStats()}
function updateStats(){levelEl.textContent=level;lv.textContent=level;sc.textContent=score}
function metrics(){const g=grid.getBoundingClientRect();return{g,w:g.width/C,h:g.height/R}}
function pointInBoard(e){const r=board.getBoundingClientRect();return{x:e.clientX-r.left,y:e.clientY-r.top}}
function render(){grid.innerHTML="";for(let r=0;r<R;r++)for(let c=0;c<C;c++){const h=document.createElement("div");h.className="hole";h.dataset.cell=r+","+c;grid.append(h)}for(const p of pieces.filter(x=>x.placed))drawBoardPiece(p);tray.innerHTML="";for(const p of pieces.filter(x=>!x.fixed&&!x.placed))drawTrayPiece(p);const count=pieces.filter(p=>p.placed).reduce((n,p)=>n+p.pos.length,0);bar.style.width=(count/T*100)+"%";prog.textContent=count+" / "+T+" Felder"}
function drawBoardPiece(p){const m=metrics(),cell=Math.min(m.w,m.h)*.84,a=transformCells(p),sz=shapeSize(a);const el=document.createElement("div");el.className="pieceOnBoard"+(selected===p.id?" selected":"")+(p.fixed?" fixedPiece":"");el.dataset.id=p.id;el.style.setProperty("--piece",p.color);el.style.setProperty("--s",cell+"px");el.style.gridTemplateColumns=`repeat(${sz.w},${cell}px)`;const left=8+p.col*m.w+(m.w-cell)/2,top=8+p.row*m.h+(m.h-cell)/2;el.style.left=left+"px";el.style.top=top+"px";a.forEach(([r,c])=>{const d=document.createElement("div");d.className="dot";d.style.gridRow=r+1;d.style.gridColumn=c+1;el.append(d)});el.addEventListener("pointerdown",boardStart,{passive:false});board.append(el)}
function drawTrayPiece(p){const card=document.createElement("div");card.className="piece"+(selected===p.id?" selected":"");card.dataset.id=p.id;card.style.setProperty("--piece",p.color);const a=transformCells(p),sz=shapeSize(a),q=document.createElement("div");q.className="shape";q.style.gridTemplateColumns=`repeat(${sz.w},20px)`;a.forEach(([r,c])=>{const d=document.createElement("div");d.className="dot";d.style.width="20px";d.style.height="20px";d.style.gridRow=r+1;d.style.gridColumn=c+1;q.append(d)});card.append(q);const n=document.createElement("div");n.className="name";n.textContent=p.name;card.append(n);card.addEventListener("pointerdown",trayStart,{passive:false});tray.append(card)}
function makeFloat(p){const f=document.createElement("div");f.className="float";f.style.setProperty("--piece",p.color);const a=transformCells(p),sz=shapeSize(a),m=metrics(),s=Math.min(m.w,m.h)*.84;f.style.setProperty("--s",s+"px");f.style.gridTemplateColumns=`repeat(${sz.w},${s}px)`;a.forEach(([r,c])=>{const d=document.createElement("div");d.className="dot";d.style.gridRow=r+1;d.style.gridColumn=c+1;f.append(d)});board.append(f);return f}
function ghostFor(p,row,col,valid){const g=document.createElement("div");g.className="ghost"+(valid?"":" invalid");g.style.setProperty("--piece",p.color);const a=transformCells(p),sz=shapeSize(a),m=metrics(),s=Math.min(m.w,m.h)*.84;g.style.setProperty("--s",s+"px");g.style.gridTemplateColumns=`repeat(${sz.w},${s}px)`;g.style.left=(8+col*m.w+(m.w-s)/2)+"px";g.style.top=(8+row*m.h+(m.h-s)/2)+"px";a.forEach(([r,c])=>{const d=document.createElement("div");d.className="dot";d.style.gridRow=r+1;d.style.gridColumn=c+1;g.append(d)});board.append(g);return g}
function preview(e){if(!drag)return;e.preventDefault();const pt=pointInBoard(e),m=metrics(),a=transformCells(drag.p),sz=shapeSize(a);drag.f.style.left=pt.x-(sz.w*m.w)/2+"px";drag.f.style.top=pt.y-(sz.h*m.h)/2+"px";const col=Math.round((pt.x-8-(sz.w*m.w)/2)/m.w),row=Math.round((pt.y-8-(sz.h*m.h)/2)/m.h);const valid=validAt(drag.p,row,col,drag.p);if(drag.ghost)drag.ghost.remove();drag.ghost=ghostFor(drag.p,row,col,valid);drag.row=row;drag.col=col;drag.valid=valid}
function beginDrag(p,e){selected=p.id;removeToolbar();const f=makeFloat(p);drag={p,f,ghost:null,row:null,col:null,valid:false};preview(e);window.addEventListener("pointermove",preview,{passive:false});window.addEventListener("pointerup",endDrag,{once:true});window.addEventListener("pointercancel",cancelDrag,{once:true});e.preventDefault()}
function trayStart(e){const p=pieces.find(x=>x.id===e.currentTarget.dataset.id);if(p)beginDrag(p,e)}
function boardStart(e){const p=pieces.find(x=>x.id===e.currentTarget.dataset.id);if(!p)return;if(p.fixed){selected=null;removeToolbar();statusEl.className="";statusEl.textContent="🔒 Die Startfigur bleibt als Hinweis fest im Feld.";e.preventDefault();return}beginDrag(p,e)}
function cleanupDrag(){if(!drag)return;drag.f.remove();if(drag.ghost)drag.ghost.remove();window.removeEventListener("pointermove",preview);window.removeEventListener("pointercancel",cancelDrag)}
function cancelDrag(){if(!drag)return;const p=drag.p;cleanupDrag();drag=null;render();if(selected)showToolbar(pieces.find(x=>x.id===selected))}
function endDrag(){if(!drag)return;const d=drag;cleanupDrag();drag=null;if(d.valid){d.p.placed=true;setPosition(d.p,d.row,d.col);selected=d.p.id;statusEl.className="good";statusEl.textContent="✔ Teil platziert. Tippe es an, um es weiter zu bearbeiten.";render();showToolbar(d.p);if(pieces.every(p=>p.placed))win()}else{statusEl.className="bad";statusEl.textContent="❌ Dort passt das Teil nicht hinein.";render();if(selected)showToolbar(d.p)}}
function removeToolbar(){if(toolbar){toolbar.remove();toolbar=null}}
function tryTransform(p,newRot,newMirror){const old={rot:p.rot,mirror:p.mirror,row:p.row,col:p.col,pos:p.pos.map(x=>[...x])};p.rot=newRot;p.mirror=newMirror;if(p.placed&&!validAt(p,p.row,p.col,p)){p.rot=old.rot;p.mirror=old.mirror;return false}if(p.placed)setPosition(p,p.row,p.col);return true}
function showToolbar(p){if(!p||p.fixed){removeToolbar();return}removeToolbar();const el=document.createElement("div");el.className="toolbar";el.innerHTML='<button class="toolbtn" aria-label="Drehen">↻</button><button class="toolbtn" aria-label="Spiegeln">🪞</button>';el.querySelectorAll("button")[0].addEventListener("pointerdown",e=>{e.stopPropagation();e.preventDefault();if(tryTransform(p,(p.rot+1)%4,p.mirror)){render();showToolbar(p)}else{statusEl.className="bad";statusEl.textContent="❌ Diese Drehung passt hier nicht."}});el.querySelectorAll("button")[1].addEventListener("pointerdown",e=>{e.stopPropagation();e.preventDefault();if(tryTransform(p,p.rot,!p.mirror)){render();showToolbar(p)}else{statusEl.className="bad";statusEl.textContent="❌ Diese Spiegelung passt hier nicht."}});board.append(el);toolbar=el;positionToolbar(p)}
function positionToolbar(p){if(!toolbar||!p||!p.placed)return;const m=metrics(),xs=p.pos.map(x=>x[1]),ys=p.pos.map(x=>x[0]),cx=8+((Math.min(...xs)+Math.max(...xs)+1)/2)*m.w,cy=8+Math.min(...ys)*m.h;toolbar.style.left=cx+"px";toolbar.style.top=Math.max(8,cy-5)+"px"}
function win(){clearInterval(timer);const gain=Math.max(100,1000-seconds*3);score+=gain;localStorage.lonposScore=score;let done=JSON.parse(localStorage.lonposDone||"[]");if(!done.includes(level))done.push(level);localStorage.lonposDone=JSON.stringify(done);updateStats();setTimeout(()=>{alert("🎉 Level "+level+" geschafft!\nZeit: "+fmt(seconds)+"\n+"+gain+" Punkte");if(level<100){level++;localStorage.lonposLevel=level;buildLevel()}},120)}
document.getElementById("reset").onclick=()=>buildLevel();
document.getElementById("levels").onclick=()=>{const n=Number(prompt("Level auswählen (1–100):",level));if(n>=1&&n<=100){level=n;localStorage.lonposLevel=level;buildLevel()}};
window.addEventListener("resize",()=>{render();if(selected)showToolbar(pieces.find(p=>p.id===selected))});
board.addEventListener("pointerdown",e=>{if(e.target===board||e.target===grid){selected=null;removeToolbar();render()}});
try{buildLevel()}catch(err){console.error(err);statusEl.className="bad";statusEl.textContent="Fehler beim Erzeugen des Levels. Bitte Seite neu laden."}
if("serviceWorker" in navigator){navigator.serviceWorker.register("sw.js?v=4").catch(()=>{})}
