navigator.serviceWorker?.register('sw.js')
const LEVELS=[['Easy',5],['Medium',7],['Hard',9],['Expert',11],['Godlike',13]],
  // Board shapes on an odd n x n grid; y,x are offsets from the center c. Each one was checked to generate at every level.
  // Diamonds and hearts were dropped: their checkerboard imbalance makes small sizes impossible to fill with pipes.
  SHAPES={Square:()=>true, Circle:(n,y,x,c)=>y*y+x*x<=(c+.5)**2,
    Ring:(n,y,x)=>{const h=(n-3)/4|0;return Math.abs(y)>h||Math.abs(x)>h}, Plus:(n,y,x)=>{const h=(n+1)/6|0;return Math.abs(y)<=h||Math.abs(x)<=h}},
  maskOf=(sh,n)=>{const c=(n-1)/2;return [...Array(n*n)].map((_,i)=>SHAPES[sh](n,(i/n|0)-c,i%n-c,c))},
  PALETTE=19, flows=(N,n)=>Math.min(PALETTE,Math.max(3,Math.round(N/(n/2+2.5)))), // pipe count for a board of N cells: avg pipe = n/2+2.5 cells, so bigger boards get more, shorter pipes (square: 5,8,12,15,19)
  root=document.documentElement,
  $=id=>document.getElementById(id), cv=$('cv'), x=cv.getContext('2d'), tryDo=f=>{try{return f()}catch{}};
let shape,n,M,N,cells,dot,sol,paths,cur=-1,won,sec,hints,earned,scored,total,ptr,newRec,pick,wasDone=[],fx=[],raf=0;
const key=()=>shape+'-'+n, levelName=z=>LEVELS.find(l=>l[1]===z)[0];
// Motion: one set of timing tokens (ms) for every canvas effect; all of it is skipped under Reduce Motion.
const RM=matchMedia('(prefers-reduced-motion: reduce)'), MS={stagger:35,wave:28,pop:320,ring:450,spark:600,fade:400,lift:420}; // lift = .pop board CSS
function play(k,c,dur,delay=0){if(RM.matches)return;fx.push({k,c,t0:performance.now()+delay,dur});raf||=requestAnimationFrame(loop)}
function pulse(el,cls){el.classList.remove(cls);void el.offsetWidth;el.classList.add(cls)} // restart a one-shot CSS animation
function loop(){raf=0;draw();if(fx.length)raf=requestAnimationFrame(loop)}
const HINT=10, fmt=s=>`${s/60|0}:${String(s%60).padStart(2,'0')}`,
  connVal=()=>{const P=2*N;return Math.round(N*10*P/(P+sec)/sol.length)}; // per connection: bigger board = higher base; halves at par (2s per cell)

// Stats (points, solves and records per shape+level): cookie as asked, mirrored to localStorage because Safari blocks cookies
// inside embedded frames and caps script-set cookies at 7 days (re-saved on every launch to keep it alive).
let stats=tryDo(()=>JSON.parse(tryDo(()=>decodeURIComponent(document.cookie.match(/(?:^|; )flowStats=([^;]*)/)[1]))||localStorage.flowStats))||{};
stats.points??=30; // starter points so a first hint is possible
stats.best??={};stats.solved??={}; // keyed "Shape-n": fastest solve in seconds, solve count
for(const z of [5,9,11]){stats.solved['Square-'+z]??=stats[z];stats.best['Square-'+z]??=stats.best[z]} // carry over square-only counts from before shapes
function save(){const v=JSON.stringify(stats);
  tryDo(()=>document.cookie=`flowStats=${encodeURIComponent(v)};max-age=31536000;path=/;SameSite=Lax${location.protocol==='https:'?';Secure':''}`);tryDo(()=>localStorage.flowStats=v)}

// Puzzle for any board shape: grow one random path over the board (extend into free neighbors, otherwise backbite),
// jumping to a fresh cell when stuck (that jump becomes a cut). Mix with backbite moves, cut into k pipes of even length,
// then shuffle the pipe ends so the dots spread over the board.
// A full-fill solution always exists by construction. ponytail: solutions aren't unique; any full fill wins.
function gen(n,M){
  const nb=i=>[i-n,i+n,i%n?i-1:-1,(i+1)%n?i+1:-1].filter(j=>j>=0&&j<n*n&&M[j]), adj=(a,b)=>nb(a).includes(b),
    cells=M.flatMap((m,i)=>m?[i]:[]), N=cells.length, k=flows(N,n),
    bite=p=>{const o=nb(p.at(-1)).filter(j=>j!==p.at(-2));if(!o.length)return p;const i=p.indexOf(o[Math.random()*o.length|0]);return p.slice(0,i+1).concat(p.slice(i+1).reverse())};
  for(;;){
    let p=[cells[Math.random()*N|0]],seen=new Set(p),idle=0;
    while(p.length<N){
      if(Math.random()<.5)p.reverse();
      const o=nb(p.at(-1)).filter(j=>j!==p.at(-2)),w=o[Math.random()*o.length|0];
      if(w!==undefined&&!seen.has(w)){p.push(w);seen.add(w);idle=0;continue}
      if(w!==undefined){const i=p.indexOf(w);p=p.slice(0,i+1).concat(p.slice(i+1).reverse())}
      if(++idle>N*N){const free=cells.filter(j=>!seen.has(j)),deg=j=>nb(j).filter(q=>!seen.has(q)).length;
        const f=free.sort((a,b)=>deg(a)-deg(b))[0];p.push(f);seen.add(f);idle=0} // stuck: jump (forced cut)
    }
    for(let t=0;t<N*30;t++){if(Math.random()<.5)p.reverse();p=bite(p)}
    const segs=[[p[0]]];for(let i=1;i<N;i++)adj(p[i-1],p[i])?segs.at(-1).push(p[i]):segs.push([p[i]]);
    if(segs.length>k||segs.some(s=>s.length<3))continue;
    let pipes=segs;const L=N/k,lo=Math.max(3,L/2),hi=L*1.5;
    while(pipes.length<k){const s=pipes.reduce((a,b)=>b.length>a.length?b:a);if(s.length<6)break; // cut the longest pipe into ~N/k-cell pieces: even lengths
      const c=Math.round(s.length/Math.max(2,Math.round(s.length/L)));pipes.splice(pipes.indexOf(s),1,s.slice(0,c),s.slice(c))}
    if(pipes.length<k)continue;
    // Every cut left two dots side by side; shuffle them apart. A pipe end steps onto a neighbor: in its own pipe that's a backbite
    // (the pipe winds a new way), in another pipe it takes over that pipe's tail. Lengths stay within lo..hi so no pipe hogs the board,
    // and a step that puts more dots side by side is mostly refused.
    const touch=ps=>{const d=new Set(ps.flatMap(p=>[p[0],p.at(-1)]));let s=0;for(const i of d)for(const j of nb(i))s+=d.has(j);return s};
    let cost=touch(pipes);
    for(let t=0;t<N*40;t++){
      const a=Math.random()*k|0,P=pipes[a];if(Math.random()<.5)P.reverse();
      const o=nb(P.at(-1)).filter(j=>j!==P.at(-2)),w=o[Math.random()*o.length|0],b=pipes.findIndex(q=>q.includes(w)),Q=pipes[b],np=[...pipes];
      if(b<0)continue;
      if(Q===P){const x=P.indexOf(w);np[a]=P.slice(0,x+1).concat(P.slice(x+1).reverse())}
      else{if(Math.random()<.5)Q.reverse();const i=Q.indexOf(w);if(i<lo||P.length+Q.length-i>hi)continue;np[a]=P.concat(Q.slice(i));np[b]=Q.slice(0,i)}
      const c=touch(np);if(c<=cost||Math.random()<.05){pipes=np;cost=c} // the rare uphill step keeps the shuffle from getting stuck
    }
    if(pipes.every(s=>!adj(s[0],s.at(-1))))return pipes; // no pipe may have its two dots side by side
  }
}

function newGame(sh,z){
  shape=sh;n=z;M=maskOf(sh,n);cells=M.flatMap((m,i)=>m?[i]:[]);N=cells.length;sol=gen(n,M);
  dot=Array(n*n).fill(-1);sol.forEach((s,c)=>dot[s[0]]=dot[s.at(-1)]=c);
  paths=sol.map(()=>[]);won=0;cur=-1;sec=0;earned=0;newRec=false;hints=new Set();scored=new Set();total=0;stats.last=[sh,z];save();
  wasDone=[];fx=[];delete $('sc').dataset.v;play('spawn',null,MS.pop+MS.stagger*sol.length);resize(); // fx reset: old effects point at old colors
}

function resize(){
  const w=$('wrap'),s=Math.floor(Math.min(w.clientWidth,w.clientHeight)),d=devicePixelRatio||1;
  cv.style.width=cv.style.height=s+'px';cv.width=cv.height=Math.round(s*d);draw();check();
  // Win pop: 1.2x in the wide layout; in the one-column layout up to 1.12x, capped so the spring's ~11% overshoot stays on screen.
  cv.style.setProperty('--pop',WIDE.matches?1.2:Math.min(1.12,1+(innerWidth/s-1)/1.11).toFixed(3));
}
const WIDE=matchMedia('(min-width:700px) and (min-aspect-ratio:5/4)'); // same query as the wide-layout CSS

function draw(){
  const s=cv.width/n, X=i=>(i%n+.5)*s, Y=i=>((i/n|0)+.5)*s, R=i=>[i%n*s,(i/n|0)*s,s,s],
    cs=getComputedStyle(root), v=k=>cs.getPropertyValue(k).trim(), C=sol.map((g,c)=>v('--p'+c)), // colors follow the theme
    now=performance.now(), el=(k,c)=>{const f=fx.find(f=>f.k===k&&(c==null||f.c===c));return f?now-f.t0:1e9}, // ms into an effect, huge = finished
    ease=k=>1-(1-Math.min(1,Math.max(0,k)))**3; // ease-out: things arrive and settle
  fx=fx.filter(f=>now-f.t0<f.dur);
  x.clearRect(0,0,cv.width,cv.height);
  x.fillStyle=v('--surface');for(const i of cells)x.fillRect(...R(i)); // the board, in its shape
  for(const c of hints)sol[c].forEach((i,j,g)=>{x.globalAlpha=(.42-.34*j/(g.length-1))*ease(el('hint',c)/MS.fade);x.fillStyle=C[c];x.fillRect(...R(i))});
  x.globalAlpha=1; // hint = faint trail fading away from the starting dot, no pipe
  paths.forEach((p,c)=>{x.fillStyle=C[c]+'38';for(const i of p)x.fillRect(...R(i))});
  paths.forEach((p,c)=>p.forEach(i=>{const e=(el('win')-(i%n+(i/n|0))*MS.wave)/MS.pop; // win: diagonal wave of color
    if(e>0&&e<1){x.globalAlpha=.55*Math.sin(Math.PI*e);x.fillStyle=C[c];x.fillRect(...R(i))}}));
  x.globalAlpha=1;x.strokeStyle=v('--s3');x.lineWidth=Math.max(1,s/40);
  for(const i of cells)x.strokeRect(...R(i)); // grid lines, which also outline the shape
  x.lineCap=x.lineJoin='round';x.lineWidth=s*.32;
  paths.forEach((p,c)=>{x.strokeStyle=C[c];x.beginPath();p.forEach((i,j)=>x[j?'lineTo':'moveTo'](X(i),Y(i)));x.stroke()});
  x.strokeStyle='#fff';x.globalAlpha=.13; // stacked faint strokes get lighter toward the center: pipes read as rounded tubes
  for(const w of [.22,.12]){x.lineWidth=s*w;paths.forEach(p=>{if(p.length<2)return;x.beginPath();p.forEach((i,j)=>x[j?'lineTo':'moveTo'](X(i),Y(i)));x.stroke()})}
  x.globalAlpha=1;
  if(cur>=0&&ptr){x.globalAlpha=.2;x.fillStyle=C[cur];x.beginPath();x.arc(ptr[0],ptr[1],s*.9,0,7);x.fill();x.globalAlpha=1} // under-finger halo
  x.font=`600 ${s*.36}px ${v('--font-display')}`;x.textAlign='center';x.textBaseline='middle';
  dot.forEach((c,i)=>{if(c<0)return;const k=(el('spawn')-c*MS.stagger)/MS.pop, // new puzzle: dots pop in, staggered by color
      r=s*.36*(k>=1?1:k<=0?0:1+2.70158*(k-1)**3+1.70158*(k-1)**2);
    if(r<=0)return;x.fillStyle=C[c];x.beginPath();x.arc(X(i),Y(i),r,0,7);x.fill();
    const g=x.createLinearGradient(0,Y(i)-r,0,Y(i)+r);g.addColorStop(0,'#fff5');g.addColorStop(.45,'#fff0');g.addColorStop(1,'#0002');
    x.fillStyle=g;x.fill(); // convex shading over the color: lit top, shaded bottom, letter area left clean
    if(k>=.7){x.fillStyle=v('--surface');x.fillText(String.fromCharCode(65+c),X(i),Y(i)+s*.02)}}); // letter = non-color cue
  for(const f of fx)if(f.k==='ring'){const p=(now-f.t0)/f.dur; // connection: ripple out of both dots
    x.globalAlpha=.7*(1-p);x.strokeStyle=C[f.c];x.lineWidth=s*.07;
    for(const i of [sol[f.c][0],sol[f.c].at(-1)]){x.beginPath();x.arc(X(i),Y(i),s*(.36+.45*ease(p)),0,7);x.stroke()}}
  for(const f of fx)if(f.k==='spark'){const p=(now-f.t0)/f.dur,r=s*(.45+.9*ease(p)); // 8 sparks fly out of both dots, turning as they go
    x.globalAlpha=1-p*p;x.fillStyle=C[f.c];
    for(const i of [sol[f.c][0],sol[f.c].at(-1)])for(let k=0;k<8;k++){const a=k*Math.PI/4+p;x.beginPath();x.arc(X(i)+Math.cos(a)*r,Y(i)+Math.sin(a)*r,s*.09*(1-p),0,7);x.fill()}}
  x.globalAlpha=1;
}

function check(){
  const done=paths.map((p,c)=>p.length>1&&dot[p.at(-1)]===c), f=done.filter(Boolean).length, filled=new Set(paths.flat()).size,
    solved=!won&&f===sol.length&&filled===N;
  if(!won)done.forEach((d,c)=>{if(d&&!wasDone[c]){play('ring',c,MS.ring);if(solved)play('spark',c,MS.spark)} // the winning connection also sparks
    if(d&&!scored.has(c)){scored.add(c);total+=connVal()}}); // score: first connection of each color only
  wasDone=done;
  if(solved){won=1;cur=-1;earned=Math.round(total/10);stats.points+=earned;
    const k=key();stats.solved[k]=(stats.solved[k]||0)+1;newRec=!(stats.best[k]<=sec);if(newRec)stats.best[k]=sec;save();
    const wave=MS.wave*(2*n-2)+MS.pop;pulse(cv,'pop');play('win',null,wave,MS.lift); // board pops out, then the shine sweeps it
    setTimeout(()=>won===1&&openDlg(),RM.matches?400:MS.lift+wave+150)}
  $('st').textContent=won===2?'Solution shown. Tap Done for a new one':won?`Solved in ${fmt(sec)} · +${earned} points`:`Flows ${f}/${sol.length} · Pipe ${Math.round(filled*100/N)}%`;
  $('st').className=won===1?'win':'';$('best').textContent=`${shape} · ${levelName(n)} ${n}×${n} · solved ${stats.solved[key()]||0}`;hud();
}
function hud(){$('tm').textContent=fmt(sec);setNum('sc',total);setNum('pts',stats.points)}
// Numbers that change pop (CSS .bump) and count to their new value.
function countUp(el,from,to,f=v=>v){const t0=el.t0=performance.now();
  if(RM.matches||from===to)return el.textContent=f(to);
  const step=t=>{if(el.t0!==t0)return;const k=Math.max(0,Math.min(1,(t-t0)/MS.fade));el.textContent=f(Math.round(from+(to-from)*(1-(1-k)**3)));if(k<1)requestAnimationFrame(step)};
  requestAnimationFrame(step)}
function setNum(id,v){const el=$(id),from=+el.dataset.v;el.dataset.v=v;
  if(isNaN(from)||from===v){el.t0=0;el.textContent=v;return}
  pulse(el,'bump');countUp(el,from,v)}
setInterval(()=>{if(!won&&!document.hidden&&$('home').hidden){sec++;hud()}},1000); // pauses in the background and on the home screen

const cellAt=e=>{const r=cv.getBoundingClientRect(),c=Math.floor((e.clientX-r.left)/r.width*n),w=Math.floor((e.clientY-r.top)/r.height*n);
  ptr=[(e.clientX-r.left)*cv.width/r.width,(e.clientY-r.top)*cv.height/r.height]; // finger position for the halo
  return c>=0&&w>=0&&c<n&&w<n&&M[w*n+c]?w*n+c:-1};

cv.onpointerdown=e=>{
  const i=cellAt(e);if(i<0||won)return;
  if(dot[i]>=0){cur=dot[i];paths[cur]=[i]}                       // touching a dot restarts that color from it
  else{cur=paths.findIndex(p=>p.includes(i));if(cur<0)return;paths[cur].length=paths[cur].indexOf(i)+1}
  cv.setPointerCapture(e.pointerId);draw();check();
};
cv.onpointermove=e=>{
  const t=cellAt(e);if(cur<0||t<0)return;
  const p=paths[cur];
  while(p.at(-1)!==t){                                           // walk one cell at a time so fast swipes don't skip
    const a=p.at(-1),dr=(t/n|0)-(a/n|0),dc=t%n-a%n,b=Math.abs(dc)>=Math.abs(dr)?a+Math.sign(dc):a+Math.sign(dr)*n,k=p.indexOf(b);
    if(k>=0){p.length=k+1;continue}                               // backtrack over own pipe
    if(!M[b]||p.length>1&&dot[a]===cur||dot[b]>=0&&dot[b]!==cur)break; // off the board, pipe finished, or another color's dot
    paths.forEach((q,o)=>{const j=q.indexOf(b);if(o!==cur&&j>=0)q.length=j}); // cut through other pipes
    p.push(b);
  }
  draw();check();
};
cv.onpointerup=cv.onpointercancel=()=>{cur=-1;draw()};
addEventListener('resize',resize);

const openDlg=$('doneBtn').onclick=()=>{
  $('dh').textContent=['Leave this puzzle?','Puzzle solved!','Solution shown'][won];
  $('dsum').hidden=$('rec').hidden=won!==1;$('dt').textContent=fmt(sec);countUp($('ds'),0,total);countUp($('de'),0,earned,v=>'+'+v);
  $('rec').textContent=newRec?`New record for ${shape} ${levelName(n)}`:`Record ${fmt(stats.best[key()]??0)}`;$('rec').className='rec-line'+(newRec?' new':'');
  $('keepBtn').textContent=won?'View board':'Keep playing';$('goBtn').textContent=won===1?'Next puzzle':'New puzzle';
  $('dlg').returnValue='';if(!$('dlg').open)$('dlg').showModal();
};
$('dlg').onclose=()=>{const r=$('dlg').returnValue;if(r==='go')newGame(shape,n);if(r==='home')showHome()};
$('hintBtn').onclick=()=>{
  if(won)return;
  const cand=sol.map((g,c)=>c).filter(c=>!hints.has(c)&&!(paths[c].length===sol[c].length&&sol[c].every(i=>paths[c].includes(i)))),
    c=cand[Math.random()*cand.length|0];
  if(c===undefined)return $('st').textContent='Every pipe already has a hint';
  if(stats.points<HINT)return $('st').textContent=`A hint costs ${HINT} points. Solve puzzles to earn more`;
  stats.points-=HINT;hints.add(c);play('hint',c,MS.fade);save();draw();hud();
};
$('solBtn').onclick=()=>{if(won)return;paths=sol.map(s=>[...s]);won=2;cur=-1;draw();check()}; // won=2: revealed, not counted

// Home screen: shape tiles (previewed from the real 9x9 mask) and one row per level with that shape's record and solves.
const preview=sh=>'<svg viewBox="0 0 9 9" aria-hidden="true">'+maskOf(sh,9).map((on,i)=>on?`<rect x="${i%9+.08}" y="${(i/9|0)+.08}" width=".84" height=".84" rx=".2"/>`:'').join('')+'</svg>';
function renderHome(){
  $('shapes').innerHTML=Object.keys(SHAPES).map(sh=>`<button class="shape" data-shape="${sh}" aria-pressed="${sh===pick}">${preview(sh)}${sh}</button>`).join('');
  $('levels').innerHTML=LEVELS.map(([name,z])=>{const k=pick+'-'+z,b=stats.best[k],f=flows(maskOf(pick,z).filter(Boolean).length,z);
    return `<li><button class="level" data-n="${z}"><b>${name}</b><span class="sz">${z}×${z}<span class="flows" role="img" aria-label="${f} colors">${[...Array(f)].map((_,c)=>`<i style="background:var(--p${c})"></i>`).join('')}</span></span><span class="rec">${b!=null?'Record '+fmt(b):'No record yet'}<br>${+stats.solved[k]||0} solved</span></button></li>`}).join('');
  $('ptsLine').textContent=`${stats.points} points · a hint costs ${HINT}`;
}
function showHome(){pick=shape;renderHome();$('home').hidden=false;$('game').inert=true}
$('shapes').onclick=e=>{const b=e.target.closest('.shape');if(!b)return;pick=b.dataset.shape;renderHome();$('shapes').querySelector(`[data-shape="${pick}"]`).focus()};
$('levels').onclick=e=>{const b=e.target.closest('.level');if(!b)return;$('home').hidden=true;$('game').inert=false;newGame(pick,+b.dataset.n)};

// Theme: follows the system until a switch is used, then the choice is saved with the stats (GPA-calc behavior).
const mq=matchMedia('(prefers-color-scheme: dark)'), toggles=document.querySelectorAll('.theme-toggle'),
  syncTheme=()=>{const d=root.dataset.theme?root.dataset.theme==='dark':mq.matches;toggles.forEach(t=>t.setAttribute('aria-checked',d));draw()};
if(stats.theme)root.dataset.theme=stats.theme;
toggles.forEach(t=>t.onclick=()=>{stats.theme=root.dataset.theme=t.getAttribute('aria-checked')==='true'?'light':'dark';save()});
new MutationObserver(syncTheme).observe(root,{attributes:true,attributeFilter:['data-theme']});mq.addEventListener('change',syncTheme);

const [ls,lz]=stats.last||[];
newGame(Object.hasOwn(SHAPES,ls)?ls:'Square',LEVELS.some(l=>l[1]===lz)?lz:5);syncTheme();showHome(); // last board waits behind the home screen
document.fonts?.ready.then(draw); // dot letters use the display face once it loads

// Self-check: open with #test. Every shape x level: hints, scoring, records, and the generated solution through the win check.
if(location.hash==='#test'){save=()=>{};let bad=0,t0=performance.now();
  const adj=(a,b)=>Math.abs(a-b)===n||Math.abs(a-b)===1&&(a/n|0)===(b/n|0);
  for(const sh in SHAPES)for(const [,z] of LEVELS)for(let k=0;k<5;k++){newGame(sh,z);stats.points=HINT;$('hintBtn').click();bad+=stats.points!==0||hints.size!==1;
    paths[0]=[...sol[0]];check();const t1=total;paths[0]=[sol[0][0]];check();paths[0]=[...sol[0]].reverse();check();bad+=t1!==connVal()||total!==t1; // reconnecting pays nothing
    sec=k+5;paths=sol.map(s=>[...s]);check();
    bad+=!won||stats.best[key()]>sec||sol.length>PALETTE||new Set(sol.flat()).size!==N||sol.flat().some(i=>!M[i])||sol.some(s=>s.length<3||s.some((v,j)=>j&&!adj(v,s[j-1])))}
  console.log(bad?`SELFTEST FAIL ${bad}`:`SELFTEST OK ${Math.round(performance.now()-t0)}ms`)}
