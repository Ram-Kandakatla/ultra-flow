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
const RM=matchMedia('(prefers-reduced-motion: reduce)'), MS={stagger:35,wave:28,pop:320,ring:450,spark:600,fade:400,lift:420,burst:1600}; // lift = .pop board CSS
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

// Shop: cosmetics bought with points, priced by tier. Each category's first item is free and equipped until another is picked.
const TIER={Free:0,Common:60,Rare:150,Epic:350,Legendary:800},
  SHOP={bg:['Backgrounds',[['classic','Classic','Free'],['ocean','Ocean','Common'],['forest','Forest','Common'],['dunes','Dunes','Rare'],['sakura','Sakura','Rare'],['aurora','Aurora','Epic'],['synth','Synthwave','Epic'],['sky','Time of day','Legendary']]],
    dot:['Dots',[['glossy','Glossy','Free'],['flat','Flat','Common'],['ring','Ring','Rare'],['gem','Gem','Epic'],['star','Star','Legendary']]],
    win:['Win effects',[['wave','Wave','Free'],['ripple','Ripple','Common'],['confetti','Confetti','Rare'],['rainbow','Rainbow','Epic'],['fireworks','Fireworks','Legendary']]]},
  item=(cat,id)=>Object.hasOwn(SHOP,cat)&&SHOP[cat][1].find(([i])=>i===id),
  owned=(cat,id)=>!!item(cat,id)&&(TIER[item(cat,id)[2]]===0||stats.own.includes(cat+':'+id)),
  use=cat=>owned(cat,stats.use[cat])?stats.use[cat]:SHOP[cat][1][0][0];
stats.own=Array.isArray(stats.own)?stats.own:[]; // bought, as "cat:id"
stats.use=stats.use&&typeof stats.use==='object'&&!Array.isArray(stats.use)?stats.use:{}; // equipped id per category
function buy(cat,id){const it=item(cat,id);if(!it)return false; // owned: just equip; otherwise pay first
  if(!owned(cat,id)){const p=TIER[it[2]];if(!(stats.points>=p))return false;stats.points-=p;stats.own.push(cat+':'+id)}
  stats.use[cat]=id;save();setLook();draw();return true}
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
      const c=Math.min(s.length-3,Math.max(3,Math.round(s.length/Math.max(2,Math.round(s.length/L)))));pipes.splice(pipes.indexOf(s),1,s.slice(0,c),s.slice(c))}
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
      if(Q===P){const i=P.indexOf(w);np[a]=P.slice(0,i+1).concat(P.slice(i+1).reverse())}
      else{if(Math.random()<.5)Q.reverse();const i=Q.indexOf(w);if(i<lo||P.length+Q.length-i>hi)continue;np[a]=P.concat(Q.slice(i));np[b]=Q.slice(0,i)}
      if(adj(np[a][0],np[a].at(-1))||adj(np[b][0],np[b].at(-1)))continue; // a pipe's own two dots never end up side by side
      const c=touch(np);if(c<=cost||Math.random()<.05){pipes=np;cost=c} // the rare uphill step keeps the shuffle from getting stuck
    }
    if(pipes.every(s=>!adj(s[0],s.at(-1))))return pipes; // safety net: a cut piece that started with its dots side by side and never moved
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
    Q=i=>{const g=s*.06,b=[i%n*s+g,(i/n|0)*s+g,s-2*g,s-2*g];x.beginPath();x.roundRect?x.roundRect(...b,s*.2):x.rect(...b);x.fill()}, // rounded tile inside a cell
    cs=getComputedStyle(root), v=k=>cs.getPropertyValue(k).trim(), C=sol.map((g,c)=>v('--p'+c)), ds=use('dot'), wf=use('win'), // colors follow the tone
    now=performance.now(), el=(k,c)=>{const f=fx.find(f=>f.k===k&&(c==null||f.c===c));return f?now-f.t0:1e9}, // ms into an effect, huge = finished
    ease=k=>1-(1-Math.min(1,Math.max(0,k)))**3; // ease-out: things arrive and settle
  fx=fx.filter(f=>now-f.t0<f.dur);
  x.clearRect(0,0,cv.width,cv.height);
  x.fillStyle=v('--panel')+'d6';for(const i of cells)x.fillRect(...R(i)); // the board, in its shape; see-through like the panels (84%)
  for(const c of hints)sol[c].forEach((i,j,g)=>{x.globalAlpha=(.42-.34*j/(g.length-1))*ease(el('hint',c)/MS.fade);x.fillStyle=C[c];Q(i)});
  x.globalAlpha=1; // hint = faint trail fading away from the starting dot, no pipe
  paths.forEach((p,c)=>{x.fillStyle=C[c]+'38';for(const i of p)Q(i)});
  const m=(n-1)/2, dly=i=>wf==='ripple'?Math.hypot(i%n-m,(i/n|0)-m)*1.4:i%n+(i/n|0); // win: a wave of color, diagonal or (ripple) out from the center
  paths.forEach((p,c)=>p.forEach(i=>{const e=(el('win')-dly(i)*MS.wave)/MS.pop;
    if(e>0&&e<1){x.globalAlpha=.55*Math.sin(Math.PI*e);x.fillStyle=wf==='rainbow'?`hsl(${dly(i)*24} 90% 60%)`:C[c];Q(i)}}));
  x.globalAlpha=1;x.strokeStyle=v('--tx')+'1f';x.lineWidth=Math.max(1,s/40);
  for(const i of cells)x.strokeRect(...R(i)); // grid lines, which also outline the shape
  x.lineCap=x.lineJoin='round';x.lineWidth=s*.32;
  paths.forEach((p,c)=>{x.strokeStyle=C[c];x.beginPath();p.forEach((i,j)=>x[j?'lineTo':'moveTo'](X(i),Y(i)));x.stroke()});
  x.strokeStyle='#fff';x.globalAlpha=.13; // stacked faint strokes get lighter toward the center: pipes read as rounded tubes
  for(const w of [.22,.12]){x.lineWidth=s*w;paths.forEach(p=>{if(p.length<2)return;x.beginPath();p.forEach((i,j)=>x[j?'lineTo':'moveTo'](X(i),Y(i)));x.stroke()})}
  x.globalAlpha=1;
  if(cur>=0&&ptr){x.globalAlpha=.2;x.fillStyle=C[cur];x.beginPath();x.arc(ptr[0],ptr[1],s*.9,0,7);x.fill();x.globalAlpha=1} // under-finger halo
  x.font=`600 ${s*(ds==='star'?.26:.36)}px ${v('--font-display')}`;x.textAlign='center';x.textBaseline='middle';
  dot.forEach((c,i)=>{if(c<0)return;const k=(el('spawn')-c*MS.stagger)/MS.pop, // new puzzle: dots pop in, staggered by color
      r=s*.36*(k>=1?1:k<=0?0:1+2.70158*(k-1)**3+1.70158*(k-1)**2);
    if(r<=0)return;x.fillStyle=x.strokeStyle=C[c];x.beginPath();DOT[ds](X(i),Y(i),r);
    if(ds==='ring'){x.lineWidth=s*.09;x.stroke()}else x.fill();
    if(ds==='glossy'||ds==='gem'){const g=x.createLinearGradient(0,Y(i)-r,0,Y(i)+r);g.addColorStop(0,'#fff5');g.addColorStop(.45,'#fff0');g.addColorStop(1,'#0002');
      x.fillStyle=g;x.fill()} // convex shading over the color: lit top, shaded bottom, letter area left clean
    if(k>=.7){x.fillStyle=ds==='ring'?C[c]:v('--panel');x.fillText(String.fromCharCode(65+c),X(i),Y(i)+s*.02)}}); // letter = non-color cue
  for(const f of fx)if(f.k==='ring'){const p=(now-f.t0)/f.dur; // connection: ripple out of both dots
    x.globalAlpha=.7*(1-p);x.strokeStyle=C[f.c];x.lineWidth=s*.07;
    for(const i of [sol[f.c][0],sol[f.c].at(-1)]){x.beginPath();x.arc(X(i),Y(i),s*(.36+.45*ease(p)),0,7);x.stroke()}}
  for(const f of fx)if(f.k==='spark'){const p=(now-f.t0)/f.dur,r=s*(.45+.9*ease(p)); // 8 sparks fly out of both dots, turning as they go
    x.globalAlpha=1-p*p;x.fillStyle=C[f.c];
    for(const i of [sol[f.c][0],sol[f.c].at(-1)])for(let k=0;k<8;k++){const a=k*Math.PI/4+p;x.beginPath();x.arc(X(i)+Math.cos(a)*r,Y(i)+Math.sin(a)*r,s*.09*(1-p),0,7);x.fill()}}
  const w=cv.width;
  for(const f of fx)if(f.k==='confetti'){const p=(now-f.t0)/f.dur;if(p<0)continue;x.globalAlpha=Math.min(1,(1-p)*4); // paper falls over the board
    for(let j=0;j<90;j++){const q=p*(1+rnd(j+50)*.7)-rnd(j)*.3;if(q<0)continue;
      x.save();x.translate((rnd(j+9)+Math.sin(q*8+j)*.04)*w,(q*1.3-.08)*w);x.rotate(q*14+j);x.fillStyle=C[j%C.length];x.fillRect(-w*.012,-w*.006,w*.024,w*.012);x.restore()}}
  for(const f of fx)if(f.k==='fireworks')for(let b=0;b<6;b++){const p=(now-f.t0-b*160)/800;if(p<0||p>1)continue; // six staggered bursts
    const cx=(.2+.6*rnd(b+3))*w,cy=(.18+.5*rnd(b+31))*w,d=w*.2*ease(p);x.globalAlpha=1-p;x.fillStyle=C[b%C.length];
    for(let k=0;k<14;k++){const a=k*Math.PI/7+b;x.beginPath();x.arc(cx+Math.cos(a)*d,cy+Math.sin(a)*d+p*p*w*.06,w*.011*(1-p/2),0,7);x.fill()}}
  x.globalAlpha=1;
}
// Dot shapes (Shop): a path around the dot center; ring is stroked, the rest filled.
const DOT={glossy:(X,Y,r)=>x.arc(X,Y,r,0,7), flat:(X,Y,r)=>x.arc(X,Y,r,0,7), ring:(X,Y,r)=>x.arc(X,Y,r*.84,0,7),
  gem:(X,Y,r)=>{for(let k=0;k<4;k++)x.lineTo(X+Math.sin(k*Math.PI/2)*r*1.2,Y-Math.cos(k*Math.PI/2)*r*1.2);x.closePath()},
  star:(X,Y,r)=>{for(let k=0;k<10;k++){const a=k*Math.PI/5,q=k%2?r*.62:r*1.3;x.lineTo(X+Math.sin(a)*q,Y-Math.cos(a)*q)}x.closePath()}},
  rnd=j=>{const v=Math.sin(j*12.9898+78.233)*43758.5453;return v-Math.floor(v)}; // fixed per-index randomness: particles keep their paths frame to frame

function check(){
  const done=paths.map((p,c)=>p.length>1&&dot[p.at(-1)]===c), f=done.filter(Boolean).length, filled=new Set(paths.flat()).size,
    solved=!won&&f===sol.length&&filled===N;
  if(!won)done.forEach((d,c)=>{if(d&&!wasDone[c]){play('ring',c,MS.ring);if(solved)play('spark',c,MS.spark)} // the winning connection also sparks
    if(d&&!scored.has(c)){scored.add(c);total+=connVal()}}); // score: first connection of each color only
  wasDone=done;
  if(solved){won=1;cur=-1;earned=Math.round(total/10);stats.points+=earned;
    const k=key();stats.solved[k]=(stats.solved[k]||0)+1;newRec=!(stats.best[k]<=sec);if(newRec)stats.best[k]=sec;save();
    const wf=use('win'),burst=wf==='confetti'||wf==='fireworks',dur=burst?MS.burst:MS.wave*(2*n-2)+MS.pop;
    pulse(cv,'pop');play(burst?wf:'win',null,dur,MS.lift); // board pops out, then the equipped win effect plays
    setTimeout(()=>won===1&&openDlg(),RM.matches?400:MS.lift+dur+150)}
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
setInterval(()=>{if(!won&&!document.hidden&&$('home').hidden&&!$('setDlg').open){sec++;hud()}},1000); // pauses in the background, on the home screen and in Settings

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
  $('keepBtn').textContent=won?'View board':'Keep playing';$('goBtn').textContent=won===1?'Next puzzle →':'New puzzle';
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
  $('ptsLine').textContent=`${stats.points} points · a hint costs ${HINT} · spend the rest in the Shop`;
}
function showHome(){pick=shape;renderHome();tab('play');$('home').hidden=false;$('game').inert=true}
function tab(t){for(const b of $('tabs').children)b.setAttribute('aria-pressed',b.dataset.tab===t);
  for(const k of ['play','profile','shop'])$('tab-'+k).hidden=k!==t;
  if(t==='profile')renderProfile();if(t==='shop')renderShop();$('home').scrollTop=0}
$('tabs').onclick=e=>{const b=e.target.closest('[data-tab]');if(b)tab(b.dataset.tab)};
$('toShop').onclick=()=>tab('shop');
// Profile: points, the hardest level cleared on any shape, and per shape its hardest clear with the best time there.
const topClear=sh=>LEVELS.findLast(([,z])=>stats.best[sh+'-'+z]!=null);
function renderProfile(){const rows=Object.keys(SHAPES).map(sh=>[sh,topClear(sh)]),top=LEVELS.findLast(([,z])=>rows.some(([,t])=>t?.[1]===z));
  $('profPts').textContent=+stats.points||0;$('profTop').textContent=top?top[0]:'None yet';$('bestsHead').textContent='Best times on your hardest clears';
  $('bests').innerHTML=rows.map(([sh,t])=>{const k=t&&sh+'-'+t[1];
    return `<li>${preview(sh)}<span>${sh}<small>${t?`${t[0]} ${t[1]}×${t[1]}`:'Not cleared yet'}</small></span><b>${t?fmt(+stats.best[k]):'—'}${t?`<small>${+stats.solved[k]||0} solved</small>`:''}</b></li>`}).join('');
  $('profTotal').textContent=`${Object.values(stats.solved).reduce((a,v)=>a+(+v||0),0)} puzzles solved in all`}
// Shop tab: buying takes two taps (the first turns the button into a confirm); owned items equip in one.
function renderShop(){const pts=+stats.points||0,now=skyAt(new Date().getHours());
  $('tab-shop').innerHTML=`<p class="wallet"><b>${pts}</b> points · buy once, switch any time</p>`+Object.entries(SHOP).map(([cat,[title,list]])=>
    `<section><h2 class="eyebrow">${title}</h2><div class="items">${list.map(([id,name,tier])=>{const own=owned(cat,id),on=use(cat)===id,p=TIER[tier];
      return `<div class="item card"><i class="pv pv-${cat} ${cat==='bg'?'theme-'+id+(id==='sky'?' '+now:''):cat+'-'+id}" aria-hidden="true"></i><b id="it-${cat}-${id}">${name}</b><span class="tier t-${tier}">${tier}</span>`+
        `<button class="btn${on?' in-use':' btn-primary'}" data-cat="${cat}" data-id="${id}" aria-describedby="it-${cat}-${id}"${on||!own&&pts<p?' aria-disabled="true"':''}>${on?'In use':own?'Use':'Buy · '+p}</button></div>`}).join('')}</div></section>`).join('')}
$('tab-shop').onclick=e=>{const b=e.target.closest('button[data-cat]');if(!b||b.getAttribute('aria-disabled'))return;
  const {cat,id}=b.dataset,at=()=>$('tab-shop').querySelector(`[data-cat="${cat}"][data-id="${id}"]`);
  if(!owned(cat,id)&&!b.dataset.sure){renderShop();const c=at();c.dataset.sure=1;c.textContent='Tap again to buy';c.focus();return}
  buy(cat,id);renderShop();at().focus()};
$('shapes').onclick=e=>{const b=e.target.closest('.shape');if(!b)return;pick=b.dataset.shape;renderHome();$('shapes').querySelector(`[data-shape="${pick}"]`).focus()};
$('levels').onclick=e=>{const b=e.target.closest('.level');if(!b)return;$('home').hidden=true;$('game').inert=false;newGame(pick,+b.dataset.n)};

// Theme: follows the system until a switch is used, then the choice is saved with the stats (GPA-calc behavior).
const mq=matchMedia('(prefers-color-scheme: dark)'), toggles=document.querySelectorAll('.theme-toggle'),
  syncTheme=()=>{const d=root.dataset.theme?root.dataset.theme==='dark':mq.matches;toggles.forEach(t=>t.setAttribute('aria-checked',d));draw()};
if(stats.theme)root.dataset.theme=stats.theme;
toggles.forEach(t=>t.onclick=()=>{stats.theme=root.dataset.theme=t.getAttribute('aria-checked')==='true'?'light':'dark';
  stats.sky=stats.theme==='dark'?'nighttime':'daytime';save();setLook()}); // the switch also pins the sky: day = the 8 AM sky, night = the 8 PM sky
new MutationObserver(syncTheme).observe(root,{attributes:true,attributeFilter:['data-theme']});mq.addEventListener('change',syncTheme);

// Look: body gets the equipped background (theme-*). With Time of day it also gets the sky, which follows the clock (checked every minute)
// until the Dark mode switch or Settings picks one, saved with the stats. Settings' sky picker only works with Time of day equipped.
const SKY=[[5,'nighttime'],[8,'sunrise'],[17,'daytime'],[20,'sunset'],[24,'nighttime']], skyAt=h=>SKY.find(([e])=>h<e)[1], // [hour it ends, sky]
  pinned=()=>SKY.some(([,s])=>s===stats.sky)&&stats.sky, // anything else (incl. 'auto') follows the clock
  setLook=()=>{const a=skyAt(new Date().getHours()),bg=use('bg');$('autoSw').className=a;
    document.body.className='theme-'+bg+(bg==='sky'?' '+(pinned()||a):'');$('skyPick').disabled=bg!=='sky';$('skyHint').hidden=bg==='sky'};
document.querySelectorAll('.set-btn').forEach(b=>b.onclick=()=>{$('setForm').sky.value=pinned()||'auto';$('setDlg').showModal()});
$('setForm').onchange=e=>{stats.sky=e.target.value;save();setLook()};
setLook();setInterval(setLook,60000);document.addEventListener('visibilitychange',setLook); // resumed apps catch up at once

const [ls,lz]=stats.last||[];
newGame(Object.hasOwn(SHAPES,ls)?ls:'Square',LEVELS.some(l=>l[1]===lz)?lz:5);syncTheme();showHome(); // last board waits behind the home screen
document.fonts?.ready.then(draw); // dot letters use the display face once it loads

// Self-check: open with #test. Every shape x level: hints, scoring, records, and the generated solution through the win check.
if(location.hash==='#test'){save=()=>{};let bad=0,t0=performance.now();
  const adj=(a,b)=>Math.abs(a-b)===n||Math.abs(a-b)===1&&(a/n|0)===(b/n|0);
  for(const sh in SHAPES)for(const [,z] of LEVELS)for(let k=0;k<5;k++){newGame(sh,z);stats.points=HINT;$('hintBtn').click();bad+=stats.points!==0||hints.size!==1;
    paths[0]=[...sol[0]];check();const t1=total;paths[0]=[sol[0][0]];check();paths[0]=[...sol[0]].reverse();check();bad+=t1!==connVal()||total!==t1; // reconnecting pays nothing
    sec=k+5;paths=sol.map(s=>[...s]);check();
    bad+=!won||stats.best[key()]>sec||sol.length>PALETTE||sol.length!==flows(N,n)||sol.some(s=>s.length>2*N/sol.length)||new Set(sol.flat()).size!==N||sol.flat().some(i=>!M[i])||sol.some(s=>s.length<3||s.some((v,j)=>j&&!adj(v,s[j-1])))}
  {const b=stats.best;stats.best={'Ring-9':40,'Ring-13':90,'Plus-5':9};bad+=topClear('Ring')[1]!==13||topClear('Plus')[1]!==5||topClear('Circle')!==undefined;stats.best=b} // profile: hardest clear per shape
  bad+=[4,5,7,8,16,17,19,20,23].map(skyAt)+''!=='nighttime,sunrise,sunrise,daytime,daytime,sunset,sunset,nighttime,nighttime';
  const keep=[stats.points,stats.own,stats.use];stats.own=[];stats.use={}; // shop: can't overspend, pays once, re-equips free
  stats.points=TIER.Rare-1;bad+=buy('bg','dunes')||stats.points!==TIER.Rare-1||use('bg')!=='classic';
  stats.points=TIER.Rare;bad+=!buy('bg','dunes')||stats.points!==0||use('bg')!=='dunes'||!document.body.classList.contains('theme-dunes');
  bad+=!buy('bg','dunes')||stats.points!==0||!buy('bg','classic')||use('bg')!=='classic'||buy('bg','nope')||buy('toString','x');
  for(const cat in SHOP)for(const [id] of SHOP[cat][1]){stats.points=1e4;bad+=!buy(cat,id)||use(cat)!==id; // every cosmetic equips and draws
    fx=[{k:id==='confetti'||id==='fireworks'?id:'win',t0:performance.now()-400,dur:MS.burst}];draw()}
  [stats.points,stats.own,stats.use]=keep;fx=[];setLook();draw();
  console.log(bad?`SELFTEST FAIL ${bad}`:`SELFTEST OK ${Math.round(performance.now()-t0)}ms`)}
