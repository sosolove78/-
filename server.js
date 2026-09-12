const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' }, maxHttpBufferSize: 2e6 });
const PORT = process.env.PORT || 3000;
app.use(express.static(path.join(__dirname, 'public')));

const words = JSON.parse(fs.readFileSync(path.join(__dirname, 'data/words.json')));
const questions = JSON.parse(fs.readFileSync(path.join(__dirname, 'data/questions.json')));
const truth = JSON.parse(fs.readFileSync(path.join(__dirname, 'data/truth.json')));

const rooms = new Map();
const AV = ['🐶','🐱','🐰','🐻','🐼','🐨','🦊','🐯','🦁','🐸','🐵','🐧','🐥','🦄','🐙','🦖','👻','🤖','👽','🥷','🧙','🧛','🧚','🧑‍🚀','🕵️','👑','😎','🤠','🥳','😈'];
const ADMIN_PASSWORD = '4890';
const LIMITS = { liar:[3,10], mafia:[5,12], truth:[2,10], rummi:[2,4] };
const GAME_NAMES = { liar:'라이어게임', mafia:'마피아게임', truth:'진실게임', rummi:'루미큐브' };
const ROLE_NAMES = { mafia:'마피아', police:'경찰', doctor:'의사', citizen:'시민' };

const uid = () => crypto.randomUUID();
const clean = x => String(x || '').trim().replace(/[<>]/g,'').slice(0,12) || '플레이어';
const active = r => r.players.filter(p => p.connected);
const by = (r,id) => r.players.find(p => p.id === id);
const sock = p => io.sockets.sockets.get(p.socketId);
const clamp = (n,a,b) => Math.max(a,Math.min(b,n));
const shuffle = a => [...a].sort(() => Math.random() - .5);
const pick = a => a[Math.floor(Math.random()*a.length)];
function code(){ let c; do { c='ABCDEFGHJKLMNPQRSTUVWXYZ23456789'.split('').sort(()=>Math.random()-.5).slice(0,5).join(''); } while(rooms.has(c)); return c; }
function player(name,avatar,sessionId){ return { id:uid(), sessionId, name:clean(name), avatar:AV.includes(avatar)?avatar:AV[0], gender:null, connected:true, score:0, alive:true, rolePublic:null, isBot:false }; }
function botPlayer(r){const n=r.players.filter(p=>p.isBot).length+1;return {id:uid(),sessionId:'bot-'+uid(),name:'소소봇'+n,avatar:AV[(n+2)%AV.length],gender:n%2?'male':'female',connected:true,score:0,alive:true,rolePublic:null,isBot:true};}
function bind(s,r,p){ p.socketId=s.id; p.connected=true; s.join(r.code); s.data.roomCode=r.code; s.data.playerId=p.id; }
function clearTimer(r){ if(r.timer) clearTimeout(r.timer); r.timer=null; r.deadline=null; }
function setTimer(r,sec,fn){ clearTimer(r); if(!sec)return; r.deadline=Date.now()+sec*1000; r.timer=setTimeout(()=>{r.timer=null;r.deadline=null;fn();},sec*1000); }

function baseSettings(){ return { liarCount:1, roundTime:120, voteTime:30, liarFinalGuess:true, liarRoleMode:'liar', truthLevel:'normal', drawTime:90, drawRounds:1, rummiTurnTime:60 }; }
function newRoom(game,mode,password,p){ return { code:code(), hostId:p.id, players:[p], game, mode:mode||'normal', phase:'lobby', round:0, password:String(password||'').slice(0,24), settings:baseSettings(), submitted:[], answers:{}, votes:{}, liarIds:[], settingsVersion:1 }; }
function resetRound(r){ clearTimer(r); r.submitted=[]; r.answers={}; r.answersRevealed=false; r.votes={}; r.votesSubmitted=[]; r.voteResult=null; r.guessResult=null; r.nightActions={}; r.nightSubmitted=[]; r.inspections={}; }
function resetForGameSwitch(r,game){ clearTimer(r); r.game=game; r.mode='normal'; r.phase='lobby'; r.round=0; r.players.forEach(p=>{p.alive=true;p.role=null;p.rolePublic=null;p.score=0;}); r.settings=baseSettings(); r.prompt=null; r.liarIds=[]; r.draw=null; r.rummi=null; r.mafiaLog=[]; r.truthQuestion=null; r.truthTurnId=null; resetRound(r); }

function publicState(r){
  const base={ code:r.code, hostId:r.hostId, game:r.game, gameName:GAME_NAMES[r.game], mode:r.mode, phase:r.phase, round:r.round,
    players:r.players.map(p=>({id:p.id,name:p.name,avatar:p.avatar,gender:p.gender||null,connected:p.connected,score:p.score,alive:p.alive,rolePublic:p.rolePublic,isBot:!!p.isBot})),
    settings:r.settings, deadline:r.deadline, submitted:r.submitted||[], answersRevealed:r.answersRevealed, answers:r.answersRevealed?r.answers:{}, votesSubmitted:r.votesSubmitted||[], voteResult:r.voteResult,
    truthTurnId:r.truthTurnId, truthQuestion:r.truthQuestion, mafiaLog:r.mafiaLog||[], nightSubmitted:r.nightSubmitted||[],
    promptMeta:r.game==='liar'&&r.prompt?{category:r.prompt.category,min:r.prompt.min,max:r.prompt.max}:null };
  if(r.game==='draw' && r.draw) Object.assign(base,{draw:{drawerId:r.draw.drawerId,turn:r.draw.turn,totalTurns:r.draw.totalTurns,category:r.draw.prompt?.category||'',guessedIds:r.draw.guessedIds||[],guessFeed:r.draw.guessFeed||[],revealWord:r.phase==='drawReveal'?r.draw.prompt?.word:null,strokes:r.draw.strokes||[]}});
  if(r.game==='rummi' && r.rummi) Object.assign(base,{rummi:{turnPlayerId:r.rummi.turnOrder[r.rummi.turnIndex],turnNumber:r.rummi.turnNumber,board:r.rummi.board,poolCount:r.rummi.pool.length,registered:r.rummi.registered,winnerId:r.rummi.winnerId||null,lastAction:r.rummi.lastAction||''}});
  return base;
}
function scheduleBots(r){
  clearTimeout(r.botTimer);r.botTimer=setTimeout(()=>{
    const bots=active(r).filter(p=>p.isBot); if(!bots.length)return;
    if(r.game==='liar'&&r.mode==='question'&&r.phase==='play'){
      for(const p of bots)if(!r.submitted.includes(p.id)){const min=r.prompt.min,max=r.prompt.max;r.answers[p.id]=Math.floor(min+Math.random()*(max-min+1));r.submitted.push(p.id)}
      if(active(r).every(x=>r.submitted.includes(x.id)))return revealAnswers(r);
    }
    if(['vote','mafiaVote'].includes(r.phase)){
      const voters=bots.filter(p=>!r.votesSubmitted.includes(p.id)&&(r.game!=='mafia'||p.alive));
      for(const p of voters){const targets=active(r).filter(x=>x.id!==p.id&&(r.game!=='mafia'||x.alive));if(targets.length){r.votes[p.id]=pick(targets).id;r.votesSubmitted.push(p.id)}}
      const all=active(r).filter(x=>r.game!=='mafia'||x.alive);if(all.every(x=>r.votesSubmitted.includes(x.id)))return r.game==='liar'?tallyLiar(r):resolveMafiaVote(r);
    }
    if(r.game==='mafia'&&r.phase==='mafiaNight'){
      const actors=bots.filter(p=>p.alive&&['mafia','doctor','police'].includes(p.role)&&!r.nightSubmitted.includes(p.id));
      for(const p of actors){let targets=r.players.filter(x=>x.alive&&x.id!==p.id&&(p.role!=='mafia'||x.role!=='mafia'));if(!targets.length)continue;const t=pick(targets);if(p.role==='police')r.inspections[p.id]={name:t.name,isMafia:t.role==='mafia'};else r.nightActions[p.id]={type:p.role==='mafia'?'kill':'save',target:t.id};r.nightSubmitted.push(p.id)}
      const allActors=r.players.filter(x=>x.alive&&['mafia','doctor','police'].includes(x.role));if(allActors.every(x=>r.nightSubmitted.includes(x.id)))return resolveNight(r);
    }
    if(r.game==='liar'&&r.phase==='liarGuess'&&bots.some(p=>p.id===r.guessingLiarId)){
      const ok=Math.random()<.25;r.guessResult={attempted:true,guess:ok?r.prompt.word:'모르겠어요',answer:r.prompt.word,correct:ok};clearTimer(r);scoreLiarResult(r,ok);r.phase='result';return emitRoom(r);
    }
    if(r.game==='rummi'&&r.phase==='rummiPlay'){
      const pid=r.rummi.turnOrder[r.rummi.turnIndex],bp=by(r,pid);if(bp?.isBot){const t=r.rummi.pool.pop();if(t)r.rummi.racks[pid].push(t);return nextRummi(r,t?`🤖 ${bp.name}이 타일 1개를 가져갔습니다.`:`🤖 ${bp.name}이 턴을 넘겼습니다.`)}
    }
  },700+Math.random()*900);
}
function emitRoom(r){
  io.to(r.code).emit('roomState',publicState(r));
  for(const p of r.players){
    const s=sock(p); if(!s)continue;
    if(r.game==='liar' && r.prompt && r.phase!=='lobby'){
      const bad=r.liarIds.includes(p.id); const spyMode=r.liarRoleMode==='spy';
      s.emit('privateData',{game:'liar',isLiar:bad,isSpy:spyMode&&bad,roleMode:r.liarRoleMode,
        word:r.mode==='normal' ? (bad?(spyMode?r.spyWord:null):r.prompt.word) : null,
        category:r.mode==='normal'?r.prompt.category:null, question:r.mode==='question'&&!bad?r.prompt.question:null,
        min:r.prompt.min,max:r.prompt.max, canGuess:r.phase==='liarGuess'&&r.guessingLiarId===p.id,
        wordLength:r.phase==='liarGuess'&&r.guessingLiarId===p.id?[...r.prompt.word.replace(/\s/g,'')].length:null});
    }
    if(r.game==='mafia' && r.phase!=='lobby'){
      const canSeeMafia=p.role==='mafia'||!p.alive||r.phase==='mafiaResult';
      s.emit('privateData',{game:'mafia',role:p.role,alive:p.alive,mafiaIds:canSeeMafia?r.players.filter(x=>x.role==='mafia').map(x=>x.id):[],mafiaNames:p.role==='mafia'?r.players.filter(x=>x.role==='mafia').map(x=>x.name):[],inspection:r.inspections?.[p.id]||null});
    }
    if(r.game==='draw' && r.draw && r.phase!=='lobby'){
      s.emit('privateData',{game:'draw',isDrawer:r.draw.drawerId===p.id,word:r.draw.drawerId===p.id?r.draw.prompt.word:null,category:r.draw.prompt.category});
    }
    if(r.game==='rummi' && r.rummi && r.phase!=='lobby'){
      s.emit('privateData',{game:'rummi',rack:r.rummi.racks[p.id]||[],isTurn:r.rummi.turnOrder[r.rummi.turnIndex]===p.id,registered:!!r.rummi.registered[p.id]});
    }
  }
  scheduleBots(r);
}

// ---------- Liar / Spy ----------
function chooseSpyWord(prompt){ const pool=words.filter(x=>x.category===prompt.category && x.word!==prompt.word); return pool.length?pick(pool).word:pick(words.filter(x=>x.word!==prompt.word)).word; }
function startLiar(r){
  if(active(r).length<3) throw Error('라이어게임은 최소 3명입니다.'); resetRound(r); r.round++; r.phase='play';
  const n=clamp(r.settings.liarCount,1,Math.min(3,active(r).length-1)); r.liarIds=shuffle(active(r)).slice(0,n).map(p=>p.id);
  r.liarRoleMode=r.mode==='question'?'liar':(r.settings.liarRoleMode==='random'?(Math.random()<.5?'liar':'spy'):r.settings.liarRoleMode);
  r.prompt=pick(r.mode==='question'?questions:words); r.spyWord=r.liarRoleMode==='spy'?chooseSpyWord(r.prompt):null;
  if(r.settings.roundTime)setTimer(r,r.settings.roundTime,()=>r.mode==='question'?revealAnswers(r):openLiarVote(r)); emitRoom(r);
}
function revealAnswers(r){ if(r.game!=='liar'||r.mode!=='question'||r.phase!=='play')return; for(const p of active(r))if(r.answers[p.id]===undefined)r.answers[p.id]=null; r.answersRevealed=true;r.phase='reveal'; if(r.settings.roundTime)setTimer(r,r.settings.roundTime,()=>openLiarVote(r)); emitRoom(r); }
function openLiarVote(r){ clearTimer(r); r.phase='vote';r.votes={};r.votesSubmitted=[];setTimer(r,r.settings.voteTime||30,()=>tallyLiar(r));emitRoom(r); }
function tallyLiar(r){
  if(r.phase!=='vote')return;clearTimer(r);const c={};Object.values(r.votes).forEach(x=>c[x]=(c[x]||0)+1);const m=Math.max(0,...Object.values(c));const top=Object.keys(c).filter(x=>c[x]===m&&m);const target=top.length===1?top[0]:null;const caught=!!target&&r.liarIds.includes(target);
  r.voteResult={counts:c,targetId:target,liarIds:r.liarIds,caught,tie:top.length!==1,roleMode:r.liarRoleMode,citizenWord:r.mode==='normal'?r.prompt.word:null,spyWord:r.liarRoleMode==='spy'?r.spyWord:null};
  if(caught&&r.mode==='normal'&&r.settings.liarFinalGuess){r.phase='liarCaught';emitRoom(r);setTimeout(()=>{if(r.phase!=='liarCaught')return;r.phase='liarGuess';r.guessingLiarId=target;setTimer(r,25,()=>{r.guessResult={attempted:false,answer:r.prompt.word};scoreLiarResult(r,false);r.phase='result';emitRoom(r)});emitRoom(r)},1800);}
  else {scoreLiarResult(r,false);r.phase='result';emitRoom(r);}
}
function scoreLiarResult(r,guessCorrect=false){
  if(r.scoredRound===r.round)return;r.scoredRound=r.round; const caught=r.voteResult?.caught;
  for(const p of r.players){ if(r.liarIds.includes(p.id))p.score+=caught?(guessCorrect?2:0):3; else if(caught)p.score+=1; }
}

// ---------- Truth ----------
function startTruth(r){ if(active(r).length<2)throw Error('진실게임은 최소 2명입니다.'); resetRound(r); r.round++;r.phase='truth';r.truthIndex=(r.truthIndex??-1)+1;if(r.truthIndex>=r.players.length)r.truthIndex=0;let p=r.players[r.truthIndex];let safety=0;while(!p.connected&&safety++<r.players.length){r.truthIndex=(r.truthIndex+1)%r.players.length;p=r.players[r.truthIndex]}r.truthTurnId=p.id;makeTruth(r);emitRoom(r); }
function makeTruth(r){ const level=r.settings.truthLevel||'normal';const targeted=active(r).length>2&&Math.random()<.48;const pool=targeted?truth.targeted[level]:truth[level];let q=pick(pool);if(targeted){const turn=by(r,r.truthTurnId);let targets=active(r).filter(x=>x.id!==r.truthTurnId);if(q.includes('{opposite}')&&turn?.gender)targets=targets.filter(x=>x.gender&&x.gender!==turn.gender);const t=pick(targets.length?targets:active(r).filter(x=>x.id!==r.truthTurnId));if(t)q=q.replaceAll('{target}',t.name).replaceAll('{opposite}',t.name);}r.truthQuestion=q; }

// ---------- Mafia ----------
function mafiaSetup(r){ if(active(r).length<5)throw Error('마피아게임은 최소 5명입니다.');resetRound(r);r.round=1;r.players.forEach(p=>{p.alive=true;p.rolePublic=null;p.score=0});const ps=shuffle(active(r)),mc=ps.length>=8?2:1;ps.forEach((p,i)=>p.role=i<mc?'mafia':i===mc?'police':i===mc+1?'doctor':'citizen');r.mafiaLog=[];r.day=1;r.inspections={};startMafiaNight(r); }
function startMafiaNight(r){resetRound(r);r.phase='mafiaNight';r.mafiaLog.push(`🌙 ${r.day}일차 밤이 되었습니다.`);setTimer(r,r.settings.roundTime||60,()=>resolveNight(r));emitRoom(r);}
function resolveNight(r){if(r.phase!=='mafiaNight')return;clearTimer(r);const acts=Object.values(r.nightActions),kills=acts.filter(a=>a.type==='kill').map(a=>a.target),save=acts.find(a=>a.type==='save')?.target;let victim=null;if(kills.length){const c={};kills.forEach(x=>c[x]=(c[x]||0)+1);victim=Object.keys(c).sort((a,b)=>c[b]-c[a])[0]}if(victim&&victim!==save){const p=by(r,victim);if(p){p.alive=false;r.mafiaLog.push(`☀️ 아침이 밝았습니다. ${p.name}님이 밤에 사망했습니다. 💀`)}}else r.mafiaLog.push('☀️ 아침이 밝았습니다. 지난밤 아무도 사망하지 않았습니다.');if(checkMafiaEnd(r))return;r.phase='mafiaDay';setTimer(r,r.settings.roundTime||120,()=>startMafiaVote(r));emitRoom(r);}
function startMafiaVote(r){clearTimer(r);r.phase='mafiaVote';r.votes={};r.votesSubmitted=[];setTimer(r,r.settings.voteTime||30,()=>resolveMafiaVote(r));emitRoom(r);}
function resolveMafiaVote(r){if(r.phase!=='mafiaVote')return;clearTimer(r);const c={};Object.values(r.votes).forEach(x=>c[x]=(c[x]||0)+1);const m=Math.max(0,...Object.values(c));const top=Object.keys(c).filter(x=>c[x]===m&&m);if(top.length===1){const p=by(r,top[0]);if(p){p.alive=false;p.rolePublic=p.role;r.mafiaLog.push(`⚖️ 투표로 ${p.name}님이 처형되었습니다. 역할: ${ROLE_NAMES[p.role]}`)}}else r.mafiaLog.push('⚖️ 투표가 동률이라 아무도 처형되지 않았습니다.');if(checkMafiaEnd(r))return;r.day++;startMafiaNight(r);}
function checkMafiaEnd(r){const aliveP=r.players.filter(p=>p.alive),m=aliveP.filter(p=>p.role==='mafia').length,c=aliveP.length-m;if(m===0||m>=c){r.phase='mafiaResult';r.mafiaWinner=m===0?'시민팀':'마피아팀';r.mafiaLog.push(`🏆 ${r.mafiaWinner} 승리!`);r.players.forEach(p=>p.rolePublic=p.role);emitRoom(r);return true}return false;}

// ---------- Drawing quiz ----------
function drawSetup(r){ if(active(r).length<2)throw Error('그림퀴즈는 최소 2명입니다.');resetRound(r);r.players.forEach(p=>p.score=0);const order=shuffle(active(r)).map(p=>p.id);r.draw={order,index:0,turn:1,totalTurns:order.length*clamp(+r.settings.drawRounds||1,1,3),strokes:[],guessedIds:[],guessFeed:[]};startDrawTurn(r);}
function startDrawTurn(r){if(!r.draw)return;if(r.draw.turn>r.draw.totalTurns){r.phase='drawResult';clearTimer(r);emitRoom(r);return;}r.phase='drawPlay';r.draw.drawerId=r.draw.order[r.draw.index%r.draw.order.length];r.draw.prompt=pick(words.filter(x=>!['한국 연예인','나라','도시'].includes(x.category)));r.draw.strokes=[];r.draw.guessedIds=[];r.draw.guessFeed=[];setTimer(r,r.settings.drawTime||90,()=>finishDrawTurn(r));emitRoom(r);io.to(r.code).emit('canvasClear');}
function finishDrawTurn(r){if(!r.draw||!['drawPlay','drawReveal'].includes(r.phase))return;clearTimer(r);r.phase='drawReveal';emitRoom(r);setTimeout(()=>{if(r.phase!=='drawReveal')return;r.draw.turn++;r.draw.index++;startDrawTurn(r)},4000);}
function normalizeGuess(x){return String(x||'').trim().replace(/\s+/g,'').toLowerCase();}

// ---------- Rummi ----------
const RC=['red','blue','black','orange'];
function makeTiles(){const t=[];for(let copy=0;copy<2;copy++)for(const color of RC)for(let n=1;n<=13;n++)t.push({id:uid(),color,n,joker:false});t.push({id:uid(),color:'joker',n:0,joker:true},{id:uid(),color:'joker',n:0,joker:true});return shuffle(t);}
function rummiSetup(r){if(active(r).length<2||active(r).length>4)throw Error('루미큐브는 2~4명입니다.');resetRound(r);r.players.forEach(p=>p.score=0);const pool=makeTiles(),ps=active(r),starter=Math.floor(Math.random()*ps.length),order=[...ps.slice(starter),...ps.slice(0,starter)].map(p=>p.id),racks={};for(const p of ps)racks[p.id]=pool.splice(0,14);r.rummi={pool,racks,board:[],registered:Object.fromEntries(ps.map(p=>[p.id,false])),turnOrder:order,turnIndex:0,turnNumber:1,lastAction:`🎲 ${by(r,order[0]).name}님이 무작위로 선 플레이어가 되었습니다.`};r.phase='rummiPlay';setRummiTimer(r);emitRoom(r);}
function setRummiTimer(r){setTimer(r,r.settings.rummiTurnTime||60,()=>rummiTimeout(r));}
function nextRummi(r,msg){clearTimer(r);if(msg)r.rummi.lastAction=msg;r.rummi.turnIndex=(r.rummi.turnIndex+1)%r.rummi.turnOrder.length;r.rummi.turnNumber++;setRummiTimer(r);emitRoom(r);}
function rummiTimeout(r){const id=r.rummi.turnOrder[r.rummi.turnIndex];const tile=r.rummi.pool.pop();if(tile)r.rummi.racks[id].push(tile);nextRummi(r,`⏰ ${by(r,id)?.name}님 시간 종료 · 타일 1개 추가`);}
function tileValue(t){return t.joker?0:t.n;}
function validGroup(g){
  if(!Array.isArray(g)||g.length<3)return false;const non=g.filter(t=>!t.joker),j=g.length-non.length;if(!non.length)return false;
  // same number, unique colors, max 4
  if(g.length<=4 && non.every(t=>t.n===non[0].n) && new Set(non.map(t=>t.color)).size===non.length)return true;
  // same color run with jokers filling gaps
  if(!non.every(t=>t.color===non[0].color))return false;const nums=non.map(t=>t.n).sort((a,b)=>a-b);if(new Set(nums).size!==nums.length)return false;let gaps=0;for(let i=1;i<nums.length;i++)gaps+=nums[i]-nums[i-1]-1;return gaps<=j && (nums[nums.length-1]-nums[0]+1)<=g.length;
}
function initialGroupValue(g){const non=g.filter(t=>!t.joker);if(!non.length)return 0;if(non.every(t=>t.n===non[0].n))return non[0].n*g.length;const nums=non.map(t=>t.n).sort((a,b)=>a-b);let start=Math.max(1,nums[0]-(g.filter(t=>t.joker).length));return Array.from({length:g.length},(_,i)=>start+i).reduce((a,b)=>a+b,0);}
function flatten(board){return board.flat();}
function sameIds(a,b){const x=a.map(t=>t.id).sort(),y=b.map(t=>t.id).sort();return x.length===y.length&&x.every((v,i)=>v===y[i]);}
function tileMapForRummi(r,pid){const all=[...r.rummi.racks[pid],...flatten(r.rummi.board)];return new Map(all.map(t=>[t.id,t]));}
function validateRummiDraft(r,pid,draft){
  if(!Array.isArray(draft?.board)||!Array.isArray(draft?.rackIds))throw Error('잘못된 배치입니다.');const map=tileMapForRummi(r,pid);const board=draft.board.map(g=>g.map(id=>map.get(id))).filter(g=>g.length);if(board.some(g=>g.some(t=>!t)))throw Error('알 수 없는 타일이 포함되어 있습니다.');if(board.some(g=>!validGroup(g)))throw Error('모든 테이블 조합은 3개 이상의 유효한 그룹/연속이어야 합니다.');const rack=draft.rackIds.map(id=>map.get(id));if(rack.some(t=>!t))throw Error('내 패 정보가 올바르지 않습니다.');const allNow=[...flatten(board),...rack];const allBefore=[...flatten(r.rummi.board),...r.rummi.racks[pid]];if(!sameIds(allNow,allBefore))throw Error('타일이 빠지거나 중복되었습니다.');const oldBoardIds=new Set(flatten(r.rummi.board).map(t=>t.id));if(rack.some(t=>oldBoardIds.has(t.id)))throw Error('테이블에 있던 타일은 다시 내 패로 가져올 수 없습니다.');const usedOwn=r.rummi.racks[pid].filter(t=>!draft.rackIds.includes(t.id));if(!usedOwn.length)throw Error('내 패에서 최소 1개는 내려놓아야 합니다.');if(!r.rummi.registered[pid]){const oldBoard=r.rummi.board;for(let i=0;i<oldBoard.length;i++){if(!board[i]||!sameIds(oldBoard[i],board[i]))throw Error('첫 등록 전에는 기존 테이블 조합을 건드릴 수 없습니다.');}const newGroups=board.slice(oldBoard.length);const ownIds=new Set(r.rummi.racks[pid].map(t=>t.id));if(newGroups.flat().some(t=>!ownIds.has(t.id)))throw Error('첫 등록은 내 패만 사용해야 합니다.');const value=newGroups.reduce((s,g)=>s+initialGroupValue(g),0);if(value<30)throw Error(`첫 등록은 합계 30점 이상이어야 합니다. (현재 ${value}점)`);}return {board,rack,usedOwn};
}

io.on('connection', s => {
  s.on('adminLogin',(d,cb)=>{if(String(d.password||'')!==ADMIN_PASSWORD)return cb?.({ok:false,error:'관리자 비밀번호가 올바르지 않습니다.'});s.data.adminToken=uid();cb?.({ok:true,token:s.data.adminToken});});
  s.on('adminBot',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 사용할 수 있습니다.');if(!s.data.adminToken||d.token!==s.data.adminToken)throw Error('관리자 인증이 필요합니다.');if(r.phase!=='lobby')throw Error('AI 인원 변경은 대기실에서만 가능합니다.');const [min,max]=LIMITS[r.game];const add=()=>{if(r.players.length>=max)return false;r.players.push(botPlayer(r));return true};if(d.action==='add')add();else if(d.action==='min')while(r.players.length<min)add();else if(d.action==='max')while(r.players.length<max)add();else if(d.action==='clear')r.players=r.players.filter(p=>!p.isBot);else throw Error('알 수 없는 관리자 명령입니다.');emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('createRoom',(d,cb)=>{try{const game=LIMITS[d.game]?d.game:'liar',sid=String(d.sessionId||uid()),p=player(d.name,d.avatar,sid),r=newRoom(game,d.mode,d.password,p);rooms.set(r.code,r);bind(s,r,p);cb?.({ok:true,code:r.code,playerId:p.id,sessionId:sid});emitRoom(r);}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('joinRoom',(d,cb)=>{try{const r=rooms.get(String(d.code||'').toUpperCase());if(!r)throw Error('방을 찾을 수 없습니다.');if(r.password&&r.password!==String(d.password||''))throw Error('비밀번호가 올바르지 않습니다.');const sid=String(d.sessionId||uid()),old=r.players.find(p=>p.sessionId===sid);if(old){bind(s,r,old);cb?.({ok:true,code:r.code,playerId:old.id,sessionId:sid});emitRoom(r);return;}const max=LIMITS[r.game][1];if(r.players.length>=max)throw Error(`현재 게임은 최대 ${max}명입니다.`);if(r.phase!=='lobby')throw Error('게임 진행 중에는 새로 참가할 수 없습니다.');const p=player(d.name,d.avatar,sid);r.players.push(p);bind(s,r,p);cb?.({ok:true,code:r.code,playerId:p.id,sessionId:sid});emitRoom(r);}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('resumeSession',(d,cb)=>{const r=rooms.get(String(d.code||'').toUpperCase()),p=r?.players.find(x=>x.sessionId===d.sessionId);if(!r||!p)return cb?.({ok:false});bind(s,r,p);cb?.({ok:true,code:r.code,playerId:p.id,sessionId:d.sessionId});emitRoom(r);});
  s.on('switchGame',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId||r.phase!=='lobby')throw Error('대기실에서 방장만 게임을 바꿀 수 있습니다.');const g=d.game;if(!LIMITS[g])throw Error('지원하지 않는 게임입니다.');if(r.players.length>LIMITS[g][1])throw Error(`${GAME_NAMES[g]}은 최대 ${LIMITS[g][1]}명입니다.`);resetForGameSwitch(r,g);emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('setGender',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||!p)throw Error('플레이어를 찾을 수 없습니다.');if(!['male','female'].includes(d.gender))throw Error('성별을 선택해주세요.');p.gender=d.gender;emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('updateSettings',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId||r.phase!=='lobby')throw Error('대기실에서 방장만 설정할 수 있습니다.');if(d.mode)r.mode=d.mode;if(d.liarCount)r.settings.liarCount=+d.liarCount;if(d.roundTime!==undefined)r.settings.roundTime=+d.roundTime;if(d.voteTime)r.settings.voteTime=+d.voteTime;if(d.truthLevel)r.settings.truthLevel=d.truthLevel;if(d.liarFinalGuess!==undefined)r.settings.liarFinalGuess=!!d.liarFinalGuess;if(d.liarRoleMode)r.settings.liarRoleMode=d.liarRoleMode;if(d.drawTime)r.settings.drawTime=+d.drawTime;if(d.drawRounds)r.settings.drawRounds=+d.drawRounds;if(d.rummiTurnTime)r.settings.rummiTurnTime=+d.rummiTurnTime;emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('startGame',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 시작할 수 있습니다.');const [min,max]=LIMITS[r.game];const n=active(r).length;if(n<min||n>max)throw Error(`${GAME_NAMES[r.game]}은 ${min}~${max}명으로 플레이할 수 있습니다.`);if(r.game==='liar')startLiar(r);else if(r.game==='mafia')mafiaSetup(r);else if(r.game==='truth'){if(active(r).some(p=>!p.gender&&!p.isBot))throw Error('진실게임 시작 전에 모든 플레이어가 남자/여자를 선택해야 합니다.');startTruth(r);}else if(r.game==='draw')drawSetup(r);else if(r.game==='rummi')rummiSetup(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('submitAnswer',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='liar'||r.mode!=='question'||r.phase!=='play')throw Error('지금은 답변할 수 없습니다.');if(r.submitted.includes(p.id))throw Error('이미 답변했습니다.');const v=Number(d.value);if(!Number.isFinite(v)||v<r.prompt.min||v>r.prompt.max)throw Error(`범위는 ${r.prompt.min}~${r.prompt.max}입니다.`);r.answers[p.id]=v;r.submitted.push(p.id);if(active(r).every(x=>r.submitted.includes(x.id)))revealAnswers(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('openVoting',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 투표를 시작할 수 있습니다.');if(r.game==='liar')openLiarVote(r);else if(r.game==='mafia')startMafiaVote(r);else throw Error('이 게임에서는 사용할 수 없습니다.');cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('vote',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||!p||!t)throw Error('대상을 찾을 수 없습니다.');if(!['vote','mafiaVote'].includes(r.phase))throw Error('지금은 투표 시간이 아닙니다.');if(r.votesSubmitted.includes(p.id))throw Error('이미 투표했습니다.');if(r.game==='mafia'&&!p.alive)throw Error('사망한 플레이어는 투표할 수 없습니다.');if(r.game==='mafia'&&!t.alive)throw Error('사망한 플레이어에게 투표할 수 없습니다.');r.votes[p.id]=t.id;r.votesSubmitted.push(p.id);const voters=active(r).filter(x=>r.game!=='mafia'||x.alive);if(voters.every(x=>r.votesSubmitted.includes(x.id))){r.game==='liar'?tallyLiar(r):resolveMafiaVote(r);}else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('submitLiarGuess',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.phase!=='liarGuess'||r.guessingLiarId!==s.data.playerId)throw Error('추측할 수 없습니다.');const ok=normalizeGuess(d.guess)===normalizeGuess(r.prompt.word);r.guessResult={attempted:true,guess:clean(d.guess),answer:r.prompt.word,correct:ok};clearTimer(r);scoreLiarResult(r,ok);r.phase='result';emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('truthNext',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId)startTruth(r);});
  s.on('truthReroll',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId&&r.phase==='truth'){makeTruth(r);emitRoom(r);}});
  s.on('nightAction',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||r.phase!=='mafiaNight'||!p?.alive||!t?.alive)throw Error('지금 선택할 수 없습니다.');if(r.nightSubmitted.includes(p.id))throw Error('이미 행동했습니다.');let type;if(p.role==='mafia')type='kill';else if(p.role==='doctor')type='save';else if(p.role==='police')type='inspect';else throw Error('밤 능력이 없습니다.');if(type==='inspect')r.inspections[p.id]={name:t.name,isMafia:t.role==='mafia'};else r.nightActions[p.id]={type,target:t.id};r.nightSubmitted.push(p.id);const actors=r.players.filter(x=>x.alive&&['mafia','doctor','police'].includes(x.role));if(actors.every(x=>r.nightSubmitted.includes(x.id)))resolveNight(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  // Drawing
  s.on('drawStroke',(d)=>{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='draw'||r.phase!=='drawPlay'||r.draw.drawerId!==s.data.playerId)return;const st={x1:+d.x1,y1:+d.y1,x2:+d.x2,y2:+d.y2,color:String(d.color||'#111').slice(0,20),size:clamp(+d.size||4,1,30)};r.draw.strokes.push(st);if(r.draw.strokes.length>8000)r.draw.strokes.shift();s.to(r.code).emit('drawStroke',st);});
  s.on('drawClear',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.game==='draw'&&r.phase==='drawPlay'&&r.draw.drawerId===s.data.playerId){r.draw.strokes=[];io.to(r.code).emit('canvasClear');}});
  s.on('drawUndo',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.game==='draw'&&r.phase==='drawPlay'&&r.draw.drawerId===s.data.playerId){r.draw.strokes.pop();io.to(r.code).emit('canvasSync',r.draw.strokes);}});
  s.on('drawGuess',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='draw'||r.phase!=='drawPlay'||!p)throw Error('지금은 정답을 입력할 수 없습니다.');if(p.id===r.draw.drawerId)throw Error('출제자는 정답을 입력하지 않습니다.');if(r.draw.guessedIds.includes(p.id))throw Error('이미 정답을 맞혔습니다.');const text=String(d.guess||'').trim().slice(0,30);if(!text)throw Error('정답을 입력해주세요.');const correct=normalizeGuess(text)===normalizeGuess(r.draw.prompt.word);if(correct){const rank=r.draw.guessedIds.length;const pts=Math.max(30,100-rank*15);p.score+=pts;const drawer=by(r,r.draw.drawerId);if(drawer)drawer.score+=25;r.draw.guessedIds.push(p.id);r.draw.guessFeed.push({playerId:p.id,name:p.name,text:'정답!',correct:true});const guessers=active(r).filter(x=>x.id!==r.draw.drawerId);if(guessers.every(x=>r.draw.guessedIds.includes(x.id))){emitRoom(r);finishDrawTurn(r);}else emitRoom(r);}else{r.draw.guessFeed.push({playerId:p.id,name:p.name,text,correct:false});if(r.draw.guessFeed.length>10)r.draw.guessFeed.shift();emitRoom(r);}cb?.({ok:true,correct});}catch(e){cb?.({ok:false,error:e.message});}});
  // Rummi
  s.on('rummiCommit',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),pid=s.data.playerId;if(!r||r.game!=='rummi'||r.phase!=='rummiPlay'||r.rummi.turnOrder[r.rummi.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const v=validateRummiDraft(r,pid,d);r.rummi.board=v.board;r.rummi.racks[pid]=v.rack;if(!r.rummi.registered[pid])r.rummi.registered[pid]=true;if(v.rack.length===0){clearTimer(r);r.rummi.winnerId=pid;r.phase='rummiResult';r.rummi.lastAction=`🏆 ${by(r,pid).name}님이 모든 타일을 내려놓고 승리했습니다!`;emitRoom(r);return cb?.({ok:true});}nextRummi(r,`✅ ${by(r,pid).name}님이 ${v.usedOwn.length}개 타일을 내려놓았습니다.`);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('rummiDraw',(_,cb)=>{try{const r=rooms.get(s.data.roomCode),pid=s.data.playerId;if(!r||r.game!=='rummi'||r.phase!=='rummiPlay'||r.rummi.turnOrder[r.rummi.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const t=r.rummi.pool.pop();if(t)r.rummi.racks[pid].push(t);nextRummi(r,t?`➕ ${by(r,pid).name}님이 타일 1개를 가져갔습니다.`:`📭 남은 타일이 없습니다.`);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('backToLobby',(_,cb)=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId){clearTimer(r);r.phase='lobby';r.players.forEach(p=>{p.alive=true;p.rolePublic=null});emitRoom(r);cb?.({ok:true});}});
  s.on('nextRound',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 진행할 수 있습니다.');if(r.game==='liar')startLiar(r);else if(r.game==='truth')startTruth(r);else if(r.game==='mafia')mafiaSetup(r);else if(r.game==='draw')drawSetup(r);else if(r.game==='rummi')rummiSetup(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('leaveRoom',(_,cb)=>{const r=rooms.get(s.data.roomCode),p=r&&by(r,s.data.playerId);if(r&&p){p.connected=false;if(r.hostId===p.id){const next=r.players.find(x=>x.connected&&x.id!==p.id);if(next)r.hostId=next.id;}emitRoom(r);}s.leave(s.data.roomCode);s.data.roomCode=null;s.data.playerId=null;cb?.({ok:true});});
  s.on('disconnect',()=>{const r=rooms.get(s.data.roomCode),p=r&&by(r,s.data.playerId);if(r&&p){p.connected=false;emitRoom(r);}});
});

server.listen(PORT,()=>console.log(`SOSO Party Game listening on ${PORT}`));
