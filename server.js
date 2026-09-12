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
const wordchainData = JSON.parse(fs.readFileSync(path.join(__dirname, 'data/wordchain.json')));
const WORDCHAIN_WORDS = [...new Set(wordchainData.map(x=>String(x).trim()).filter(x=>x.length>=2))];
const WORDCHAIN_SET = new Set(WORDCHAIN_WORDS);

const rooms = new Map();
const AV = ['🐶','🐱','🐰','🐻','🐼','🐨','🦊','🐯','🦁','🐸','🐵','🐧','🐥','🦄','🐙','🦖','👻','🤖','👽','🥷','🧙','🧛','🧚','🧑‍🚀','🕵️','👑','😎','🤠','🥳','😈'];
const ADMIN_PASSWORD = '4890';
const LIMITS = { liar:[3,10], mafia:[5,12], truth:[2,10], rummi:[2,4], wordchain:[2,10] };
const GAME_NAMES = { liar:'라이어게임', mafia:'마피아게임', truth:'진실게임', rummi:'루미큐브', wordchain:'끝말잇기' };
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
function clearTimer(r){ if(r.timer) clearTimeout(r.timer); if(r.nightMinTimer) clearTimeout(r.nightMinTimer); r.timer=null; r.nightMinTimer=null; r.deadline=null; }
function setTimer(r,sec,fn){ clearTimer(r); if(!sec)return; r.deadline=Date.now()+sec*1000; r.timer=setTimeout(()=>{r.timer=null;r.deadline=null;fn();},sec*1000); }

function baseSettings(){ return { liarCount:1, roundTime:120, voteTime:30, liarFinalGuess:true, liarRoleMode:'liar', truthLevel:'normal', rummiTurnTime:60, wordchainMode:'normal', wordchainTurnTime:10, wordchainLives:3, wordchainOneShot:false }; }
function newRoom(game,mode,password,p){ return { code:code(), hostId:p.id, players:[p], game, mode:mode||'normal', phase:'lobby', round:0, password:String(password||'').slice(0,24), settings:baseSettings(), submitted:[], answers:{}, votes:{}, liarIds:[], settingsVersion:1 }; }
function resetRound(r){ clearTimer(r); r.submitted=[]; r.answers={}; r.answersRevealed=false; r.votes={}; r.votesSubmitted=[]; r.voteResult=null; r.guessResult=null; r.nightActions={}; r.nightSubmitted=[]; r.inspections={}; r.discussionStarterId=null; r.discussionDirection=null; }
function resetForGameSwitch(r,game){ clearTimer(r); r.game=game; r.mode='normal'; r.phase='lobby'; r.round=0; r.players.forEach(p=>{p.alive=true;p.role=null;p.rolePublic=null;p.score=0;}); r.settings=baseSettings(); r.prompt=null; r.liarIds=[]; r.rummi=null; r.mafiaLog=[]; r.truthQuestion=null; r.truthTurnId=null; r.wordchain=null; resetRound(r); }

function publicState(r){
  const base={ code:r.code, hostId:r.hostId, game:r.game, gameName:GAME_NAMES[r.game], mode:r.mode, phase:r.phase, round:r.round,
    players:r.players.map(p=>({id:p.id,name:p.name,avatar:p.avatar,gender:p.gender||null,connected:p.connected,score:p.score,alive:p.alive,rolePublic:p.rolePublic,isBot:!!p.isBot})),
    settings:r.settings, deadline:r.deadline, submitted:r.submitted||[], answersRevealed:r.answersRevealed, answers:r.answersRevealed?r.answers:{}, votesSubmitted:r.votesSubmitted||[], voteResult:r.voteResult,
    truthTurnId:r.truthTurnId, truthQuestion:r.truthQuestion, mafiaLog:r.mafiaLog||[], nightSubmitted:r.nightSubmitted||[], mafiaRoleRevealSeq:r.mafiaRoleRevealSeq||0, nightMinEndAt:r.nightMinEndAt||null,
    discussionStarterId:r.discussionStarterId||null, discussionDirection:r.discussionDirection||null,
    promptMeta:r.game==='liar'&&r.prompt?{category:r.prompt.category,min:r.prompt.min,max:r.prompt.max}:null };
  if(r.game==='rummi' && r.rummi) Object.assign(base,{rummi:{turnPlayerId:r.rummi.turnOrder[r.rummi.turnIndex],turnNumber:r.rummi.turnNumber,board:r.rummi.board,poolCount:r.rummi.pool.length,registered:r.rummi.registered,winnerId:r.rummi.winnerId||null,lastAction:r.rummi.lastAction||'',rackCounts:Object.fromEntries(Object.entries(r.rummi.racks).map(([id,rack])=>[id,rack.length]))}});
  if(r.game==='wordchain' && r.wordchain) Object.assign(base,{wordchain:{turnPlayerId:r.wordchain.turnOrder[r.wordchain.turnIndex],turnNumber:r.wordchain.turnNumber,currentWord:r.wordchain.currentWord,required:r.wordchain.required,direction:r.wordchain.direction,lives:r.wordchain.lives,eliminated:r.wordchain.eliminated,history:r.wordchain.history.slice(-18),lastAction:r.wordchain.lastAction||'',winnerId:r.wordchain.winnerId||null,items:r.wordchain.items}});
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
      const allActors=r.players.filter(x=>x.alive&&['mafia','doctor','police'].includes(x.role));if(allActors.every(x=>r.nightSubmitted.includes(x.id)))return finishNightWhenReady(r);
    }
    if(r.game==='liar'&&r.phase==='liarGuess'&&bots.some(p=>p.id===r.guessingLiarId)){
      const ok=Math.random()<.25;r.guessResult={attempted:true,guess:ok?r.prompt.word:'모르겠어요',answer:r.prompt.word,correct:ok};clearTimer(r);scoreLiarResult(r,ok);r.phase='result';return emitRoom(r);
    }
    if(r.game==='wordchain'&&r.phase==='wordchainPlay'){
      const wc=r.wordchain,pid=wc.turnOrder[wc.turnIndex],bp=by(r,pid);if(bp?.isBot&&!wc.eliminated[pid]){const candidates=wordchainCandidates(wc.required,wc.used,r.settings.wordchainOneShot);if(candidates.length){return submitWordchain(r,pid,pick(candidates),true)}return failWordchainTurn(r,pid,'단어를 찾지 못했습니다.');}
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
      s.emit('privateData',{game:'mafia',role:p.role,alive:p.alive,roleRevealSeq:r.mafiaRoleRevealSeq||0,mafiaIds:canSeeMafia?r.players.filter(x=>x.role==='mafia').map(x=>x.id):[],mafiaNames:p.role==='mafia'?r.players.filter(x=>x.role==='mafia').map(x=>x.name):[],inspection:r.inspections?.[p.id]||null});
    }
    if(r.game==='wordchain' && r.wordchain && r.phase!=='lobby'){
      s.emit('privateData',{game:'wordchain',items:r.wordchain.items[p.id]||[]});
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
  const talkers=active(r); r.discussionStarterId=pick(talkers).id; r.discussionDirection=Math.random()<.5?'left':'right';
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
function mafiaSetup(r){
  if(active(r).length<5)throw Error('마피아게임은 최소 5명입니다.');
  resetRound(r);r.round=1;r.players.forEach(p=>{p.alive=true;p.rolePublic=null;p.score=0});
  const ps=shuffle(active(r)),mc=ps.length>=8?2:1;
  ps.forEach((p,i)=>p.role=i<mc?'mafia':i===mc?'police':i===mc+1?'doctor':'citizen');
  r.mafiaLog=[];r.day=1;r.inspections={};r.mafiaRoleRevealSeq=(r.mafiaRoleRevealSeq||0)+1;
  r.phase='mafiaRoleReveal';
  // 역할을 충분히 확인할 수 있도록 5초 동안 역할 공개 화면을 유지한 뒤 첫 밤으로 넘어갑니다.
  setTimer(r,5,()=>startMafiaNight(r));emitRoom(r);
}
function startMafiaNight(r){
  resetRound(r);r.phase='mafiaNight';r.nightStartedAt=Date.now();r.nightMinEndAt=r.nightStartedAt+30000;
  r.mafiaLog.push(`🌙 ${r.day}일차 밤이 되었습니다.`);
  // 설정한 진행 시간이 밤의 최대 시간입니다. 제한없음이면 모든 능력 수행 후(최소 30초 이후) 아침으로 넘어갑니다.
  if(r.settings.roundTime)setTimer(r,r.settings.roundTime,()=>resolveNight(r));
  emitRoom(r);
}
function finishNightWhenReady(r){
  if(r.phase!=='mafiaNight')return;
  const remain=Math.max(0,(r.nightMinEndAt||0)-Date.now());
  if(remain<=0)return resolveNight(r);
  // 모두 행동을 마쳐도 밤 시작 후 최소 30초는 유지합니다. 화면 타이머도 실제 남은 대기시간에 맞춥니다.
  clearTimer(r);r.deadline=Date.now()+remain;
  r.nightMinTimer=setTimeout(()=>{r.nightMinTimer=null;r.deadline=null;resolveNight(r);},remain);
  emitRoom(r);
}
function resolveNight(r){if(r.phase!=='mafiaNight')return;clearTimer(r);r.nightMinEndAt=null;const acts=Object.values(r.nightActions),kills=acts.filter(a=>a.type==='kill').map(a=>a.target),save=acts.find(a=>a.type==='save')?.target;let victim=null;if(kills.length){const c={};kills.forEach(x=>c[x]=(c[x]||0)+1);victim=Object.keys(c).sort((a,b)=>c[b]-c[a])[0]}if(victim&&victim!==save){const p=by(r,victim);if(p){p.alive=false;r.mafiaLog.push(`☀️ 아침이 밝았습니다. ${p.name}님이 밤에 사망했습니다. 💀`)}}else r.mafiaLog.push('☀️ 아침이 밝았습니다. 지난밤 아무도 사망하지 않았습니다.');if(checkMafiaEnd(r))return;r.phase='mafiaDay';if(r.settings.roundTime)setTimer(r,r.settings.roundTime,()=>startMafiaVote(r));emitRoom(r);}
function startMafiaVote(r){clearTimer(r);r.phase='mafiaVote';r.votes={};r.votesSubmitted=[];setTimer(r,r.settings.voteTime||30,()=>resolveMafiaVote(r));emitRoom(r);}
function resolveMafiaVote(r){if(r.phase!=='mafiaVote')return;clearTimer(r);const c={};Object.values(r.votes).forEach(x=>c[x]=(c[x]||0)+1);const m=Math.max(0,...Object.values(c));const top=Object.keys(c).filter(x=>c[x]===m&&m);if(top.length===1){const p=by(r,top[0]);if(p){p.alive=false;p.rolePublic=p.role;r.mafiaLog.push(`⚖️ 투표로 ${p.name}님이 처형되었습니다. 역할: ${ROLE_NAMES[p.role]}`)}}else r.mafiaLog.push('⚖️ 투표가 동률이라 아무도 처형되지 않았습니다.');if(checkMafiaEnd(r))return;r.day++;startMafiaNight(r);}
function checkMafiaEnd(r){const aliveP=r.players.filter(p=>p.alive),m=aliveP.filter(p=>p.role==='mafia').length,c=aliveP.length-m;if(m===0||m>=c){r.phase='mafiaResult';r.mafiaWinner=m===0?'시민팀':'마피아팀';r.mafiaLog.push(`🏆 ${r.mafiaWinner} 승리!`);r.players.forEach(p=>p.rolePublic=p.role);emitRoom(r);return true}return false;}

// ---------- Word Chain ----------
const DUEUM = {'녀':['녀','여'],'뇨':['뇨','요'],'뉴':['뉴','유'],'니':['니','이'],'랴':['랴','야'],'려':['려','여'],'례':['례','예'],'료':['료','요'],'류':['류','유'],'리':['리','이'],'라':['라','나'],'락':['락','낙'],'란':['란','난'],'람':['람','남'],'랑':['랑','낭'],'래':['래','내'],'랭':['랭','냉'],'로':['로','노'],'록':['록','녹'],'론':['론','논'],'롱':['롱','농'],'뢰':['뢰','뇌'],'루':['루','누'],'륜':['륜','윤'],'률':['률','율'],'륭':['륭','융'],'륵':['륵','늑'],'름':['름','늠'],'릉':['릉','능'],'린':['린','인'],'림':['림','임'],'립':['립','입']};
function firstChar(w){return [...w][0]||''} function lastChar(w){const a=[...w];return a[a.length-1]||''}
function allowedStarts(ch){return DUEUM[ch]||[ch]}
function wordchainCandidates(required,used,noOneShot=false){const starts=allowedStarts(required);return WORDCHAIN_WORDS.filter(w=>starts.includes(firstChar(w))&&!used.has(w)&&(!noOneShot||hasWordchainFollow(w,used)));}
function hasWordchainFollow(w,used){const last=lastChar(w),starts=allowedStarts(last);return WORDCHAIN_WORDS.some(x=>x!==w&&!used.has(x)&&starts.includes(firstChar(x)));}
function randomStartWord(){const good=WORDCHAIN_WORDS.filter(w=>hasWordchainFollow(w,new Set([w])));return pick(good.length?good:WORDCHAIN_WORDS);}
function wordchainSetup(r){resetRound(r);r.round++;const ps=shuffle(active(r));ps.forEach(p=>p.alive=true);let t=+r.settings.wordchainTurnTime||10;if(r.settings.wordchainMode==='speed')t=5;const start=randomStartWord();r.wordchain={turnOrder:ps.map(p=>p.id),turnIndex:0,turnNumber:1,direction:1,currentWord:start,required:lastChar(start),used:new Set([start]),history:[start],lives:Object.fromEntries(ps.map(p=>[p.id,+r.settings.wordchainLives||3])),eliminated:{},items:Object.fromEntries(ps.map(p=>[p.id,r.settings.wordchainMode==='item'?shuffle(['time','reverse','shield','bomb','change']).slice(0,2):[]])),shields:{},timeBonus:{},penalty:{},lastAction:`🎲 시작 단어는 '${start}'입니다.`};r.phase='wordchainPlay';startWordchainTurn(r);}
function wcAlive(r){return r.wordchain.turnOrder.filter(id=>!r.wordchain.eliminated[id]&&by(r,id)?.connected)}
function startWordchainTurn(r){clearTimer(r);const wc=r.wordchain;if(wcAlive(r).length<=1)return finishWordchain(r);let pid=wc.turnOrder[wc.turnIndex],guard=0;while((wc.eliminated[pid]||!by(r,pid)?.connected)&&guard++<wc.turnOrder.length){wc.turnIndex=(wc.turnIndex+wc.direction+wc.turnOrder.length)%wc.turnOrder.length;pid=wc.turnOrder[wc.turnIndex]}let sec=r.settings.wordchainMode==='speed'?5:(+r.settings.wordchainTurnTime||10);sec+=(wc.timeBonus[pid]||0);if(wc.penalty[pid]){sec=Math.min(sec,5);delete wc.penalty[pid]}delete wc.timeBonus[pid];setTimer(r,sec,()=>failWordchainTurn(r,pid,'시간초과!'));emitRoom(r);}
function nextWordchainTurn(r){const wc=r.wordchain;wc.turnNumber++;wc.turnIndex=(wc.turnIndex+wc.direction+wc.turnOrder.length)%wc.turnOrder.length;startWordchainTurn(r);}
function submitWordchain(r,pid,raw,isBot=false){const wc=r.wordchain;if(r.phase!=='wordchainPlay'||wc.turnOrder[wc.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const w=String(raw||'').trim().replace(/\s+/g,'');if(!w)throw Error('단어를 입력해주세요.');if(!WORDCHAIN_SET.has(w))throw Error('등록되지 않은 단어입니다. 다른 단어를 입력해보세요.');if(wc.used.has(w))throw Error('이미 나온 단어입니다.');if(!allowedStarts(wc.required).includes(firstChar(w)))throw Error(`'${wc.required}'(으)로 시작하는 단어를 입력해주세요.`);if(r.settings.wordchainOneShot&&!hasWordchainFollow(w,wc.used))throw Error('매너 모드에서는 이어갈 수 없는 한방단어를 사용할 수 없습니다.');clearTimer(r);wc.currentWord=w;wc.required=lastChar(w);wc.used.add(w);wc.history.push(w);wc.lastAction=`${isBot?'🤖 ':''}${by(r,pid)?.name} → ${w}`;nextWordchainTurn(r);}
function failWordchainTurn(r,pid,why){if(r.phase!=='wordchainPlay')return;const wc=r.wordchain;if(wc.shields[pid]){delete wc.shields[pid];wc.lastAction=`🛡️ ${by(r,pid)?.name}님이 방어로 실패를 막았습니다!`;return nextWordchainTurn(r)}wc.lives[pid]=Math.max(0,(wc.lives[pid]||1)-1);if(wc.lives[pid]<=0){wc.eliminated[pid]=true;wc.lastAction=`💀 ${by(r,pid)?.name} 탈락! · ${why}`}else wc.lastAction=`💔 ${by(r,pid)?.name} ${why} · 목숨 ${wc.lives[pid]}개`;if(wcAlive(r).length<=1)return finishWordchain(r);nextWordchainTurn(r);}
function finishWordchain(r){clearTimer(r);const alive=wcAlive(r),winner=alive[0]||r.wordchain.turnOrder.find(id=>!r.wordchain.eliminated[id]);r.wordchain.winnerId=winner||null;r.phase='wordchainResult';r.wordchain.lastAction=winner?`🏆 ${by(r,winner)?.name}님이 끝말잇기에서 승리했습니다!`:'게임 종료';emitRoom(r);}
function useWordchainItem(r,pid,item){const wc=r.wordchain;if(r.phase!=='wordchainPlay'||wc.turnOrder[wc.turnIndex]!==pid)throw Error('내 차례에만 아이템을 사용할 수 있습니다.');if(r.settings.wordchainMode!=='item')throw Error('아이템 모드가 아닙니다.');const arr=wc.items[pid]||[],i=arr.indexOf(item);if(i<0)throw Error('보유하지 않은 아이템입니다.');arr.splice(i,1);if(item==='time'){const remain=r.deadline?Math.max(1,Math.ceil((r.deadline-Date.now())/1000)):5;clearTimer(r);setTimer(r,remain+5,()=>failWordchainTurn(r,pid,'시간초과!'));wc.lastAction=`⏳ ${by(r,pid).name} +5초 사용!`;}else if(item==='reverse'){wc.direction*=-1;wc.lastAction=`🔄 ${by(r,pid).name} 방향전환!`;}else if(item==='shield'){wc.shields[pid]=true;wc.lastAction=`🛡️ ${by(r,pid).name} 방어 준비!`;}else if(item==='bomb'){let ni=(wc.turnIndex+wc.direction+wc.turnOrder.length)%wc.turnOrder.length,guard=0;while(wc.eliminated[wc.turnOrder[ni]]&&guard++<wc.turnOrder.length)ni=(ni+wc.direction+wc.turnOrder.length)%wc.turnOrder.length;wc.penalty[wc.turnOrder[ni]]=true;wc.lastAction=`💣 다음 플레이어의 제한시간이 5초가 됩니다!`;}else if(item==='change'){const letters=['가','나','다','마','바','사','아','자','차','카','타','파','하'];wc.required=pick(letters);wc.lastAction=`🔤 시작 글자가 '${wc.required}'(으)로 변경됐습니다!`;}emitRoom(r);}

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
  s.on('updateSettings',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId||r.phase!=='lobby')throw Error('대기실에서 방장만 설정할 수 있습니다.');if(d.mode)r.mode=d.mode;if(d.liarCount)r.settings.liarCount=+d.liarCount;if(d.roundTime!==undefined)r.settings.roundTime=+d.roundTime;if(d.voteTime)r.settings.voteTime=+d.voteTime;if(d.truthLevel)r.settings.truthLevel=d.truthLevel;if(d.liarFinalGuess!==undefined)r.settings.liarFinalGuess=!!d.liarFinalGuess;if(d.liarRoleMode)r.settings.liarRoleMode=d.liarRoleMode;if(d.rummiTurnTime)r.settings.rummiTurnTime=+d.rummiTurnTime;if(d.wordchainMode)r.settings.wordchainMode=d.wordchainMode;if(d.wordchainTurnTime)r.settings.wordchainTurnTime=+d.wordchainTurnTime;if(d.wordchainLives)r.settings.wordchainLives=+d.wordchainLives;if(d.wordchainOneShot!==undefined)r.settings.wordchainOneShot=!!d.wordchainOneShot;emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('startGame',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 시작할 수 있습니다.');const [min,max]=LIMITS[r.game];const n=active(r).length;if(n<min||n>max)throw Error(`${GAME_NAMES[r.game]}은 ${min}~${max}명으로 플레이할 수 있습니다.`);if(r.game==='liar')startLiar(r);else if(r.game==='mafia')mafiaSetup(r);else if(r.game==='truth'){if(active(r).some(p=>!p.gender&&!p.isBot))throw Error('진실게임 시작 전에 모든 플레이어가 남자/여자를 선택해야 합니다.');startTruth(r);}else if(r.game==='rummi')rummiSetup(r);else if(r.game==='wordchain')wordchainSetup(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('submitAnswer',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='liar'||r.mode!=='question'||r.phase!=='play')throw Error('지금은 답변할 수 없습니다.');if(r.submitted.includes(p.id))throw Error('이미 답변했습니다.');const v=Number(d.value);if(!Number.isFinite(v)||v<r.prompt.min||v>r.prompt.max)throw Error(`범위는 ${r.prompt.min}~${r.prompt.max}입니다.`);r.answers[p.id]=v;r.submitted.push(p.id);if(active(r).every(x=>r.submitted.includes(x.id)))revealAnswers(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('openVoting',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 투표를 시작할 수 있습니다.');if(r.game==='liar')openLiarVote(r);else if(r.game==='mafia')startMafiaVote(r);else throw Error('이 게임에서는 사용할 수 없습니다.');cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('vote',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||!p||!t)throw Error('대상을 찾을 수 없습니다.');if(!['vote','mafiaVote'].includes(r.phase))throw Error('지금은 투표 시간이 아닙니다.');if(r.votesSubmitted.includes(p.id))throw Error('이미 투표했습니다.');if(r.game==='mafia'&&!p.alive)throw Error('사망한 플레이어는 투표할 수 없습니다.');if(r.game==='mafia'&&!t.alive)throw Error('사망한 플레이어에게 투표할 수 없습니다.');r.votes[p.id]=t.id;r.votesSubmitted.push(p.id);const voters=active(r).filter(x=>r.game!=='mafia'||x.alive);if(voters.every(x=>r.votesSubmitted.includes(x.id))){r.game==='liar'?tallyLiar(r):resolveMafiaVote(r);}else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('submitLiarGuess',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.phase!=='liarGuess'||r.guessingLiarId!==s.data.playerId)throw Error('추측할 수 없습니다.');const ok=normalizeGuess(d.guess)===normalizeGuess(r.prompt.word);r.guessResult={attempted:true,guess:clean(d.guess),answer:r.prompt.word,correct:ok};clearTimer(r);scoreLiarResult(r,ok);r.phase='result';emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('truthNext',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId)startTruth(r);});
  s.on('truthReroll',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId&&r.phase==='truth'){makeTruth(r);emitRoom(r);}});
  s.on('nightAction',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||r.phase!=='mafiaNight'||!p?.alive||!t?.alive)throw Error('지금 선택할 수 없습니다.');if(r.nightSubmitted.includes(p.id))throw Error('이미 행동했습니다.');let type;if(p.role==='mafia')type='kill';else if(p.role==='doctor')type='save';else if(p.role==='police')type='inspect';else throw Error('밤 능력이 없습니다.');if(type==='inspect')r.inspections[p.id]={name:t.name,isMafia:t.role==='mafia'};else r.nightActions[p.id]={type,target:t.id};r.nightSubmitted.push(p.id);const actors=r.players.filter(x=>x.alive&&['mafia','doctor','police'].includes(x.role));if(actors.every(x=>r.nightSubmitted.includes(x.id)))finishNightWhenReady(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  // Word Chain
  s.on('wordchainSubmit',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='wordchain')throw Error('끝말잇기 방이 아닙니다.');submitWordchain(r,s.data.playerId,d.word);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('wordchainItem',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='wordchain')throw Error('끝말잇기 방이 아닙니다.');useWordchainItem(r,s.data.playerId,d.item);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  // Rummi
  s.on('rummiCommit',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),pid=s.data.playerId;if(!r||r.game!=='rummi'||r.phase!=='rummiPlay'||r.rummi.turnOrder[r.rummi.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const v=validateRummiDraft(r,pid,d);r.rummi.board=v.board;r.rummi.racks[pid]=v.rack;if(!r.rummi.registered[pid])r.rummi.registered[pid]=true;if(v.rack.length===0){clearTimer(r);r.rummi.winnerId=pid;r.phase='rummiResult';r.rummi.lastAction=`🏆 ${by(r,pid).name}님이 모든 타일을 내려놓고 승리했습니다!`;emitRoom(r);return cb?.({ok:true});}nextRummi(r,`✅ ${by(r,pid).name}님이 ${v.usedOwn.length}개 타일을 내려놓았습니다.`);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('rummiDraw',(_,cb)=>{try{const r=rooms.get(s.data.roomCode),pid=s.data.playerId;if(!r||r.game!=='rummi'||r.phase!=='rummiPlay'||r.rummi.turnOrder[r.rummi.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const t=r.rummi.pool.pop();if(t)r.rummi.racks[pid].push(t);nextRummi(r,t?`➕ ${by(r,pid).name}님이 타일 1개를 가져갔습니다.`:`📭 남은 타일이 없습니다.`);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('backToLobby',(_,cb)=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId){clearTimer(r);r.phase='lobby';r.players.forEach(p=>{p.alive=true;p.rolePublic=null});emitRoom(r);cb?.({ok:true});}});
  s.on('nextRound',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 진행할 수 있습니다.');if(r.game==='liar')startLiar(r);else if(r.game==='truth')startTruth(r);else if(r.game==='mafia')mafiaSetup(r);else if(r.game==='rummi')rummiSetup(r);else if(r.game==='wordchain')wordchainSetup(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('leaveRoom',(_,cb)=>{const r=rooms.get(s.data.roomCode),p=r&&by(r,s.data.playerId);if(r&&p){p.connected=false;if(r.hostId===p.id){const next=r.players.find(x=>x.connected&&x.id!==p.id);if(next)r.hostId=next.id;}emitRoom(r);}s.leave(s.data.roomCode);s.data.roomCode=null;s.data.playerId=null;cb?.({ok:true});});
  s.on('disconnect',()=>{const r=rooms.get(s.data.roomCode),p=r&&by(r,s.data.playerId);if(r&&p){p.connected=false;emitRoom(r);}});
});

server.listen(PORT,()=>console.log(`SOSO Party Game listening on ${PORT}`));
