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
const ACCOUNTS_FILE = path.join(__dirname, 'data/genius-accounts.json');
let geniusAccounts = {}; try { geniusAccounts=JSON.parse(fs.readFileSync(ACCOUNTS_FILE)); } catch {}
const saveAccounts=()=>{try{fs.writeFileSync(ACCOUNTS_FILE,JSON.stringify(geniusAccounts,null,2))}catch{}};
const hashPassword=x=>crypto.createHash('sha256').update(String(x||'')).digest('hex');

const rooms = new Map();
const AV = ['🐶','🐱','🐰','🐻','🐼','🐨','🦊','🐯','🦁','🐸','🐵','🐧','🐥','🦄','🐙','🦖','👻','🤖','👽','🥷','🧙','🧛','🧚','🧑‍🚀','🕵️','👑','😎','🤠','🥳','😈'];
const ADMIN_PASSWORD = '4890';
const LIMITS = { liar:[3,10], mafia:[5,12], truth:[2,10], rummi:[2,4], wordchain:[2,10], genius:[4,10], stockwar:[4,10], secretvault:[4,10], deathmatch:[2,2], indianpoker:[2,2] };
const GAME_NAMES = { liar:'라이어게임', mafia:'마피아게임', truth:'진실게임', rummi:'루미큐브', wordchain:'끝말잇기', genius:'지니어스게임', stockwar:'주식전쟁', secretvault:'비밀금고', deathmatch:'데스매치', indianpoker:'인디언 포커' };
const ROLE_NAMES = { mafia:'마피아', spy:'스파이', police:'경찰', doctor:'의사', soldier:'군인', reporter:'기자', politician:'정치인', terrorist:'테러리스트', citizen:'시민' };

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
function clearTimer(r){ if(r.timer) clearTimeout(r.timer); if(r.nightMinTimer) clearTimeout(r.nightMinTimer); if(r.nightHardTimer) clearTimeout(r.nightHardTimer); if(r.stepTimer) clearTimeout(r.stepTimer); r.timer=null; r.nightMinTimer=null; r.nightHardTimer=null; r.stepTimer=null; r.deadline=null; }
function setTimer(r,sec,fn){ clearTimer(r); if(!sec)return; r.deadline=Date.now()+sec*1000; r.timer=setTimeout(()=>{r.timer=null;r.deadline=null;fn();},sec*1000); }

function mafiaRolesFor(n){
  const a=[]; const add=(role,count=1)=>{for(let i=0;i<count;i++)a.push(role)};
  if(n<5)return a; add('mafia',n>=8?2:1); if(n>=10)add('spy'); add('police'); add('doctor'); if(n>=6)add('soldier'); if(n>=7)add('reporter'); if(n>=9)add('politician'); if(n>=11)add('terrorist'); while(a.length<n)add('citizen'); return a;
}
function baseSettings(){ return { liarCount:1, roundTime:120, voteTime:30, liarFinalGuess:true, liarRoleMode:'liar', truthLevel:'normal', rummiTurnTime:60, wordchainMode:'normal', wordchainTurnTime:10, wordchainLives:3, wordchainOneShot:false, geniusGame:'stockwar', deathmatchGame:'indianpoker', deathmatchGarnetBet:1, stockTradeTime:90, stockGarnetMatch:false, stockWhisperReveal:false, stockRankHidden:true }; }
function newRoom(game,mode,password,p){ return { lastActivity:Date.now(), code:code(), hostId:p.id, players:[p], game, mode:mode||'normal', phase:'lobby', round:0, password:String(password||'').slice(0,24), settings:baseSettings(), submitted:[], answers:{}, votes:{}, liarIds:[], settingsVersion:1 }; }
function resetRound(r){ clearTimer(r); r.submitted=[]; r.answers={}; r.answersRevealed=false; r.votes={}; r.votesSubmitted=[]; r.voteResult=null; r.guessResult=null; r.nightActions={}; r.nightSubmitted=[]; r.inspections={}; r.reporterUsed=r.reporterUsed||{}; r.discussionStarterId=null; r.discussionDirection=null; }
function resetForGameSwitch(r,game){ clearTimer(r); r.game=game; r.mode='normal'; r.phase='lobby'; r.round=0; r.players.forEach(p=>{p.alive=true;p.role=null;p.rolePublic=null;p.score=0;}); r.settings=baseSettings(); r.prompt=null; r.liarIds=[]; r.rummi=null; r.mafiaLog=[]; r.truthQuestion=null; r.truthTurnId=null; r.wordchain=null; r.indian=null; r.mafiaChats={team:[],dead:[]}; r.loverIds=[]; r.soldierShieldUsed={}; r.reporterUsed={}; resetRound(r); }

function publicState(r){
  const base={ code:r.code, hostId:r.hostId, game:r.game, gameName:GAME_NAMES[r.game], mode:r.mode, phase:r.phase, round:r.round,
    players:r.players.map(p=>({id:p.id,name:p.name,avatar:p.avatar,gender:p.gender||null,connected:p.connected,score:p.score,alive:p.alive,rolePublic:p.rolePublic,claimedRole:p.claimedRole||null,isBot:!!p.isBot,geniusName:p.geniusName||null,geniusGarnets:p.geniusName?(geniusAccounts[p.geniusName]?.garnets||0):null,geniusWins:p.geniusName?(geniusAccounts[p.geniusName]?.wins||0):null})),
    settings:r.settings, deadline:r.deadline, submitted:r.submitted||[], answersRevealed:r.answersRevealed, answers:r.answersRevealed?r.answers:{}, votesSubmitted:r.votesSubmitted||[], voteResult:r.voteResult,
    truthTurnId:r.truthTurnId, truthQuestion:r.truthQuestion, mafiaLog:r.mafiaLog||[], nightSubmitted:[], mafiaRoleRevealSeq:r.mafiaRoleRevealSeq||0, nightMinEndAt:r.nightMinEndAt||null,
    mafiaDealer:r.mafiaDealer||'', mafiaNightStep:r.phase==='mafiaNight'?'all':(r.mafiaNightStep||null), mafiaCandidateId:r.mafiaCandidateId||null, executeVotesSubmitted:r.executeVotesSubmitted||[], mafiaAwards:r.mafiaAwards||[],
    terroristPickId:r.terroristPickId||null, discussionStarterId:r.discussionStarterId||null, discussionDirection:r.discussionDirection||null,
    geniusGift:r.geniusGift?{winnerId:r.geniusGift.winnerId,eligibleIds:r.geniusGift.eligibleIds||[],done:!!r.geniusGift.done,recipientId:r.geniusGift.recipientId||null}:null,
    promptMeta:r.game==='liar'&&r.prompt?{category:r.prompt.category,min:r.prompt.min,max:r.prompt.max}:null };
  if(r.game==='secretvault'&&r.vault) Object.assign(base,{vault:{round:r.vault.round,requirement:r.vault.requirement,reward:r.vault.reward,dealer:r.vault.dealer,briefingReady:r.vault.briefingReady||[],proposal:r.vault.proposal?{id:r.vault.proposal.id,members:r.vault.proposal.members,splits:r.vault.proposal.splits,accepted:r.vault.proposal.accepted}:null,log:r.vault.log.slice(-8),final:r.vault.final||false,ranking:r.vault.ranking||[]}});
  if(r.game==='stockwar'&&r.stock) Object.assign(base,{stock:{round:r.stock.round,companies:r.stock.companies,news:r.stock.news,marketEvent:r.stock.marketEvent||null,phase:r.stock.phase,portfolioPublic:false,dealer:r.stock.dealer,tradeEndsAt:r.stock.tradeEndsAt||null,ranking:r.stock.ranking||[],volume:r.stock.volume||{},whaleAlerts:(r.stock.whaleAlerts||[]).slice(-5),publicAlerts:(r.stock.publicAlerts||[]).slice(-8),briefingReady:r.stock.briefingReady||[],briefingTotal:active(r).filter(x=>!x.isBot).length,auction:r.stock.auction?{active:r.stock.auction.active,endsAt:r.stock.auction.endsAt,highBid:r.stock.auction.highBid,highBidderName:r.stock.auction.highBidderName,round:r.stock.auction.round}:null,afterMarket:r.stock.afterMarket||null,garnetPot:r.stock.garnetPot||0,liveRanking:[]}});
  if(r.game==='rummi' && r.rummi) Object.assign(base,{rummi:{turnPlayerId:r.rummi.turnOrder[r.rummi.turnIndex],turnNumber:r.rummi.turnNumber,board:r.rummi.board,poolCount:r.rummi.pool.length,registered:r.rummi.registered,winnerId:r.rummi.winnerId||null,lastAction:r.rummi.lastAction||'',rackCounts:Object.fromEntries(Object.entries(r.rummi.racks).map(([id,rack])=>[id,rack.length]))}});
  if(r.game==='wordchain' && r.wordchain) Object.assign(base,{wordchain:{turnPlayerId:r.wordchain.turnOrder[r.wordchain.turnIndex],turnNumber:r.wordchain.turnNumber,currentWord:r.wordchain.currentWord,required:r.wordchain.required,direction:r.wordchain.direction,lives:r.wordchain.lives,eliminated:r.wordchain.eliminated,history:r.wordchain.history.slice(-18),lastAction:r.wordchain.lastAction||'',winnerId:r.wordchain.winnerId||null,items:r.wordchain.items,challenge:r.wordchain.challenge?{word:r.wordchain.challenge.word,submitterId:r.wordchain.challenge.submitterId,challengers:r.wordchain.challenge.challengers,expiresAt:r.wordchain.challenge.expiresAt}:null}});
  if(r.game==='indianpoker' && r.indian) Object.assign(base,{indian:{round:r.indian.round,turnPlayerId:r.indian.turnPlayerId,pot:r.indian.pot,chips:r.indian.chips,bets:r.indian.bets,currentBet:r.indian.currentBet,lastAction:r.indian.lastAction||'',showdown:r.indian.showdown||null,winnerId:r.indian.winnerId||null,briefingReady:r.indian.briefingReady||[],garnetPot:r.indian.garnetPot||0}});
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
      for(const p of voters){const targets=active(r).filter(x=>x.id!==p.id&&(r.game!=='mafia'||x.alive));if(targets.length){r.votes[p.id]=(r.game==='mafia'&&Math.random()<.12)?'abstain':pick(targets).id;r.votesSubmitted.push(p.id)}}
      const all=active(r).filter(x=>r.game!=='mafia'||x.alive);if(all.every(x=>r.votesSubmitted.includes(x.id)))return r.game==='liar'?tallyLiar(r):resolveMafiaVote(r);
    }
    if(r.game==='mafia'&&r.phase==='mafiaNight'){
      const actors=bots.filter(p=>p.alive&&!r.nightSubmitted.includes(p.id)&&(['mafia','doctor','police'].includes(p.role)||(p.role==='reporter'&&!r.reporterUsed?.[p.id])));
      for(const p of actors){
        let targets=r.players.filter(x=>x.alive&&(p.role==='doctor'||x.id!==p.id)&&(p.role!=='mafia'||!['mafia','spy'].includes(x.role)));if(!targets.length)continue;
        let t;if(p.role==='mafia'&&r.mafiaTargetId)t=by(r,r.mafiaTargetId);else t=pick(targets);
        if(p.role==='mafia'){r.mafiaTargetId=t.id;r.nightActions[p.id]={type:'kill',target:t.id}}
        else if(p.role==='police'){r.inspections[p.id]={name:t.name,isMafia:t.role==='mafia'};r.mafiaStats.investigations[p.id]=(r.mafiaStats.investigations[p.id]||0)+(t.role==='mafia'?1:0)}
        else if(p.role==='reporter'){r.nightActions[p.id]={type:'report',target:t.id};r.reporterUsed[p.id]=true}
        else r.nightActions[p.id]={type:'save',target:t.id};
        r.nightSubmitted.push(p.id)
      }
      return maybeFinishMafiaNight(r);
    }
    if(r.game==='mafia'&&r.phase==='mafiaExecuteVote'){
      for(const p of bots.filter(x=>x.alive&&!r.executeVotesSubmitted.includes(x.id))){r.executeVotes[p.id]=Math.random()<.62?'execute':'spare';r.executeVotesSubmitted.push(p.id)}
      const voters=r.players.filter(x=>x.alive);if(voters.every(x=>r.executeVotesSubmitted.includes(x.id)))return resolveMafiaExecuteVote(r);
    }
    if(r.game==='stockwar'&&r.phase==='stockBriefing'){
      for(const p of bots)if(!r.stock.briefingReady.includes(p.id))r.stock.briefingReady.push(p.id);
    }
    if(r.game==='liar'&&r.phase==='liarGuess'&&bots.some(p=>p.id===r.guessingLiarId)){
      const ok=Math.random()<.25;r.guessResult={attempted:true,guess:ok?r.prompt.word:'모르겠어요',answer:r.prompt.word,correct:ok};clearTimer(r);scoreLiarResult(r,ok);r.phase='result';return emitRoom(r);
    }
    if(r.game==='wordchain'&&r.phase==='wordchainPlay'){
      const wc=r.wordchain,pid=wc.turnOrder[wc.turnIndex],bp=by(r,pid);if(bp?.isBot&&!wc.eliminated[pid]){const candidates=wordchainCandidates(wc.required,wc.used,r.settings.wordchainOneShot);if(candidates.length){return submitWordchain(r,pid,pick(candidates),true)}return failWordchainTurn(r,pid,'단어를 찾지 못했습니다.');}
    }
    if(r.game==='stockwar'&&r.phase==='stockTrade'){
      for(const p of bots){if(r.stock.botActedRound[p.id]===r.stock.round)continue;r.stock.botActedRound[p.id]=r.stock.round;const a=r.stock.accounts[p.id],info=(r.stock.info[p.id]||[]).at(-1);let c=info?.companyId?r.stock.companies.find(x=>x.id===info.companyId):pick(r.stock.companies);if(!c)c=pick(r.stock.companies);const positive=info?.truth?.direction==='상승';if(positive&&a.cash>=c.price){const q=Math.max(1,Math.min(3,Math.floor(a.cash/c.price)));a.cash-=c.price*q;a.holdings[c.id]=(a.holdings[c.id]||0)+q;a.traded.add(c.id);r.stock.volume[c.id]=(r.stock.volume[c.id]||0)+q;r.stock.netFlow[c.id]=(r.stock.netFlow[c.id]||0)+q;r.stock.tradeLog[p.id].push({round:r.stock.round,side:'buy',companyId:c.id,company:c.name,qty:q,price:c.price,amount:c.price*q})}}
      return emitRoom(r);
    }
    if(r.game==='indianpoker'&&r.phase==='indianPlay'){
      const bp=by(r,r.indian.turnPlayerId);if(bp?.isBot){const opp=active(r).find(x=>x.id!==bp.id),seen=r.indian.cards[opp?.id]||5,toCall=Math.max(0,(r.indian.currentBet||0)-(r.indian.bets[bp.id]||0));if(seen>=8&&toCall>=2)return indianAct(r,bp.id,'fold',0,true);if(seen<=4&&r.indian.chips[bp.id]>toCall+1)return indianAct(r,bp.id,'raise',1,true);return indianAct(r,bp.id,'call',0,true)}
    }
    if(r.game==='rummi'&&r.phase==='rummiPlay'){
      const pid=r.rummi.turnOrder[r.rummi.turnIndex],bp=by(r,pid);if(bp?.isBot){const t=r.rummi.pool.pop();if(t)r.rummi.racks[pid].push(t);return nextRummi(r,t?`🤖 ${bp.name}이 타일 1개를 가져갔습니다.`:`🤖 ${bp.name}이 턴을 넘겼습니다.`)}
    }
  },700+Math.random()*900);
}
function emitRoom(r){
  r.lastActivity=Date.now();
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
      const team=['mafia','spy'].includes(p.role), canSeeMafia=team||!p.alive||r.phase==='mafiaResult';
      const loverId=(r.loverIds||[]).includes(p.id)?r.loverIds.find(x=>x!==p.id):null;
      s.emit('privateData',{game:'mafia',role:p.role,alive:p.alive,roleRevealSeq:r.mafiaRoleRevealSeq||0,mafiaIds:canSeeMafia?r.players.filter(x=>x.role==='mafia').map(x=>x.id):[],mafiaTeamIds:canSeeMafia?r.players.filter(x=>['mafia','spy'].includes(x.role)).map(x=>x.id):[],mafiaNames:team?r.players.filter(x=>['mafia','spy'].includes(x.role)).map(x=>x.name):[],allRoles:(!p.alive||r.phase==='mafiaResult')?Object.fromEntries(r.players.map(x=>[x.id,x.role])):{},inspection:r.inspections?.[p.id]||null,loverId,loverName:loverId?by(r,loverId)?.name:null,reporterUsed:!!r.reporterUsed?.[p.id],terroristCandidates:r.terroristPickId===p.id?(r.terroristCandidates||[]):[],teamChat:team?(r.mafiaChats?.team||[]):[],deadChat:!p.alive?(r.mafiaChats?.dead||[]):[],nightDone:(r.nightSubmitted||[]).includes(p.id)});
    }
    if(r.game==='wordchain' && r.wordchain && r.phase!=='lobby'){
      s.emit('privateData',{game:'wordchain',items:r.wordchain.items[p.id]||[]});
    }
    if(r.game==='secretvault' && r.vault && r.phase!=='lobby'){ const a=r.vault.accounts[p.id]; const vr=active(r).map(x=>({id:x.id,coins:r.vault.accounts[x.id]?.coins||0})).sort((x,y)=>y.coins-x.coins); s.emit('privateData',{game:'secretvault',coins:a.coins,keys:a.keys,mission:a.mission,messages:r.vault.messages[p.id]||[],decision:a.decision||null,currentRank:vr.findIndex(x=>x.id===p.id)+1}); }
    if(r.game==='stockwar' && r.stock && r.phase!=='lobby'){ const a=r.stock.accounts[p.id]||(r.stock.accounts[p.id]={cash:1000,holdings:{},traded:new Set(),loanTaken:false,debt:0,transferRound:r.stock.round,transferTotal:0,transferTo:{}});r.stock.info[p.id]=r.stock.info[p.id]||[];r.stock.messages[p.id]=r.stock.messages[p.id]||[];r.stock.contractLog[p.id]=r.stock.contractLog[p.id]||[];r.stock.tradeLog[p.id]=r.stock.tradeLog[p.id]||[];r.stock.dealerOffers[p.id]=r.stock.dealerOffers[p.id]||[]; const sr=active(r).map(x=>({id:x.id,value:stockValue(r,x.id)})).sort((x,y)=>y.value-x.value); s.emit('privateData',{game:'stockwar',cash:a.cash,holdings:a.holdings,info:r.stock.info[p.id],messages:r.stock.messages[p.id],mission:r.stock.missions?.[p.id]||null,contracts:r.stock.contractLog[p.id].slice(-20),auctionMyBid:r.stock.auction?.bids?.[p.id]||0,dealerOffers:r.stock.dealerOffers[p.id],tradeLog:r.stock.tradeLog[p.id].slice(-20),currentRank:Math.max(1,sr.findIndex(x=>x.id===p.id)+1),currentValue:stockValue(r,p.id),debt:a.debt||0,loanTaken:!!a.loanTaken,transferTotal:a.transferTotal||0,transferTo:a.transferTo||{},transferTotalLimit:200,transferPersonLimit:100}); }
    if(r.game==='rummi' && r.rummi && r.phase!=='lobby'){
      s.emit('privateData',{game:'rummi',rack:r.rummi.racks[p.id]||[],isTurn:r.rummi.turnOrder[r.rummi.turnIndex]===p.id,registered:!!r.rummi.registered[p.id]});
    }
    if(r.game==='indianpoker' && r.indian && r.phase!=='lobby'){ const opp=r.players.find(x=>x.id!==p.id); s.emit('privateData',{game:'indianpoker',opponentCard:r.indian.cards?.[opp?.id]??null,ownCard:r.phase==='indianShowdown'||r.phase==='indianResult'?r.indian.cards?.[p.id]:null}); }
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
function mafiaDealerTextForStep(step){
  return step==='mafia'?'마피아는 눈을 뜨고 제거할 사람을 선택하십시오.':
    step==='police'?'경찰은 눈을 뜨고 조사할 사람을 선택하십시오.':
    step==='doctor'?'의사는 눈을 뜨고 살릴 사람을 선택하십시오.':
    step==='reporter'?'기자는 취재할 사람을 선택하십시오.':'밤의 행동을 기다리고 있습니다.';
}
function mafiaSetup(r){
  const n=active(r).length;if(n<5)throw Error('마피아게임은 최소 5명입니다.');
  resetRound(r);r.round=1;r.players.forEach(p=>{p.alive=true;p.rolePublic=null;p.claimedRole=null;p.score=0});
  const ps=shuffle(active(r)), roles=shuffle(mafiaRolesFor(n)); ps.forEach((p,i)=>p.role=roles[i]);
  r.mafiaLog=[];r.day=1;r.inspections={};r.reporterUsed={};r.soldierShieldUsed={};r.mafiaChats={team:[],dead:[]};r.loverIds=[];r.terroristPickId=null;
  r.mafiaStats={saves:{},correctVotes:{},investigations:{}};r.mafiaAwards=[];r.mafiaRoleRevealSeq=(r.mafiaRoleRevealSeq||0)+1;
  if(n>=12){const eligible=shuffle(ps);let a=eligible[0],b=eligible.find(x=>x.id!==a.id && !(a.role==='mafia'&&x.role==='mafia'));if(b)r.loverIds=[a.id,b.id]}
  r.phase='mafiaRoleReveal';r.mafiaDealer='지금부터 마피아 게임을 시작합니다. 당신에게 주어진 역할을 확인하고 기억하십시오.';
  setTimer(r,7,()=>startMafiaNight(r));emitRoom(r);
}
function mafiaNightActors(r){return r.players.filter(x=>x.alive&&(['mafia','doctor','police'].includes(x.role)||(x.role==='reporter'&&!r.reporterUsed?.[x.id])))}
function startMafiaNight(r){
  resetRound(r);r.phase='mafiaNight';r.nightStartedAt=Date.now();r.nightMinEndAt=r.nightStartedAt+20000;r.mafiaTargetId=null;
  r.mafiaLog.push(`🌙 ${r.day}일차 밤이 되었습니다.`);
  r.mafiaNightStep='all';r.mafiaDealer='밤입니다. 능력이 있는 플레이어는 자신의 화면에서 행동을 선택하세요.';
  const maxSec=Math.max(20,+r.settings.roundTime||60);r.deadline=Date.now()+maxSec*1000;
  r.nightHardTimer=setTimeout(()=>resolveNight(r),maxSec*1000);emitRoom(r);
}
function maybeFinishMafiaNight(r){
  if(r.phase!=='mafiaNight')return;
  const actors=mafiaNightActors(r);if(!actors.length)return resolveNight(r);
  if(!actors.every(x=>r.nightSubmitted.includes(x.id)))return emitRoom(r);
  const remain=Math.max(0,(r.nightMinEndAt||0)-Date.now());
  if(remain<=0)return resolveNight(r);
  if(r.stepTimer)clearTimeout(r.stepTimer);r.stepTimer=setTimeout(()=>resolveNight(r),remain);emitRoom(r);
}
function mafiaPublicTeam(role){return ['mafia','spy'].includes(role)?'mafiaTeam':'citizenTeam'}
function killPlayer(r,p,reason){if(!p?.alive)return null;p.alive=false;p.rolePublic=mafiaPublicTeam(p.role);r.mafiaLog.push(reason);return p}
function resolveNight(r){
  if(r.phase!=='mafiaNight')return;
  if(r.nightHardTimer)clearTimeout(r.nightHardTimer);if(r.stepTimer)clearTimeout(r.stepTimer);r.nightHardTimer=null;r.stepTimer=null;r.deadline=null;r.nightMinEndAt=null;
  const acts=Object.values(r.nightActions),kills=acts.filter(a=>a.type==='kill').map(a=>a.target),saveEntry=Object.entries(r.nightActions).find(([,a])=>a.type==='save'),save=saveEntry?.[1]?.target,doctorId=saveEntry?.[0];
  const reports=acts.filter(a=>a.type==='report'); for(const a of reports){const t=by(r,a.target);if(t)r.mafiaLog.push(`📰 특종! ${t.name}님의 직업은 ${ROLE_NAMES[t.role]}입니다!`)}
  let victim=null;if(kills.length){const c={};kills.forEach(x=>c[x]=(c[x]||0)+1);victim=Object.keys(c).sort((a,b)=>c[b]-c[a])[0]}
  if(victim&&victim!==save){
    let vp=by(r,victim);const lover=(r.loverIds||[]).includes(victim)?by(r,r.loverIds.find(x=>x!==victim)):null;
    if(lover?.alive){killPlayer(r,lover,`💀 ${lover.name}님이 죽었습니다.`)}
    else if(vp?.role==='soldier'&&!r.soldierShieldUsed[vp.id]){r.soldierShieldUsed[vp.id]=true;r.mafiaLog.push('☀️ 아침이 밝았습니다. 지난밤 아무도 사망하지 않았습니다.')}
    else if(vp)killPlayer(r,vp,`☀️ 아침이 밝았습니다. ${vp.name}님이 밤에 사망했습니다. 💀`)
  }else{
    if(victim&&victim===save&&save&&doctorId){r.mafiaStats.saves[doctorId]=(r.mafiaStats.saves[doctorId]||0)+1}
    r.mafiaLog.push('☀️ 아침이 밝았습니다. 지난밤 아무도 사망하지 않았습니다.');
  }
  if(checkMafiaEnd(r))return;
  r.phase='mafiaDay';r.mafiaNightStep=null;r.mafiaDealer='아침이 밝았습니다. 지난밤의 결과를 확인하고 자유롭게 토론하십시오.';
  if(r.settings.roundTime)setTimer(r,r.settings.roundTime,()=>startMafiaVote(r));emitRoom(r)
}
function startMafiaVote(r){
  clearTimer(r);r.phase='mafiaVote';r.votes={};r.votesSubmitted=[];r.mafiaCandidateId=null;r.mafiaDealer='자유 토론이 종료되었습니다. 처형 후보를 한 명 선택하거나 기권하십시오.';
  setTimer(r,r.settings.voteTime||30,()=>resolveMafiaVote(r));emitRoom(r)
}
function startMafiaDefense(r,candidateId){
  clearTimer(r);r.mafiaCandidateId=candidateId;r.phase='mafiaDefense';const p=by(r,candidateId);
  r.mafiaDealer=`${p?.name||'처형 후보'}님에게 최후 변론 30초를 드립니다. 다른 플레이어는 변론을 들어주십시오.`;
  setTimer(r,30,()=>startMafiaExecuteVote(r));emitRoom(r)
}
function startMafiaExecuteVote(r){
  clearTimer(r);r.phase='mafiaExecuteVote';r.executeVotes={};r.executeVotesSubmitted=[];const p=by(r,r.mafiaCandidateId);
  r.mafiaDealer=`${p?.name||'후보'}님을 처형할지 최종 투표합니다. 처형 또는 살려준다를 선택하십시오.`;
  setTimer(r,20,()=>resolveMafiaExecuteVote(r));emitRoom(r)
}
function resolveMafiaVote(r){
  if(r.phase!=='mafiaVote')return;clearTimer(r);const c={};
  for(const [voter,target] of Object.entries(r.votes)){if(target==='abstain')continue;const vp=by(r,voter);c[target]=(c[target]||0)+(vp?.role==='politician'?2:1)}
  const m=Math.max(0,...Object.values(c)),top=Object.keys(c).filter(x=>c[x]===m&&m);
  for(const [voter,target] of Object.entries(r.votes)){const vp=by(r,voter),tp=by(r,target);if(vp&&tp&&['mafia','spy'].includes(tp.role)&&!['mafia','spy'].includes(vp.role))r.mafiaStats.correctVotes[voter]=(r.mafiaStats.correctVotes[voter]||0)+1}
  if(top.length===1)return startMafiaDefense(r,top[0]);
  r.mafiaLog.push(top.length?'⚖️ 투표가 동률이라 처형 후보가 정해지지 않았습니다.':'⚖️ 기권 또는 무효표로 처형 후보가 정해지지 않았습니다.');
  r.mafiaDealer='처형 후보가 정해지지 않았습니다. 잠시 후 다시 밤이 시작됩니다.';r.stepTimer=setTimeout(()=>{r.day++;startMafiaNight(r)},4500);emitRoom(r)
}
function resolveMafiaExecuteVote(r){
  if(r.phase!=='mafiaExecuteVote')return;clearTimer(r);let yes=0,no=0;
  for(const [voter,v] of Object.entries(r.executeVotes||{})){const weight=by(r,voter)?.role==='politician'?2:1;if(v==='execute')yes+=weight;else no+=weight}
  const p=by(r,r.mafiaCandidateId);
  if(p&&yes>no){
    killPlayer(r,p,`⚖️ 최종 투표 ${yes}:${no}로 ${p.name}님이 처형되었습니다. 소속: ${mafiaPublicTeam(p.role)==='mafiaTeam'?'마피아팀':'시민팀'}`);
    if(p.role==='terrorist'){
      const candidates=Object.entries(r.votes||{}).filter(([vid,t])=>t===p.id&&by(r,vid)?.alive).map(([vid])=>vid);
      if(candidates.length){r.phase='terroristPick';r.terroristPickId=p.id;r.terroristCandidates=candidates;r.deadline=Date.now()+15000;r.timer=setTimeout(()=>resolveTerrorist(r,p.id,pick(candidates)),15000);r.mafiaDealer='처형된 플레이어는 테러리스트였습니다. 함께 데려갈 플레이어를 선택합니다.';emitRoom(r);return}
    }
  }else{
    r.mafiaLog.push(`🕊️ 최종 투표 ${yes}:${no}로 ${p?.name||'후보'}님은 살아남았습니다.`);
  }
  r.mafiaCandidateId=null;r.executeVotes={};r.executeVotesSubmitted=[];
  if(checkMafiaEnd(r))return;r.day++;r.stepTimer=setTimeout(()=>startMafiaNight(r),3500);emitRoom(r)
}
function resolveTerrorist(r,pid,targetId){
  if(r.phase!=='terroristPick'||r.terroristPickId!==pid)return;clearTimer(r);const t=by(r,targetId);
  if(t?.alive)killPlayer(r,t,`💣 테러리스트가 ${t.name}님을 함께 데려갔습니다!`);
  r.terroristPickId=null;r.terroristCandidates=[];if(checkMafiaEnd(r))return;r.day++;r.stepTimer=setTimeout(()=>startMafiaNight(r),3500);emitRoom(r)
}
function mafiaBuildAwards(r){
  const out=[];
  const correct=Object.entries(r.mafiaStats?.correctVotes||{}).sort((a,b)=>b[1]-a[1])[0];if(correct&&correct[1])out.push(`🎯 명탐정 · ${by(r,correct[0])?.name||''} (${correct[1]}회)`);
  const saves=Object.entries(r.mafiaStats?.saves||{}).sort((a,b)=>b[1]-a[1])[0];if(saves&&saves[1])out.push(`💉 명의 · ${by(r,saves[0])?.name||''} (${saves[1]}회 구조)`);const inv=Object.entries(r.mafiaStats?.investigations||{}).sort((a,b)=>b[1]-a[1])[0];if(inv&&inv[1])out.push(`🚓 베테랑 경찰 · ${by(r,inv[0])?.name||''} (마피아 ${inv[1]}회 발견)`);
  const survivor=r.players.find(p=>p.alive&&p.role==='mafia');if(survivor)out.push(`🐍 연기의 신 · ${survivor.name}`);
  const sacrificed=(r.loverIds||[]).find(id=>!by(r,id)?.alive);if(sacrificed)out.push(`💘 사랑꾼 · ${by(r,sacrificed)?.name||''}`);
  return out;
}
function checkMafiaEnd(r){
  const aliveP=r.players.filter(p=>p.alive),realM=aliveP.filter(p=>p.role==='mafia').length,m=aliveP.filter(p=>['mafia','spy'].includes(p.role)).length,c=aliveP.length-m;
  if(realM===0||m>=c){clearTimer(r);r.phase='mafiaResult';r.mafiaWinner=realM===0?'시민팀':'마피아팀';r.mafiaDealer=`게임이 종료되었습니다. ${r.mafiaWinner}의 승리입니다. 모든 플레이어의 실제 직업을 공개합니다.`;r.mafiaLog.push(`🏆 ${r.mafiaWinner} 승리!`);r.players.forEach(p=>p.rolePublic=p.role);r.mafiaAwards=mafiaBuildAwards(r);emitRoom(r);return true}
  return false
}

// ---------- Word Chain ----------
const DUEUM = {'녀':['녀','여'],'뇨':['뇨','요'],'뉴':['뉴','유'],'니':['니','이'],'랴':['랴','야'],'려':['려','여'],'례':['례','예'],'료':['료','요'],'류':['류','유'],'리':['리','이'],'라':['라','나'],'락':['락','낙'],'란':['란','난'],'람':['람','남'],'랑':['랑','낭'],'래':['래','내'],'랭':['랭','냉'],'로':['로','노'],'록':['록','녹'],'론':['론','논'],'롱':['롱','농'],'뢰':['뢰','뇌'],'루':['루','누'],'륜':['륜','윤'],'률':['률','율'],'륭':['륭','융'],'륵':['륵','늑'],'름':['름','늠'],'릉':['릉','능'],'린':['린','인'],'림':['림','임'],'립':['립','입']};
function firstChar(w){return [...w][0]||''} function lastChar(w){const a=[...w];return a[a.length-1]||''}
function allowedStarts(ch){return DUEUM[ch]||[ch]}
function wordchainCandidates(required,used,noOneShot=false){const starts=allowedStarts(required);return WORDCHAIN_WORDS.filter(w=>starts.includes(firstChar(w))&&!used.has(w)&&(!noOneShot||hasWordchainFollow(w,used)));}
function hasWordchainFollow(w,used){const last=lastChar(w),starts=allowedStarts(last);return WORDCHAIN_WORDS.some(x=>x!==w&&!used.has(x)&&starts.includes(firstChar(x)));}
function randomStartWord(){const good=WORDCHAIN_WORDS.filter(w=>hasWordchainFollow(w,new Set([w])));return pick(good.length?good:WORDCHAIN_WORDS);}
function wordchainSetup(r){resetRound(r);r.round++;const ps=shuffle(active(r));ps.forEach(p=>p.alive=true);const start=randomStartWord();r.wordchain={turnOrder:ps.map(p=>p.id),turnIndex:0,turnNumber:1,direction:1,currentWord:start,required:lastChar(start),used:new Set([start]),history:[start],lives:Object.fromEntries(ps.map(p=>[p.id,+r.settings.wordchainLives||3])),eliminated:{},items:Object.fromEntries(ps.map(p=>[p.id,r.settings.wordchainMode==='item'?shuffle(['time','reverse','shield','bomb','change']).slice(0,2):[]])),shields:{},timeBonus:{},penalty:{},challenge:null,lastAction:`🎲 시작 단어는 '${start}'입니다.`};r.phase='wordchainPlay';startWordchainTurn(r);}
function wcAlive(r){return r.wordchain.turnOrder.filter(id=>!r.wordchain.eliminated[id]&&by(r,id)?.connected)}
function startWordchainTurn(r){clearTimer(r);const wc=r.wordchain;if(wcAlive(r).length<=1)return finishWordchain(r);let pid=wc.turnOrder[wc.turnIndex],guard=0;while((wc.eliminated[pid]||!by(r,pid)?.connected)&&guard++<wc.turnOrder.length){wc.turnIndex=(wc.turnIndex+wc.direction+wc.turnOrder.length)%wc.turnOrder.length;pid=wc.turnOrder[wc.turnIndex]}let sec=r.settings.wordchainMode==='speed'?5:(+r.settings.wordchainTurnTime||10);sec+=(wc.timeBonus[pid]||0);if(wc.penalty[pid]){sec=Math.min(sec,5);delete wc.penalty[pid]}delete wc.timeBonus[pid];setTimer(r,sec,()=>failWordchainTurn(r,pid,'시간초과!'));emitRoom(r);}
function nextWordchainTurn(r){const wc=r.wordchain;wc.turnNumber++;wc.turnIndex=(wc.turnIndex+wc.direction+wc.turnOrder.length)%wc.turnOrder.length;startWordchainTurn(r);}
function submitWordchain(r,pid,raw,isBot=false){const wc=r.wordchain;if(r.phase!=='wordchainPlay'||wc.turnOrder[wc.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const w=String(raw||'').trim().replace(/\s+/g,'');if(w.length<2)throw Error('두 글자 이상의 단어를 입력해주세요.');if(wc.used.has(w))throw Error('이미 나온 단어입니다.');if(!allowedStarts(wc.required).includes(firstChar(w)))throw Error(`'${wc.required}'(으)로 시작하는 단어를 입력해주세요.`);clearTimer(r);wc.currentWord=w;wc.required=lastChar(w);wc.used.add(w);wc.history.push(w);wc.challenge={word:w,submitterId:pid,challengers:[],expiresAt:Date.now()+10000};wc.lastAction=`${isBot?'🤖 ':''}${by(r,pid)?.name} → ${w} · 10초간 이의제기 가능`;nextWordchainTurn(r);}
function challengeWordchain(r,pid){const wc=r.wordchain,ch=wc?.challenge,p=by(r,pid);if(!wc||r.phase!=='wordchainPlay'||!ch||Date.now()>ch.expiresAt)throw Error('이의제기 시간이 지났습니다.');if(ch.submitterId===pid)throw Error('내 단어에는 이의제기할 수 없습니다.');if(wc.eliminated[pid]||!p?.connected)throw Error('이의제기할 수 없습니다.');if(ch.challengers.includes(pid))throw Error('이미 이의제기했습니다.');ch.challengers.push(pid);const eligible=wc.turnOrder.filter(id=>id!==ch.submitterId&&!wc.eliminated[id]&&by(r,id)?.connected);if(eligible.length&&eligible.every(id=>ch.challengers.includes(id))){const sid=ch.submitterId;wc.lives[sid]=Math.max(0,(wc.lives[sid]||1)-1);if(wc.lives[sid]<=0)wc.eliminated[sid]=true;wc.lastAction=`⚠️ 전원 이의제기 성립 · ${by(r,sid)?.name} 목숨 -1`;wc.challenge=null;if(wcAlive(r).length<=1)return finishWordchain(r);}emitRoom(r);}

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

// ---------- Secret Vault ----------
const VAULT_KEYS=['🔴','🔵','🟡','🟢','🟣'];
const VAULT_REQ=[['🔴','🔵','🟡'],['🟢','🟢','🟣','🔵'],['🔴','🟡','🟣','🟢'],['🔴','🔵','🟢','🟣'],['🟡','🟡','🔴','🔵','🟣'],['🔴','🔴','🔵','🟢','🟡','🟣']];
const VAULT_REWARD=[250,320,400,520,650,1000],VAULT_TIME=[240,300,300,360,360,480];
function vaultRoundIntermission(r,nextRound){clearTimer(r);r.phase='vaultIntermission';r.vault.dealer=`잠시 후 ROUND ${nextRound}가 시작됩니다.`;r.deadline=Date.now()+20000;setTimer(r,20,()=>vaultStartRound(r,nextRound));emitRoom(r)}
function vaultStartRound(r,nextRound){r.vault.round=nextRound;r.round=nextRound;r.vault.requirement=VAULT_REQ[nextRound-1];r.vault.reward=VAULT_REWARD[nextRound-1];r.vault.final=nextRound===6;r.vault.proposal=null;r.vault.dealer=r.vault.final?'마지막 금고입니다. 충분히 협상한 뒤 최종 계약을 완성하세요.':'새로운 금고가 공개되었습니다. 자유롭게 협상하세요.';active(r).forEach(p=>{const a=r.vault.accounts[p.id];if(nextRound>1)a.keys.push(pick(VAULT_KEYS));a.decision=null});r.phase='vaultNegotiate';setTimer(r,VAULT_TIME[nextRound-1],()=>vaultRoundTimeout(r));emitRoom(r)}
function vaultSetup(r){resetRound(r);r.geniusGift=null;r.geniusRewardsApplied=false;r.round=1;r.vault={round:1,accounts:{},messages:{},proposal:null,log:[],dealer:'각자의 비밀 열쇠를 확인하십시오. 필요한 열쇠를 모아 금고를 여세요.',requirement:VAULT_REQ[0],reward:VAULT_REWARD[0],final:false,ranking:[]};active(r).forEach((p,i)=>{r.vault.accounts[p.id]={coins:0,keys:[pick(VAULT_KEYS),pick(VAULT_KEYS)],mission:{text:i%3===0?'게임 종료까지 2개 이상의 금고에 참여하세요.':i%3===1?'한 라운드에서 150코인 이상 획득하세요.':'마지막 금고에 참여하세요.',reward:100},joined:0,decision:null};r.vault.messages[p.id]=[]});r.phase='vaultBriefing';r.vault.briefingReady=[];r.vault.dealer='룰 설명을 확인한 뒤 준비 완료를 눌러주세요. 전원이 준비하면 시작하며 최대 3분 후 자동 시작합니다.';setTimer(r,180,()=>vaultBegin(r));emitRoom(r)}
function vaultBegin(r){clearTimer(r);vaultStartRound(r,1)}
function vaultRoundTimeout(r){if(r.vault.proposal)return vaultResolve(r);r.vault.log.push(`ROUND ${r.vault.round} · 계약 없이 금고가 닫혔습니다.`);vaultNext(r)}
function vaultNext(r){clearTimer(r);if(r.vault.round>=6)return vaultFinish(r);vaultRoundIntermission(r,r.vault.round+1)}
function vaultResolve(r){const pr=r.vault.proposal;if(!pr)return vaultNext(r);const keys=pr.members.flatMap(id=>r.vault.accounts[id]?.keys||[]),need=[...r.vault.requirement];let ok=true;for(const k of need){const i=keys.indexOf(k);if(i<0){ok=false;break}keys.splice(i,1)}if(!ok){r.vault.log.push(`ROUND ${r.vault.round} · 금고 개방 실패`);return vaultNext(r)}if(r.vault.final){r.phase='vaultFinalDecision';r.vault.dealer='계약이 성립했습니다. 계약 참가자는 협력 또는 배신을 비밀리에 선택하십시오.';clearTimer(r);setTimer(r,30,()=>vaultResolveFinal(r));return emitRoom(r)}for(const id of pr.members){const a=r.vault.accounts[id];a.coins+=(pr.splits[id]||0);a.joined++}r.vault.log.push(`ROUND ${r.vault.round} · 금고 개방 성공! ${r.vault.reward}C 분배`);vaultNext(r)}
function vaultResolveFinal(r){const pr=r.vault.proposal,ds=pr.members.filter(id=>r.vault.accounts[id].decision==='betray');if(ds.length===1){for(const id of pr.members)r.vault.accounts[id].coins+=pr.splits[id]||0;r.vault.accounts[ds[0]].coins+=300;r.vault.log.push('FINAL · 단 한 명의 배신자가 추가 300C를 차지했습니다.')}else if(ds.length>=2){const coop=pr.members.filter(id=>!ds.includes(id));const each=coop.length?Math.floor(r.vault.reward/coop.length):0;coop.forEach(id=>r.vault.accounts[id].coins+=each);r.vault.log.push('FINAL · 배신자가 둘 이상이어서 배신자들은 0C, 협력자들이 상금을 나눴습니다.')}else{for(const id of pr.members)r.vault.accounts[id].coins+=pr.splits[id]||0;r.vault.log.push('FINAL · 모두 협력하여 약속대로 상금을 나눴습니다.')}vaultFinish(r)}
function awardGeniusRanking(r,ranking){
  if(r.geniusRewardsApplied)return; r.geniusRewardsApplied=true;
  const rewards=[3,1,1];
  for(let i=0;i<Math.min(3,ranking.length);i++){const p=by(r,ranking[i].id);if(p?.geniusName&&geniusAccounts[p.geniusName])geniusAccounts[p.geniusName].garnets=(geniusAccounts[p.geniusName].garnets||0)+rewards[i]}
  const winner=ranking[0]&&by(r,ranking[0].id);if(winner?.geniusName&&geniusAccounts[winner.geniusName])geniusAccounts[winner.geniusName].wins=(geniusAccounts[winner.geniusName].wins||0)+1;
  const lastId=ranking.at(-1)?.id;const eligible=ranking.map(x=>x.id).filter(id=>id!==ranking[0]?.id&&id!==lastId&&by(r,id)?.geniusName&&!by(r,id)?.isBot);
  r.geniusGift={winnerId:ranking[0]?.id||null,eligibleIds:eligible,done:eligible.length===0,recipientId:null};
  saveAccounts();
}
function vaultFinish(r){clearTimer(r);for(const p of active(r)){const a=r.vault.accounts[p.id];if((a.joined>=2)|| (r.vault.proposal?.members||[]).includes(p.id)&&a.mission.text.includes('마지막'))a.coins+=a.mission.reward}r.vault.ranking=active(r).map(p=>({id:p.id,name:p.name,coins:r.vault.accounts[p.id].coins})).sort((a,b)=>b.coins-a.coins);awardGeniusRanking(r,r.vault.ranking);r.phase='vaultFinal';r.vault.dealer='모든 금고가 닫혔습니다. 최종 자산 순위를 공개합니다.';emitRoom(r)}


// ---------- Indian Poker Deathmatch ----------
function indianSetup(r){resetRound(r);const ps=active(r);if(ps.length!==2)throw Error('인디언 포커는 정확히 2명이 필요합니다.');if(ps.some(p=>!p.isBot&&!p.geniusName))throw Error('데스매치는 실제 플레이어가 두뇌게임 프로필 로그인을 완료해야 합니다.');const bet=Math.max(1,+r.settings.deathmatchGarnetBet||1);for(const p of ps.filter(p=>!p.isBot)){const a=geniusAccounts[p.geniusName];if(!a||a.garnets<bet)throw Error(`${p.name}님의 가넷이 부족합니다. 최소 ${bet}가넷이 필요합니다.`)}for(const p of ps.filter(p=>!p.isBot))geniusAccounts[p.geniusName].garnets-=bet;saveAccounts();r.game='indianpoker';r.parentGame='deathmatch';r.round=1;r.indian={round:1,chips:Object.fromEntries(ps.map(p=>[p.id,20])),cards:{},bets:{},pot:0,currentBet:0,turnPlayerId:null,acted:[],lastAction:'룰 설명을 확인해주세요.',showdown:null,winnerId:null,briefingReady:[],garnetBet:bet,garnetPot:bet*2};r.phase='indianBriefing';setTimer(r,120,()=>indianStartRound(r));emitRoom(r)}
function indianStartRound(r){clearTimer(r);const ps=active(r);if(ps.some(p=>(r.indian.chips[p.id]||0)<=0)||r.indian.round>10)return indianFinish(r);r.round=r.indian.round;r.phase='indianPlay';r.indian.showdown=null;r.indian.pot=0;r.indian.bets={};r.indian.currentBet=1;r.indian.acted=[];const deck=shuffle([1,2,3,4,5,6,7,8,9,10,1,2,3,4,5,6,7,8,9,10]);for(const p of ps){const ante=Math.min(1,r.indian.chips[p.id]);r.indian.chips[p.id]-=ante;r.indian.bets[p.id]=ante;r.indian.pot+=ante;r.indian.cards[p.id]=deck.pop()}r.indian.turnPlayerId=ps[(r.indian.round-1)%2].id;r.indian.lastAction=`ROUND ${r.indian.round} · 상대 카드를 보고 베팅하세요.`;setTimer(r,75,()=>indianAct(r,r.indian.turnPlayerId,'fold',0,true));emitRoom(r)}
function indianAct(r,pid,action,raise=0,auto=false){if(r.game!=='indianpoker'||r.phase!=='indianPlay'||r.indian.turnPlayerId!==pid)throw Error('내 차례가 아닙니다.');const ps=active(r),me=by(r,pid),opp=ps.find(p=>p.id!==pid),b=r.indian.bets[pid]||0,toCall=Math.max(0,r.indian.currentBet-b);clearTimer(r);if(action==='fold'){r.indian.lastAction=`${me.name}님이 폴드했습니다.`;return indianResolveRound(r,opp.id,'fold')}if(action==='raise'){const maxRaise=Math.max(0,(r.indian.chips[pid]||0)-toCall),add=Math.max(1,Math.min(maxRaise,Math.floor(+raise||1)));if(maxRaise<1)throw Error('추가로 걸 수 있는 칩이 없습니다.');const cost=toCall+add;if(r.indian.chips[pid]<cost)throw Error('칩이 부족합니다.');r.indian.chips[pid]-=cost;r.indian.bets[pid]+=cost;r.indian.pot+=cost;r.indian.currentBet=r.indian.bets[pid];r.indian.acted=[pid];r.indian.lastAction=`${me.name}님이 ${add}칩을 추가로 걸었습니다.`;}else{const cost=toCall;if(r.indian.chips[pid]<cost)throw Error('콜할 칩이 부족합니다.');r.indian.chips[pid]-=cost;r.indian.bets[pid]+=cost;r.indian.pot+=cost;if(!r.indian.acted.includes(pid))r.indian.acted.push(pid);r.indian.lastAction=cost?`${me.name}님이 콜했습니다.`:`${me.name}님이 체크했습니다.`;}const matched=(r.indian.bets[pid]||0)===(r.indian.bets[opp.id]||0);if(matched&&r.indian.acted.includes(pid)&&r.indian.acted.includes(opp.id))return indianResolveRound(r,null,'showdown');r.indian.turnPlayerId=opp.id;setTimer(r,75,()=>indianAct(r,opp.id,'fold',0,true));emitRoom(r)}
function indianResolveRound(r,winnerId,reason){clearTimer(r);const ps=active(r);let win=winnerId;if(reason==='showdown'){const [a,b]=ps,ca=r.indian.cards[a.id],cb=r.indian.cards[b.id];if(ca>cb)win=a.id;else if(cb>ca)win=b.id;else win=null;}if(win)r.indian.chips[win]=(r.indian.chips[win]||0)+r.indian.pot;else{const half=Math.floor(r.indian.pot/2);ps.forEach((p,i)=>r.indian.chips[p.id]=(r.indian.chips[p.id]||0)+half+(i===0?r.indian.pot-half*2:0));}r.indian.showdown={cards:{...r.indian.cards},winnerId:win,reason};r.phase='indianShowdown';r.indian.lastAction=win?`${by(r,win)?.name}님이 ${r.indian.pot}칩을 가져갑니다.`:'무승부입니다.';setTimer(r,9,()=>{r.indian.round++;indianStartRound(r)});emitRoom(r)}
function indianFinish(r){clearTimer(r);const ps=active(r),rank=[...ps].sort((a,b)=>(r.indian.chips[b.id]||0)-(r.indian.chips[a.id]||0));r.indian.winnerId=rank[0]?.id||null;r.phase='indianResult';const win=by(r,r.indian.winnerId);if(win?.geniusName&&geniusAccounts[win.geniusName]){geniusAccounts[win.geniusName].garnets=(geniusAccounts[win.geniusName].garnets||0)+(r.indian.garnetPot||0);geniusAccounts[win.geniusName].wins=(geniusAccounts[win.geniusName].wins||0)+1;saveAccounts()}r.indian.lastAction=win?`🏆 ${win.name}님이 인디언 포커에서 승리했습니다!`:'게임 종료';emitRoom(r)}

// ---------- Stock War ----------
const STOCK_COMPANIES=[
 {id:'serim',icon:'💻',name:'세림전자',sector:'반도체·전자',stability:5,growth:3,volatility:2,desc:'안정적인 대형 전자기업'},
 {id:'hanbit',icon:'🧬',name:'한빛바이오',sector:'제약·바이오',stability:2,growth:5,volatility:5,desc:'임상 결과에 민감한 성장주'},
 {id:'mirae',icon:'⚡',name:'미래에너지',sector:'에너지',stability:3,growth:4,volatility:3,desc:'정책과 원자재 흐름에 민감'},
 {id:'star',icon:'🎤',name:'스타엔터',sector:'엔터테인먼트',stability:3,growth:4,volatility:4,desc:'흥행과 소속 아티스트 이슈에 민감'},
 {id:'neo',icon:'🎮',name:'네오게임즈',sector:'게임',stability:3,growth:5,volatility:4,desc:'신작 성과가 주가를 크게 움직임'},
 {id:'daeyang',icon:'🏗️',name:'대양건설',sector:'건설',stability:4,growth:3,volatility:3,desc:'수주와 부동산 정책에 민감'},
 {id:'seon',icon:'💊',name:'세온제약',sector:'제약',stability:3,growth:4,volatility:4,desc:'허가와 신제품 판매에 민감'},
 {id:'pixel',icon:'🕹️',name:'픽셀소프트',sector:'게임·소프트웨어',stability:2,growth:5,volatility:5,desc:'신작과 플랫폼 계약에 민감'},
 {id:'hangyeol',icon:'🍜',name:'한결푸드',sector:'식품',stability:5,growth:2,volatility:2,desc:'원재료 가격과 신제품 흥행에 민감'},
 {id:'onuri',icon:'🛒',name:'온누리유통',sector:'유통',stability:4,growth:3,volatility:3,desc:'소비심리와 점포 실적에 민감'},
 {id:'luna',icon:'🎬',name:'루나엔터',sector:'콘텐츠·엔터',stability:3,growth:4,volatility:4,desc:'콘텐츠 흥행과 계약 이슈에 민감'},
 {id:'union',icon:'🤖',name:'유니온테크',sector:'AI·로봇',stability:2,growth:5,volatility:5,desc:'기술 발표와 대형 계약에 민감'},
 {id:'green',icon:'🌿',name:'그린파워',sector:'신재생에너지',stability:3,growth:5,volatility:4,desc:'친환경 정책과 발전 수주에 민감'},
 {id:'smile',icon:'🍪',name:'미소제과',sector:'식품·소비재',stability:5,growth:2,volatility:2,desc:'원가와 히트상품에 민감'},
 {id:'medigen',icon:'🧪',name:'메디젠',sector:'바이오',stability:2,growth:5,volatility:5,desc:'연구성과와 기술수출에 민감'}
];
const STOCK_EVENTS={
 serim:[['대형 반도체 공급 계약 체결',18],['차세대 칩 수율 개선',14],['주요 고객 주문 축소',-15],['해외 공장 가동 지연',-12]],
 hanbit:[['신약 임상시험에서 긍정적 결과 발표',32],['신약 허가 심사 통과',25],['임상 결과 기대 미달',-28],['핵심 특허 분쟁 발생',-18]],
 mirae:[['정부 친환경 지원책의 직접 수혜기업 선정',24],['대형 발전 프로젝트 수주',18],['원자재 가격 급등으로 수익성 악화',-16],['지원 정책 축소 발표',-20]],
 star:[['소속 아티스트 월드투어 흥행',22],['신규 아티스트 대형 히트',17],['소속 연예인 대형 스캔들',-27],['주요 아티스트 계약 해지',-22]],
 neo:[['신작 게임 글로벌 흥행',30],['해외 퍼블리싱 계약 체결',18],['신작 평가 부진',-24],['장시간 서버 장애 발생',-15]],
 daeyang:[['대형 도시개발 사업 수주',20],['해외 플랜트 계약 체결',16],['원자재 비용 급등',-14],['핵심 공사 일정 지연',-18]],
 seon:[['신제품 판매 호조',19],['신약 허가 승인',24],['제품 회수 결정',-22],['허가 심사 지연',-15]],
 pixel:[['신작 동시접속자 기록 경신',28],['글로벌 플랫폼 독점 계약',21],['신작 흥행 부진',-25],['핵심 개발진 이탈',-17]],
 hangyeol:[['신제품 전국 품절',15],['해외 수출 계약 확대',13],['곡물 가격 급등',-12],['위생 이슈 발생',-18]],
 onuri:[['분기 매출 사상 최대',14],['온라인 배송 사업 급성장',17],['소비심리 급락',-13],['대형 점포 실적 악화',-16]],
 luna:[['신작 드라마 글로벌 1위',24],['대형 제작사와 공동제작 계약',18],['주연 배우 논란',-21],['제작비 급증',-14]],
 union:[['AI 로봇 대형 공급 계약',27],['핵심 특허 등록 성공',22],['시제품 결함 공개',-23],['대형 계약 무산',-20]],
 green:[['국가 신재생 사업 우선협상자 선정',25],['대형 태양광 단지 수주',20],['정책 보조금 축소',-19],['발전 설비 사고',-17]],
 smile:[['신제품 SNS 대히트',14],['원가 절감 성공',11],['원재료 공급 차질',-12],['대표 제품 리콜',-18]],
 medigen:[['기술수출 계약 체결',31],['연구 결과 국제학술지 게재',22],['임상 중단 발표',-30],['파트너사 계약 해지',-20]]
};
const MARKET_EVENTS=[
 {text:'정부 경기부양책 발표로 시장 전반에 매수세가 유입됩니다.',pct:5},
 {text:'금리 인상 우려로 위험자산 선호가 약해집니다.',pct:-5},
 {text:'해외 증시 강세의 영향으로 투자심리가 개선됩니다.',pct:3},
 {text:'글로벌 경기침체 우려가 커지며 시장이 위축됩니다.',pct:-4},
 {text:'별다른 시장 전체 이슈는 없습니다.',pct:0}
];
const INFO_SOURCES=[
 {name:'회사 내부자',stars:5},{name:'정부 관계자',stars:4},{name:'산업 연구소',stars:4},{name:'증권사 애널리스트',stars:3},{name:'증권가 소문',stars:2}
];
function stockValue(r,pid){const a=r.stock?.accounts?.[pid]||{cash:1000,holdings:{},debt:0};return Math.round((a.cash||0)+Object.entries(a.holdings||{}).reduce((z,[id,q])=>z+q*(r.stock.companies.find(c=>c.id===id)?.price||0),0)-(a.debt||0))}
function stockInfoCard(r,p,target,ev,index){
  const source=INFO_SOURCES[(index+p.name.length+r.stock.round)%INFO_SOURCES.length], dir=ev[1]>0?'상승':'하락', mag=Math.abs(ev[1]);
  const types=[
   `${target.name}의 다음 변동은 ${target.sector} 업종의 다른 종목보다 클 가능성이 높습니다.`,
   `${target.name}은 이번 장 마감 후 ${dir}합니다.`,
   `${target.name}의 변동폭은 약 ${Math.max(8,mag-6)}~${mag+6}% 범위로 예상됩니다.`,
   `이번 라운드의 핵심 사건은 ${target.sector} 업종에서 발생합니다.`,
   `${target.name} 관련 다음 사건은 ${ev[1]>0?'긍정적':'부정적'}인 결과로 이어질 가능성이 높습니다.`
  ];
  const tier=index%5, text=types[tier], grade=tier>=2?'특급정보':tier===1?'고급정보':'일반정보';
  return {id:uid(),round:r.stock.round,text,grade,source:source.name,reliability:source.stars,companyId:target.id,truth:{direction:dir,pct:ev[1]}};
}
function stockMission(r,p,i){const c=r.stock.companies[i%r.stock.companies.length];const list=[
 {text:`게임 종료 시 ${c.name} 주식을 5주 이상 보유하세요.`,type:'hold',companyId:c.id,target:5,reward:2},
 {text:'게임 종료 시 현금 500코인 이상을 보유하세요.',type:'cash',target:500,reward:2},
 {text:'게임 중 5개 종목을 모두 한 번 이상 거래하세요.',type:'diverse',target:5,reward:2},
 {text:'최종 자산 3위 안에 들어가세요.',type:'top3',reward:3}
 ]; return list[i%list.length]}
function stockDealer(r,text){r.stock.dealer=text;emitRoom(r)}
function stockRoundIntermission(r,nextRound){clearTimer(r);r.phase='stockIntermission';r.stock.phase='intermission';r.stock.dealer=`잠시 후 ROUND ${nextRound}가 시작됩니다.`;r.deadline=Date.now()+5000;setTimer(r,5,()=>{r.stock.round=nextRound;stockPrepareRound(r)});emitRoom(r)}
function stockSetup(r){
  resetRound(r);r.geniusGift=null;r.geniusRewardsApplied=false;r.round=1;const ps=active(r);const companies=shuffle(STOCK_COMPANIES).slice(0,5).map(c=>({...c,price:100,change:0,history:[100]}));
  r.stock={round:1,companies,accounts:{},info:{},messages:{},dealerOffers:{},contractLog:{},tradeLog:{},missions:{},volume:{},netFlow:{},whaleAlerts:[],publicAlerts:[],news:'시장이 곧 개장합니다.',dealer:'주식전쟁을 시작합니다. 모든 플레이어는 1,000코인으로 시작합니다.',phase:'briefing',tradeEndsAt:null,scenario:[],garnetPot:0,botActedRound:{},briefingReady:[]};
  const turbulentRounds=new Set(shuffle([2,3,4,5,6,7]).slice(0,2));for(let round=1;round<=8;round++){const target=pick(companies),ev=pick(STOCK_EVENTS[target.id]);let market=pick(MARKET_EVENTS);const turbulent=turbulentRounds.has(round);if(turbulent){const sign=Math.random()<.5?-1:1;market={text:sign>0?'예상 밖의 대규모 자금 유입으로 시장이 급등락합니다.':'시장 불안과 대규모 매도로 변동성이 급격히 커집니다.',pct:sign*(8+Math.floor(Math.random()*8))}}r.stock.scenario.push({round,targetId:target.id,eventText:ev[0],eventPct:Math.round(ev[1]*(turbulent?1.25:1)),market,turbulent})}
  ps.forEach((p,i)=>{r.stock.accounts[p.id]={cash:1000,holdings:{},traded:new Set(),loanTaken:false,debt:0,transferRound:1,transferTotal:0,transferTo:{}};r.stock.info[p.id]=[];r.stock.messages[p.id]=[];r.stock.dealerOffers[p.id]=[];r.stock.contractLog[p.id]=[];r.stock.tradeLog[p.id]=[];r.stock.missions[p.id]=stockMission(r,p,i)});
  if(r.settings.stockGarnetMatch){const eligible=ps.every(p=>p.geniusName&&geniusAccounts[p.geniusName]?.garnets>=1);if(eligible){for(const p of ps){geniusAccounts[p.geniusName].garnets--;r.stock.garnetPot++}saveAccounts()}else r.settings.stockGarnetMatch=false}
  r.phase='stockBriefing';r.stock.dealer='룰 설명을 확인한 뒤 준비 완료를 눌러주세요. 전원이 준비하면 시작하며, 최대 3분 후 자동 시작합니다.';setTimer(r,180,()=>stockPrepareRound(r));emitRoom(r)
}
function makeDealerOffers(r,p,target,sc,i){
  const others=shuffle(r.stock.companies.filter(c=>c.id!==target.id));
  const dir=sc.eventPct>0?'상승':'하락', marketDir=sc.market?.pct>0?'상승':sc.market?.pct<0?'하락':'중립';
  const pool=[
    {price:45,grade:'시장정보',stars:2,companyId:null,label:'시장 전체',text:`이번 라운드 시장 전체 흐름은 ${marketDir}에 가깝습니다.`},
    {price:70,grade:'업종정보',stars:3,companyId:target.id,label:target.sector,text:`이번 라운드 핵심 사건은 ${target.sector} 업종에서 발생합니다.`},
    {price:95,grade:'방향정보',stars:4,companyId:target.id,label:target.name,text:`${target.name}은 이번 장 마감 후 ${dir}합니다.`},
    {price:125,grade:'변동정보',stars:4,companyId:target.id,label:target.name,text:`${target.name}의 이번 변동폭은 약 ${Math.max(8,Math.abs(sc.eventPct)-6)}~${Math.abs(sc.eventPct)+6}% 범위입니다.`},
    {price:150,grade:'특급정보',stars:5,companyId:target.id,label:target.name,text:`${target.name}의 사건은 ${sc.eventPct>0?'강한 호재':'강한 악재'}이며, 수급에 따라 변동폭이 더 커질 수 있습니다.`},
    {price:60,grade:'비교정보',stars:3,companyId:others[0]?.id,label:others[0]?.name||'타 종목',text:`${others[0]?.name||'다른 종목'}은 이번 라운드 핵심 사건의 직접 대상이 아닙니다.`},
    {price:80,grade:'변동성정보',stars:3,companyId:null,label:'시장 변동성',text:`이번 라운드는 평소보다 변동성이 ${sc.turbulent?'높습니다':'높지 않습니다'}.`}
  ];
  return shuffle(pool).slice(0,3).map(x=>({...x,id:uid(),bought:false,round:r.stock.round}));
}
function stockPrepareRound(r){
  if(!r.stock||r.stock.round>8)return stockFinish(r);r.round=r.stock.round;const sc=r.stock.scenario[r.stock.round-1],target=r.stock.companies.find(c=>c.id===sc.targetId);r.stock.pending=sc;r.stock.volume=Object.fromEntries(r.stock.companies.map(c=>[c.id,0]));r.stock.netFlow=Object.fromEntries(r.stock.companies.map(c=>[c.id,0]));r.stock.whaleAlerts=[];r.stock.marketEvent=sc.market;
  const ps=active(r);ps.forEach((p,i)=>{const acct=r.stock.accounts[p.id]||(r.stock.accounts[p.id]={cash:1000,holdings:{},traded:new Set(),loanTaken:false,debt:0});acct.transferRound=r.stock.round;acct.transferTotal=0;acct.transferTo={};r.stock.info[p.id]=r.stock.info[p.id]||[];r.stock.messages[p.id]=r.stock.messages[p.id]||[];r.stock.contractLog[p.id]=r.stock.contractLog[p.id]||[];r.stock.tradeLog[p.id]=r.stock.tradeLog[p.id]||[];const second=r.stock.companies[(i+r.stock.round)%r.stock.companies.length];r.stock.info[p.id].push(stockInfoCard(r,p,target,[sc.eventText,sc.eventPct],i+r.stock.round));if(second&&second.id!==target.id){const src=INFO_SOURCES[(i+r.stock.round+2)%INFO_SOURCES.length];r.stock.info[p.id].push({id:uid(),round:r.stock.round,text:`${second.name}은 이번 라운드 핵심 사건의 직접 대상이 아닙니다. 이 회사의 기본 변동성은 ${second.volatility}/5입니다.`,grade:'보조정보',source:src.name,reliability:src.stars,companyId:second.id,truth:{directTarget:false}})}r.stock.dealerOffers[p.id]=makeDealerOffers(r,p,target,sc,i)});
  r.stock.news=sc.market.pct?`시장 브리핑 · ${sc.market.text}`:`${target.sector} 업종을 둘러싼 시장의 관심이 커지고 있습니다.`;
  r.stock.phase='info';r.phase='stockInfoReview';r.stock.dealer=`ROUND ${r.stock.round}. 지금부터 30초 동안 새 정보와 시장 상황을 확인하세요.`;
  setTimer(r,30,()=>stockNegotiationStart(r,target,sc));emitRoom(r)
}
function stockNegotiationStart(r,target,sc){
  if(!r.stock)return;clearTimer(r);r.stock.phase='negotiation';r.phase='stockNegotiation';r.stock.dealer=`정보 확인이 끝났습니다. 지금부터 3분 동안 밀담과 협상을 진행하고 투자 전략을 세우세요.`;
  setTimer(r,180,()=>{if([3,6].includes(r.stock.round))stockAuctionStart(r,target,sc);else stockOpenTrade(r)});emitRoom(r)
}
function stockAuctionStart(r,target,sc){
  r.stock.phase='auction';r.phase='stockAuction';r.stock.auction={active:true,round:r.stock.round,endsAt:Date.now()+60000,highBid:0,highBidderId:null,highBidderName:'없음',bids:{},info:{id:uid(),round:r.stock.round,grade:'★★★★★ 특급정보',source:'시장 내부자',reliability:5,companyId:target.id,text:`${target.name}은 이번 장 마감 후 ${sc.eventPct>0?'상승':'하락'}하며, 예상 변동폭은 약 ${Math.abs(sc.eventPct)}%입니다.`,truth:{direction:sc.eventPct>0?'상승':'하락',pct:sc.eventPct}}};
  r.stock.dealer=`특급정보 경매를 시작합니다. 1분 동안 입찰과 밀담을 진행할 수 있습니다.`;setTimer(r,60,()=>stockAuctionClose(r));emitRoom(r)
}
function stockAuctionClose(r){
  if(!r.stock?.auction?.active)return;const a=r.stock.auction;a.active=false;if(a.highBidderId){const acct=r.stock.accounts[a.highBidderId];if(acct.cash>=a.highBid){acct.cash-=a.highBid;r.stock.info[a.highBidderId].push({...a.info,id:uid(),auction:true});r.stock.news=`특급정보가 ${a.highBid}코인에 낙찰되었습니다.`}}
  r.stock.dealer=a.highBidderId?`${a.highBidderName}님이 특급정보를 ${a.highBid}코인에 낙찰받았습니다. 이제 거래를 시작합니다.`:'낙찰자가 없습니다. 이제 거래를 시작합니다.';stockOpenTrade(r)
}
function stockOpenTrade(r){r.stock.phase='trade';r.phase='stockTrade';const sec=120;r.stock.dealer=`ROUND ${r.stock.round} 시장이 열렸습니다. 지금부터 2분 동안 주식을 거래하세요.`;r.stock.tradeEndsAt=Date.now()+sec*1000;setTimer(r,sec,()=>stockClose(r));emitRoom(r)}
function stockClose(r){
  if(!r.stock||r.phase!=='stockTrade')return;clearTimer(r);const sc=r.stock.pending;for(const c of r.stock.companies){const base=c.id===sc.targetId?Math.round(sc.eventPct*1.15):Math.round(Math.random()*11-5),market=sc.market?.pct||0,flow=clamp(Math.round((r.stock.netFlow[c.id]||0)/2),-20,20),panic=sc.turbulent&&Math.random()<.35?(Math.random()<.5?-1:1)*(5+Math.floor(Math.random()*10)):0,pct=clamp(base+market+flow+panic,-65,80),old=c.price;c.price=Math.max(15,Math.round(old*(1+pct/100)));c.change=Math.round((c.price/old-1)*1000)/10;c.history.push(c.price)}const c=r.stock.companies.find(x=>x.id===sc.targetId);r.stock.news=`긴급속보 · ${c.name}: ${sc.eventText}`;r.stock.phase='result';r.phase='stockResult';r.stock.dealer=`장이 마감되었습니다. ${c.name} 관련 속보입니다. 주가 변동과 거래량을 충분히 확인하세요.`;setTimer(r,30,()=>{const next=r.stock.round+1;if(next>8)stockFinish(r);else stockRoundIntermission(r,next)});emitRoom(r)
}
function missionSuccess(r,p){const m=r.stock.missions[p.id],a=r.stock.accounts[p.id];if(!m)return false;if(m.type==='hold')return (a.holdings[m.companyId]||0)>=m.target;if(m.type==='cash')return a.cash>=m.target;if(m.type==='diverse')return a.traded?.size>=m.target;if(m.type==='top3')return (r.stock.ranking||[]).slice(0,3).some(x=>x.id===p.id);return false}
function stockDealerAnswer(r,p,q){
  const raw=String(q||'').trim(); if(!raw)return '질문을 입력해주세요.';const text=raw.replace(/\s+/g,'').toLowerCase();
  const rules=[
   [/라운드|몇판|몇장/,()=>`현재 ${r.stock.round}라운드이며 주식전쟁은 총 8라운드입니다.`],
   [/승리|우승|이기는|조건/,()=>`8라운드 종료 후 현금과 보유주식 평가액에서 부채를 뺀 순자산이 가장 높은 플레이어가 승리합니다.`],
   [/정보상점|딜러정보|정보구매|정보사/,()=>`딜러 정보상점은 매 라운드 다른 정보 3개를 제시합니다. 딜러에게 구매한 정보는 항상 진실이며 코인으로 결제합니다.`],
   [/비밀정보|개인정보/,()=>`각 플레이어는 매 라운드 서로 다른 비밀정보를 받습니다. 받은 정보는 PRIVATE TERMINAL의 내 비밀정보에서 확인할 수 있습니다.`],
   [/특급|경매|입찰/,()=>`3라운드와 6라운드에는 1분 동안 특급정보 경매가 열립니다. 가장 높은 금액을 입찰한 플레이어가 정보를 얻습니다.`],
   [/밀담|비밀대화|채팅/,()=>r.phase==='stockTrade'?'시장 거래 2분 동안은 비밀대화가 잠깁니다. 거래 전 전략·협상 시간에 밀담을 이용하세요.':'오른쪽 참가자의 대화 버튼을 누르면 해당 플레이어와 1:1 비밀대화를 할 수 있습니다.'],
   [/송금|돈보내|코인보내/,()=>`송금은 라운드당 총 200C, 같은 플레이어에게는 라운드당 최대 100C까지 가능합니다.`],
   [/대출|빚|은행/,()=>`대출은 게임당 1회, 최대 500C입니다. 최종 정산에서 원금의 120%가 부채로 차감되며 대출 사용 사실은 모두에게 공개됩니다.`],
   [/매수|사기|구매주식/,()=>r.phase==='stockTrade'?'지금 시장이 열려 있습니다. 종목별 수량을 입력하고 매수 버튼을 누르세요.':'주식 매수는 MARKET OPEN 단계에서만 가능합니다.'],
   [/매도|팔기|판매주식/,()=>r.phase==='stockTrade'?'보유수량 안에서 수량을 입력한 뒤 매도 버튼을 누르세요. 대량 매도는 해당 종목의 수급과 가격에 영향을 줄 수 있습니다.':'주식 매도는 MARKET OPEN 단계에서만 가능합니다.'],
   [/순위|몇등/,()=>`현재 당신의 순위는 ${active(r).map(x=>({id:x.id,v:stockValue(r,x.id)})).sort((a,b)=>b.v-a.v).findIndex(x=>x.id===p.id)+1}위입니다. 다른 플레이어의 순위는 공개되지 않습니다.`],
   [/시간|몇초|몇분|남았/,()=>r.deadline?`현재 단계는 약 ${Math.max(0,Math.ceil((r.deadline-Date.now())/1000))}초 남았습니다.`:'현재 단계에는 별도 카운트다운이 없습니다.'],
   [/가넷/,()=>`가넷은 두뇌게임 프로필의 영구 재화입니다. 주식전쟁 안에서 사용하는 코인과는 별개입니다.`],
   [/거짓|진짜|믿|블러핑/,()=>`딜러가 직접 판매한 정보는 진실입니다. 다른 플레이어가 말하는 정보는 시스템이 인증하지 않으므로 거짓말과 블러핑이 가능합니다.`],
   [/협상|전략/,()=>`전략·협상 단계는 3분입니다. 밀담, 송금, 정보 해석을 이용해 MARKET OPEN 전에 계획을 세우세요.`],
   [/시장거래|마켓|marketopen/,()=>`시장 거래는 2분입니다. 거래 중에는 밀담이 잠기고, 매수·매도 수급은 최종 주가에도 영향을 줄 수 있습니다.`]
  ];
  for(const [re,fn] of rules)if(re.test(text))return fn();
  const company=r.stock.companies.find(c=>text.includes(c.name.replace(/\s+/g,'').toLowerCase()));if(company)return `${company.name}의 현재 가격은 ${company.price}코인이고, 이번 라운드 변동률은 ${company.change>=0?'+':''}${company.change||0}%입니다. 미래 사건이나 숨겨진 방향은 공개할 수 없습니다.`;
  return '질문의 핵심 단어를 기준으로 규칙을 찾아 답변합니다. 라운드, 정보, 경매, 협상, 밀담, 송금, 대출, 매수·매도, 순위, 시간처럼 궁금한 규칙을 구체적으로 물어보세요.';
}
function stockFinish(r){
  clearTimer(r);for(const p of active(r)){const a=r.stock.accounts[p.id];if(a?.debt){const repay=a.debt;a.cash-=repay;a.debt=0;a.debtRepaid=repay;r.stock.contractLog[p.id].push({text:`최종 대출 상환 ${repay}C`})}}r.phase='stockFinal';r.stock.phase='final';r.stock.dealer='모든 장이 종료되었습니다. 대출 상환을 반영한 최종 자산과 시장의 진실을 공개합니다.';r.stock.ranking=active(r).map(p=>({id:p.id,name:p.name,value:stockValue(r,p.id)})).sort((a,b)=>b.value-a.value);
  const awards=[];const tradeAll=Object.entries(r.stock.tradeLog).flatMap(([pid,x])=>x.map(t=>({...t,pid,name:by(r,pid)?.name})));if(tradeAll.length){const biggest=[...tradeAll].sort((a,b)=>b.amount-a.amount)[0];awards.push(`🐋 가장 과감한 거래 · ${biggest.name} ${biggest.amount}C`)}const whisperKing=active(r).map(p=>({name:p.name,n:(r.stock.messages[p.id]||[]).filter(m=>m.own).length})).sort((a,b)=>b.n-a.n)[0];if(whisperKing)awards.push(`🤫 밀담 최다 · ${whisperKing.name} ${whisperKing.n}회`);
  r.stock.afterMarket={awards,rounds:r.stock.scenario.map(sc=>({round:sc.round,company:r.stock.companies.find(c=>c.id===sc.targetId)?.name,event:sc.eventText,pct:sc.eventPct})),whispers:r.settings.stockWhisperReveal?active(r).flatMap(p=>(r.stock.messages[p.id]||[]).filter(m=>m.own).map(m=>({from:p.name,to:by(r,m.to)?.name,text:m.text}))):[]};
  awardGeniusRanking(r,r.stock.ranking)
  for(const p of active(r)){if(p.geniusName&&geniusAccounts[p.geniusName]&&missionSuccess(r,p))geniusAccounts[p.geniusName].garnets=(geniusAccounts[p.geniusName].garnets||0)+(r.stock.missions[p.id].reward||2)}
  if(r.stock.garnetPot&&r.stock.ranking.length){let pot=r.stock.garnetPot;const shares=[Math.max(1,Math.floor(pot*.6)),Math.max(0,Math.floor(pot*.25))];shares.push(Math.max(0,pot-shares[0]-shares[1]));for(let i=0;i<Math.min(3,r.stock.ranking.length);i++){const p=by(r,r.stock.ranking[i].id);if(p?.geniusName&&geniusAccounts[p.geniusName])geniusAccounts[p.geniusName].garnets=(geniusAccounts[p.geniusName].garnets||0)+shares[i]}}
  saveAccounts();emitRoom(r)
}

io.on('connection', s => {
  s.on('geniusAuth',(d,cb)=>{try{const name=clean(d.name),pw=String(d.password||'');if(pw.length<4)throw Error('비밀번호는 4자 이상 입력해주세요.');let a=geniusAccounts[name];if(!a){a=geniusAccounts[name]={password:hashPassword(pw),garnets:1,wins:0};saveAccounts()}else if(a.password!==hashPassword(pw))throw Error('비밀번호가 올바르지 않습니다.');s.data.geniusName=name;const rr=rooms.get(s.data.roomCode),rp=rr&&by(rr,s.data.playerId);if(rp){rp.geniusName=name;if(['genius','stockwar','secretvault','deathmatch','indianpoker'].includes(rr.game)||['genius','deathmatch'].includes(rr.parentGame)){rp.name=name;rp.avatar='💎';}emitRoom(rr)}cb?.({ok:true,profile:{name,garnets:a.garnets||0,wins:a.wins||0}})}catch(e){cb?.({ok:false,error:e.message})}});

  s.on('adminLogin',(d,cb)=>{if(String(d.password||'')!==ADMIN_PASSWORD)return cb?.({ok:false,error:'관리자 비밀번호가 올바르지 않습니다.'});s.data.adminToken=uid();cb?.({ok:true,token:s.data.adminToken});});
  s.on('adminGrantGarnet',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 사용할 수 있습니다.');if(!s.data.adminToken||d.token!==s.data.adminToken)throw Error('관리자 인증이 필요합니다.');const name=clean(d.name),amount=Math.max(1,Math.min(999,Math.floor(+d.amount||1)));if(!geniusAccounts[name])throw Error('해당 닉네임의 두뇌게임 프로필을 찾을 수 없습니다.');geniusAccounts[name].garnets=(geniusAccounts[name].garnets||0)+amount;saveAccounts();emitRoom(r);cb?.({ok:true,name,amount,garnets:geniusAccounts[name].garnets});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('adminBot',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 사용할 수 있습니다.');if(!s.data.adminToken||d.token!==s.data.adminToken)throw Error('관리자 인증이 필요합니다.');if(r.phase!=='lobby')throw Error('AI 인원 변경은 대기실에서만 가능합니다.');const [min,max]=LIMITS[r.game];const add=()=>{if(r.players.length>=max)return false;r.players.push(botPlayer(r));return true};if(d.action==='add')add();else if(d.action==='min')while(r.players.length<min)add();else if(d.action==='max')while(r.players.length<max)add();else if(d.action==='clear')r.players=r.players.filter(p=>!p.isBot);else throw Error('알 수 없는 관리자 명령입니다.');emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('createRoom',(d,cb)=>{try{const game=LIMITS[d.game]?d.game:'liar';if(['genius','deathmatch'].includes(game)&&!s.data.geniusName)throw Error('GENIUS_AUTH_REQUIRED');const sid=String(d.sessionId||uid()),p=player(['genius','deathmatch'].includes(game)?s.data.geniusName:d.name,d.avatar,sid),r=newRoom(game,d.mode,d.password,p);if(['genius','deathmatch'].includes(game)){p.geniusName=s.data.geniusName;p.name=s.data.geniusName;p.avatar='💎';}rooms.set(r.code,r);bind(s,r,p);cb?.({ok:true,code:r.code,playerId:p.id,sessionId:sid});emitRoom(r);}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('joinRoom',(d,cb)=>{try{const r=rooms.get(String(d.code||'').toUpperCase());if(!r)throw Error('방을 찾을 수 없습니다.');if(['genius','deathmatch'].includes(r.game)&&!s.data.geniusName)throw Error('GENIUS_AUTH_REQUIRED');if(r.password&&r.password!==String(d.password||''))throw Error('비밀번호가 올바르지 않습니다.');const sid=String(d.sessionId||uid()),old=r.players.find(p=>p.sessionId===sid);if(old){bind(s,r,old);cb?.({ok:true,code:r.code,playerId:old.id,sessionId:sid});emitRoom(r);return;}const max=LIMITS[r.game][1];if(r.players.length>=max)throw Error(`현재 게임은 최대 ${max}명입니다.`);if(r.phase!=='lobby')throw Error('게임 진행 중에는 새로 참가할 수 없습니다.');const p=player(['genius','deathmatch'].includes(r.game)?s.data.geniusName:d.name,d.avatar,sid);if(['genius','deathmatch'].includes(r.game)){p.geniusName=s.data.geniusName;p.name=s.data.geniusName;p.avatar='💎';}r.players.push(p);bind(s,r,p);cb?.({ok:true,code:r.code,playerId:p.id,sessionId:sid});emitRoom(r);}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('resumeSession',(d,cb)=>{const r=rooms.get(String(d.code||'').toUpperCase()),p=r?.players.find(x=>x.sessionId===d.sessionId);if(!r||!p)return cb?.({ok:false});bind(s,r,p);cb?.({ok:true,code:r.code,playerId:p.id,sessionId:d.sessionId});emitRoom(r);});
  s.on('switchGame',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId||r.phase!=='lobby')throw Error('대기실에서 방장만 게임을 바꿀 수 있습니다.');const g=d.game;if(r.game==='genius')throw Error('지니어스게임 방에서는 일반 게임으로 변경할 수 없습니다.');if(r.game==='deathmatch')throw Error('데스매치 방에서는 다른 게임으로 변경할 수 없습니다.');if(g==='genius')throw Error('일반 게임방에서는 지니어스게임으로 변경할 수 없습니다. 메인화면에서 지니어스게임 방을 만들어주세요.');if(g==='deathmatch')throw Error('데스매치는 메인화면에서 로그인 후 별도 방을 만들어주세요.');if(!LIMITS[g])throw Error('지원하지 않는 게임입니다.');if(r.players.length>LIMITS[g][1])throw Error(`${GAME_NAMES[g]}은 최대 ${LIMITS[g][1]}명입니다.`);resetForGameSwitch(r,g);emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('setGender',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||!p)throw Error('플레이어를 찾을 수 없습니다.');if(!['male','female'].includes(d.gender))throw Error('성별을 선택해주세요.');p.gender=d.gender;emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('updateSettings',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId||r.phase!=='lobby')throw Error('대기실에서 방장만 설정할 수 있습니다.');if(d.mode)r.mode=d.mode;if(d.liarCount)r.settings.liarCount=+d.liarCount;if(d.roundTime!==undefined)r.settings.roundTime=+d.roundTime;if(d.voteTime)r.settings.voteTime=+d.voteTime;if(d.truthLevel)r.settings.truthLevel=d.truthLevel;if(d.liarFinalGuess!==undefined)r.settings.liarFinalGuess=!!d.liarFinalGuess;if(d.liarRoleMode)r.settings.liarRoleMode=d.liarRoleMode;if(d.rummiTurnTime)r.settings.rummiTurnTime=+d.rummiTurnTime;if(d.wordchainMode)r.settings.wordchainMode=d.wordchainMode;if(d.wordchainTurnTime)r.settings.wordchainTurnTime=+d.wordchainTurnTime;if(d.wordchainLives)r.settings.wordchainLives=+d.wordchainLives;if(d.wordchainOneShot!==undefined)r.settings.wordchainOneShot=!!d.wordchainOneShot;if(d.geniusGame)r.settings.geniusGame=d.geniusGame;if(d.deathmatchGame)r.settings.deathmatchGame=d.deathmatchGame;if(d.deathmatchGarnetBet!==undefined)r.settings.deathmatchGarnetBet=Math.max(1,Math.min(5,+d.deathmatchGarnetBet||1));if(d.stockTradeTime)r.settings.stockTradeTime=+d.stockTradeTime;if(d.stockGarnetMatch!==undefined)r.settings.stockGarnetMatch=!!d.stockGarnetMatch;if(d.stockWhisperReveal!==undefined)r.settings.stockWhisperReveal=!!d.stockWhisperReveal;if(d.stockRankHidden!==undefined)r.settings.stockRankHidden=!!d.stockRankHidden;emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('startGame',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 시작할 수 있습니다.');const [min,max]=LIMITS[r.game];const n=active(r).length;if(n<min||n>max)throw Error(`${GAME_NAMES[r.game]}은 ${min}~${max}명으로 플레이할 수 있습니다.`);if(r.game==='liar')startLiar(r);else if(r.game==='mafia')mafiaSetup(r);else if(r.game==='truth'){if(active(r).some(p=>!p.gender&&!p.isBot))throw Error('진실게임 시작 전에 모든 플레이어가 남자/여자를 선택해야 합니다.');startTruth(r);}else if(r.game==='rummi')rummiSetup(r);else if(r.game==='wordchain')wordchainSetup(r);else if(r.game==='deathmatch'){r.parentGame='deathmatch';indianSetup(r);}else if(r.game==='genius'){if(active(r).some(p=>!p.isBot&&!p.geniusName))throw Error('모든 실제 플레이어가 두뇌게임 프로필 로그인을 완료해야 합니다.');r.parentGame='genius';r.game=r.settings.geniusGame||'stockwar';if(r.game==='stockwar')stockSetup(r);else if(r.game==='secretvault')vaultSetup(r);else throw Error('선택한 지니어스게임은 아직 준비 중입니다.');}else if(r.game==='stockwar')stockSetup(r);else if(r.game==='secretvault')vaultSetup(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('submitAnswer',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='liar'||r.mode!=='question'||r.phase!=='play')throw Error('지금은 답변할 수 없습니다.');if(r.submitted.includes(p.id))throw Error('이미 답변했습니다.');const v=Number(d.value);if(!Number.isFinite(v)||v<r.prompt.min||v>r.prompt.max)throw Error(`범위는 ${r.prompt.min}~${r.prompt.max}입니다.`);r.answers[p.id]=v;r.submitted.push(p.id);if(active(r).every(x=>r.submitted.includes(x.id)))revealAnswers(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('openVoting',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 투표를 시작할 수 있습니다.');if(r.game==='liar')openLiarVote(r);else if(r.game==='mafia')startMafiaVote(r);else throw Error('이 게임에서는 사용할 수 없습니다.');cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('vote',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=d.targetId==='abstain'?null:by(r,d.targetId);if(!r||!p||(d.targetId!=='abstain'&&!t))throw Error('대상을 찾을 수 없습니다.');if(!['vote','mafiaVote'].includes(r.phase))throw Error('지금은 투표 시간이 아닙니다.');if(r.votesSubmitted.includes(p.id))throw Error('이미 투표했습니다.');if(r.game==='mafia'&&!p.alive)throw Error('사망한 플레이어는 투표할 수 없습니다.');if(r.game==='mafia'&&t&&!t.alive)throw Error('사망한 플레이어에게 투표할 수 없습니다.');r.votes[p.id]=d.targetId==='abstain'?'abstain':t.id;r.votesSubmitted.push(p.id);const voters=active(r).filter(x=>r.game!=='mafia'||x.alive);if(voters.every(x=>r.votesSubmitted.includes(x.id))){r.game==='liar'?tallyLiar(r):resolveMafiaVote(r);}else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('submitLiarGuess',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.phase!=='liarGuess'||r.guessingLiarId!==s.data.playerId)throw Error('추측할 수 없습니다.');const ok=normalizeGuess(d.guess)===normalizeGuess(r.prompt.word);r.guessResult={attempted:true,guess:clean(d.guess),answer:r.prompt.word,correct:ok};clearTimer(r);scoreLiarResult(r,ok);r.phase='result';emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('truthNext',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId)startTruth(r);});
  s.on('truthReroll',()=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId&&r.phase==='truth'){makeTruth(r);emitRoom(r);}});
  s.on('nightAction',(d,cb)=>{try{
    const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);
    if(!r||r.phase!=='mafiaNight'||!p?.alive||!t?.alive)throw Error('지금 선택할 수 없습니다.');
    if(!['mafia','doctor','police','reporter'].includes(p.role))throw Error('밤 능력이 없습니다.');
    if(p.role==='reporter'&&r.reporterUsed?.[p.id])throw Error('기자 능력은 이미 사용했습니다.');
    if(r.nightSubmitted.includes(p.id))throw Error('이미 행동했습니다.');
    let type;
    if(p.role==='mafia')type='kill';else if(p.role==='doctor')type='save';else if(p.role==='police')type='inspect';else if(p.role==='reporter'&&!r.reporterUsed?.[p.id])type='report';else throw Error('밤 능력이 없습니다.');
    if(type!=='save'&&t.id===p.id)throw Error('자기 자신은 선택할 수 없습니다.');
    if(type==='kill'&&['mafia','spy'].includes(t.role))throw Error('마피아팀은 공격할 수 없습니다.');
    if(type==='kill'&&r.mafiaTargetId&&r.mafiaTargetId!==t.id)throw Error('마피아팀이 같은 대상을 선택해야 합니다. 비밀채팅으로 합의해주세요.');
    if(type==='kill'){r.mafiaTargetId=t.id;r.nightActions[p.id]={type:'kill',target:t.id}}
    else if(type==='inspect'){r.inspections[p.id]={name:t.name,isMafia:t.role==='mafia'};r.mafiaStats.investigations[p.id]=(r.mafiaStats.investigations[p.id]||0)+(t.role==='mafia'?1:0)}
    else {r.nightActions[p.id]={type,target:t.id};if(type==='report')r.reporterUsed[p.id]=true}
    r.nightSubmitted.push(p.id);maybeFinishMafiaNight(r);cb?.({ok:true});
  }catch(e){cb?.({ok:false,error:e.message});}});
  s.on('stockBriefingReady',(_,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.phase!=='stockBriefing'||!p)throw Error('지금은 브리핑 단계가 아닙니다.');r.stock.briefingReady=r.stock.briefingReady||[];if(!r.stock.briefingReady.includes(p.id))r.stock.briefingReady.push(p.id);const ready=active(r).filter(x=>!x.isBot).every(x=>r.stock.briefingReady.includes(x.id));if(ready){clearTimer(r);stockPrepareRound(r)}else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockDealerAsk',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='stockwar'||!p)throw Error('주식전쟁에서만 질문할 수 있습니다.');cb?.({ok:true,answer:stockDealerAnswer(r,p,d.question)});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockTrade',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.phase!=='stockTrade'||!p)throw Error('지금은 거래할 수 없습니다.');const a=r.stock.accounts[p.id],c=r.stock.companies.find(x=>x.id===d.companyId),q=Math.max(1,Math.min(99,+d.qty||1));if(!c)throw Error('종목을 찾을 수 없습니다.');const amount=c.price*q;if(d.side==='buy'){if(a.cash<amount)throw Error('코인이 부족합니다.');a.cash-=amount;a.holdings[c.id]=(a.holdings[c.id]||0)+q;r.stock.netFlow[c.id]=(r.stock.netFlow[c.id]||0)+q}else{if((a.holdings[c.id]||0)<q)throw Error('보유 수량이 부족합니다.');a.holdings[c.id]-=q;a.cash+=amount;r.stock.netFlow[c.id]=(r.stock.netFlow[c.id]||0)-q}a.traded.add(c.id);r.stock.volume[c.id]=(r.stock.volume[c.id]||0)+q;r.stock.tradeLog[p.id].push({round:r.stock.round,side:d.side,companyId:c.id,company:c.name,qty:q,price:c.price,amount});if(amount>=250){r.stock.whaleAlerts.push({text:`익명의 투자자가 ${c.name}을(를) 대량 ${d.side==='buy'?'매수':'매도'}했습니다.`,at:Date.now()});r.stock.whaleAlerts=r.stock.whaleAlerts.slice(-5)}emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockWhisper',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||r.game!=='stockwar'||!p||!t)throw Error('대상을 찾을 수 없습니다.');if(r.phase==='stockTrade')throw Error('시장 거래 중에는 비밀대화를 사용할 수 없습니다.');const text=String(d.text||'').trim().slice(0,160);if(!text)throw Error('메시지를 입력하세요.');r.stock.messages[p.id].push({from:p.id,to:t.id,name:p.name,text,own:true});r.stock.messages[t.id].push({from:p.id,to:t.id,name:p.name,text,own:false});r.stock.messages[p.id]=r.stock.messages[p.id].slice(-40);r.stock.messages[t.id]=r.stock.messages[t.id].slice(-40);emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockAuctionBid',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.phase!=='stockAuction'||!r.stock?.auction?.active||!p)throw Error('지금은 경매 시간이 아닙니다.');const bid=Math.floor(+d.amount||0),a=r.stock.accounts[p.id];if(bid<=r.stock.auction.highBid)throw Error('현재 최고 입찰가보다 높게 입찰해주세요.');if(bid>a.cash)throw Error('보유 코인이 부족합니다.');r.stock.auction.highBid=bid;r.stock.auction.highBidderId=p.id;r.stock.auction.highBidderName=p.name;r.stock.auction.bids[p.id]=bid;emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockTransferCoin',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||r.game!=='stockwar'||!p||!t||p.id===t.id)throw Error('대상을 찾을 수 없습니다.');const amount=Math.floor(+d.amount||0);if(amount<1)throw Error('금액을 입력해주세요.');const a=r.stock.accounts[p.id],b=r.stock.accounts[t.id];if(a.transferRound!==r.stock.round){a.transferRound=r.stock.round;a.transferTotal=0;a.transferTo={}}const perLimit=100,totalLimit=200,usedTo=a.transferTo?.[t.id]||0;if(usedTo+amount>perLimit)throw Error(`한 라운드에 한 사람에게 최대 ${perLimit}코인까지 보낼 수 있습니다. 남은 한도 ${Math.max(0,perLimit-usedTo)}C`);if((a.transferTotal||0)+amount>totalLimit)throw Error(`한 라운드 총 송금 한도는 ${totalLimit}코인입니다. 남은 한도 ${Math.max(0,totalLimit-(a.transferTotal||0))}C`);if(a.cash<amount)throw Error('코인이 부족합니다.');a.cash-=amount;b.cash+=amount;a.transferTotal=(a.transferTotal||0)+amount;a.transferTo=a.transferTo||{};a.transferTo[t.id]=usedTo+amount;r.stock.contractLog[p.id].push({text:`${t.name}에게 ${amount}코인 송금`});r.stock.contractLog[t.id].push({text:`${p.name}에게서 ${amount}코인 수령`});emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockBuyDealerInfo',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='stockwar'||!p)throw Error('주식전쟁 방이 아닙니다.');if(!['stockInfoReview','stockNegotiation','stockAuction','stockTrade'].includes(r.phase))throw Error('지금은 정보를 구매할 수 없습니다.');const offer=(r.stock.dealerOffers?.[p.id]||[]).find(x=>x.id===d.offerId);if(!offer||offer.bought)throw Error('구매할 수 없는 정보입니다.');const a=r.stock.accounts[p.id];if(a.cash<offer.price)throw Error('코인이 부족합니다.');a.cash-=offer.price;offer.bought=true;r.stock.info[p.id].push({id:uid(),round:r.stock.round,text:offer.text,grade:`딜러 ${offer.grade}`,source:'공식 딜러',reliability:offer.stars,companyId:offer.companyId,dealerBought:true});r.stock.contractLog[p.id].push({text:`딜러 ${offer.grade} 구매 · ${offer.price}코인`});emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('vaultBriefingReady',(_,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='secretvault'||r.phase!=='vaultBriefing'||!p)throw Error('지금은 준비 단계가 아닙니다.');r.vault.briefingReady=r.vault.briefingReady||[];if(!r.vault.briefingReady.includes(p.id))r.vault.briefingReady.push(p.id);const humans=active(r).filter(x=>!x.isBot);if(humans.every(x=>r.vault.briefingReady.includes(x.id)))vaultBegin(r);else emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('vaultWhisper',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId),t=by(r,d.targetId);if(!r||r.game!=='secretvault'||!p||!t)throw Error('대상을 찾을 수 없습니다.');const text=String(d.text||'').trim().slice(0,160);if(!text)throw Error('메시지를 입력하세요.');r.vault.messages[p.id].push({name:p.name,to:t.name,text,own:true});r.vault.messages[t.id].push({name:p.name,to:t.name,text,own:false});emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('stockLoan',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='stockwar'||!p)throw Error('주식전쟁에서만 대출할 수 있습니다.');if(['stockBriefing','stockFinal'].includes(r.phase))throw Error('지금은 대출할 수 없습니다.');const a=r.stock.accounts[p.id];if(a.loanTaken)throw Error('대출은 게임당 한 번만 가능합니다.');const amount=Math.max(1,Math.min(500,Math.floor(+d.amount||0)));if(!amount)throw Error('대출 금액을 입력해주세요.');a.cash+=amount;a.loanTaken=true;a.debt=Math.ceil(amount*1.2);r.stock.publicAlerts=r.stock.publicAlerts||[];r.stock.publicAlerts.push({text:`${p.name}님이 신용대출을 이용했습니다.`,at:Date.now()});r.stock.publicAlerts=r.stock.publicAlerts.slice(-8);r.stock.contractLog[p.id].push({text:`신용대출 ${amount}C · 최종 상환 ${a.debt}C`});emitRoom(r);cb?.({ok:true,debt:a.debt})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('geniusGiftGarnet',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||!p||!r.geniusGift||r.geniusGift.done)throw Error('지금은 가넷을 선물할 수 없습니다.');if(r.geniusGift.winnerId!==p.id)throw Error('1위 플레이어만 선택할 수 있습니다.');const t=by(r,d.targetId);if(!t||!r.geniusGift.eligibleIds.includes(t.id)||!t.geniusName||!geniusAccounts[t.geniusName])throw Error('선물할 수 없는 플레이어입니다.');geniusAccounts[t.geniusName].garnets=(geniusAccounts[t.geniusName].garnets||0)+1;r.geniusGift.done=true;r.geniusGift.recipientId=t.id;saveAccounts();emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('vaultPropose',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='secretvault'||r.phase!=='vaultNegotiate')throw Error('지금은 계약할 수 없습니다.');const members=[...new Set((d.members||[]).filter(id=>by(r,id)))];if(!members.includes(p.id))members.push(p.id);if(members.length<2)throw Error('2명 이상 선택하세요.');const each=Math.floor(r.vault.reward/members.length),splits=Object.fromEntries(members.map((id,i)=>[id,i===0?r.vault.reward-each*(members.length-1):each]));r.vault.proposal={id:uid(),members,splits,accepted:[p.id]};r.vault.dealer=`${p.name}님이 금고 개방 계약을 제안했습니다. 참가자는 수락 여부를 결정하십시오.`;emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('vaultAccept',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),pr=r?.vault?.proposal,p=by(r,s.data.playerId);if(!pr||!p||!pr.members.includes(p.id))throw Error('참여 중인 계약이 없습니다.');if(!pr.accepted.includes(p.id))pr.accepted.push(p.id);if(pr.members.every(id=>pr.accepted.includes(id)))vaultResolve(r);else emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('vaultDecision',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.phase!=='vaultFinalDecision'||!r.vault.proposal.members.includes(p.id))throw Error('선택할 수 없습니다.');r.vault.accounts[p.id].decision=d.choice==='betray'?'betray':'cooperate';if(r.vault.proposal.members.every(id=>r.vault.accounts[id].decision))vaultResolveFinal(r);else emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('endGame',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 게임을 종료할 수 있습니다.');clearTimer(r);clearTimeout(r.botTimer);if(r.parentGame==='genius'||['stockwar','secretvault'].includes(r.game)){r.game='genius';r.parentGame=null;r.stock=null;r.vault=null;r.vault=null;}else if(r.parentGame==='deathmatch'||r.game==='indianpoker'){r.game='deathmatch';r.parentGame=null;r.indian=null;}r.phase='lobby';r.round=0;r.geniusGift=null;r.geniusRewardsApplied=false;r.players.forEach(p=>{p.alive=true;p.role=null;p.rolePublic=null;p.claimedRole=null});emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('kickPlayer',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 내보낼 수 있습니다.');if(d.playerId===r.hostId)throw Error('방장은 내보낼 수 없습니다.');const p=by(r,d.playerId);if(!p)throw Error('플레이어를 찾을 수 없습니다.');const ss=sock(p);if(ss){ss.emit('kicked');ss.leave(r.code);ss.data.roomCode=null;ss.data.playerId=null}r.players=r.players.filter(x=>x.id!==p.id);emitRoom(r);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  // Word Chain
  s.on('wordchainSubmit',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='wordchain')throw Error('끝말잇기 방이 아닙니다.');submitWordchain(r,s.data.playerId,d.word);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('wordchainItem',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='wordchain')throw Error('끝말잇기 방이 아닙니다.');useWordchainItem(r,s.data.playerId,d.item);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('wordchainChallenge',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='wordchain')throw Error('끝말잇기 방이 아닙니다.');challengeWordchain(r,s.data.playerId);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('indianBriefingReady',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='indianpoker'||r.phase!=='indianBriefing')throw Error('룰 설명 단계가 아닙니다.');if(!r.indian.briefingReady.includes(s.data.playerId))r.indian.briefingReady.push(s.data.playerId);const humans=active(r).filter(p=>!p.isBot);if(humans.every(p=>r.indian.briefingReady.includes(p.id)))indianStartRound(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('indianAction',(d,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.game!=='indianpoker')throw Error('인디언 포커 방이 아닙니다.');indianAct(r,s.data.playerId,d.action,d.raise);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  // Rummi
  s.on('rummiCommit',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),pid=s.data.playerId;if(!r||r.game!=='rummi'||r.phase!=='rummiPlay'||r.rummi.turnOrder[r.rummi.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const v=validateRummiDraft(r,pid,d);r.rummi.board=v.board;r.rummi.racks[pid]=v.rack;if(!r.rummi.registered[pid])r.rummi.registered[pid]=true;if(v.rack.length===0){clearTimer(r);r.rummi.winnerId=pid;r.phase='rummiResult';r.rummi.lastAction=`🏆 ${by(r,pid).name}님이 모든 타일을 내려놓고 승리했습니다!`;emitRoom(r);return cb?.({ok:true});}nextRummi(r,`✅ ${by(r,pid).name}님이 ${v.usedOwn.length}개 타일을 내려놓았습니다.`);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('rummiDraw',(_,cb)=>{try{const r=rooms.get(s.data.roomCode),pid=s.data.playerId;if(!r||r.game!=='rummi'||r.phase!=='rummiPlay'||r.rummi.turnOrder[r.rummi.turnIndex]!==pid)throw Error('내 차례가 아닙니다.');const t=r.rummi.pool.pop();if(t)r.rummi.racks[pid].push(t);nextRummi(r,t?`➕ ${by(r,pid).name}님이 타일 1개를 가져갔습니다.`:`📭 남은 타일이 없습니다.`);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('backToLobby',(_,cb)=>{const r=rooms.get(s.data.roomCode);if(r&&r.hostId===s.data.playerId){clearTimer(r);if(r.parentGame==='genius'){r.game='genius';r.parentGame=null;r.stock=null;r.vault=null;}else if(r.parentGame==='deathmatch'){r.game='deathmatch';r.parentGame=null;r.indian=null;}r.phase='lobby';r.players.forEach(p=>{p.alive=true;p.role=null;p.rolePublic=null;p.claimedRole=null});r.loverIds=[];r.mafiaChats={team:[],dead:[]};emitRoom(r);cb?.({ok:true});}});
  s.on('mafiaClaim',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='mafia'||!p?.alive)throw Error('지금은 직업 주장을 바꿀 수 없습니다.');const allowed=['','citizen','police','doctor','soldier','reporter','politician','terrorist'];const v=allowed.includes(d.role)?d.role:'';p.claimedRole=v||null;emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('mafiaExecuteVote',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.phase!=='mafiaExecuteVote'||!p?.alive)throw Error('지금은 최종 처형 투표 시간이 아닙니다.');if(r.executeVotesSubmitted.includes(p.id))throw Error('이미 투표했습니다.');const v=d.choice==='execute'?'execute':'spare';r.executeVotes[p.id]=v;r.executeVotesSubmitted.push(p.id);const voters=r.players.filter(x=>x.alive);if(voters.every(x=>r.executeVotesSubmitted.includes(x.id)))resolveMafiaExecuteVote(r);else emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('mafiaChat',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.game!=='mafia'||r.phase==='lobby')throw Error('채팅을 사용할 수 없습니다.');const text=String(d.text||'').trim().slice(0,120);if(!text)throw Error('메시지를 입력하세요.');let ch;if(!p.alive)ch='dead';else if(['mafia','spy'].includes(p.role)&&r.players.filter(x=>x.alive&&['mafia','spy'].includes(x.role)).length>=2)ch='team';else throw Error('사용할 수 있는 비밀 채팅이 없습니다.');r.mafiaChats=r.mafiaChats||{team:[],dead:[]};r.mafiaChats[ch].push({name:p.name,text,at:Date.now()});r.mafiaChats[ch]=r.mafiaChats[ch].slice(-50);emitRoom(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('terroristPick',(d,cb)=>{try{const r=rooms.get(s.data.roomCode),p=by(r,s.data.playerId);if(!r||r.phase!=='terroristPick'||r.terroristPickId!==p?.id)throw Error('지금 선택할 수 없습니다.');if(!r.terroristCandidates?.includes(d.targetId))throw Error('함께 데려갈 수 없는 대상입니다.');resolveTerrorist(r,p.id,d.targetId);cb?.({ok:true})}catch(e){cb?.({ok:false,error:e.message})}});
  s.on('nextRound',(_,cb)=>{try{const r=rooms.get(s.data.roomCode);if(!r||r.hostId!==s.data.playerId)throw Error('방장만 진행할 수 있습니다.');if(r.game==='liar')startLiar(r);else if(r.game==='truth')startTruth(r);else if(r.game==='mafia')mafiaSetup(r);else if(r.game==='rummi')rummiSetup(r);else if(r.game==='wordchain')wordchainSetup(r);else if(r.game==='deathmatch'){r.parentGame='deathmatch';indianSetup(r);}else if(r.game==='genius'){if(active(r).some(p=>!p.isBot&&!p.geniusName))throw Error('모든 실제 플레이어가 두뇌게임 프로필 로그인을 완료해야 합니다.');r.parentGame='genius';r.game=r.settings.geniusGame||'stockwar';if(r.game==='stockwar')stockSetup(r);else if(r.game==='secretvault')vaultSetup(r);else throw Error('선택한 지니어스게임은 아직 준비 중입니다.');}else if(r.game==='stockwar')stockSetup(r);else if(r.game==='secretvault')vaultSetup(r);else if(r.game==='indianpoker')indianSetup(r);cb?.({ok:true});}catch(e){cb?.({ok:false,error:e.message});}});
  s.on('leaveRoom',(_,cb)=>{const code=s.data.roomCode,r=rooms.get(code),p=r&&by(r,s.data.playerId);if(r&&p&&r.hostId===p.id){clearTimer(r);clearTimeout(r.botTimer);rooms.delete(code);io.to(code).emit('roomClosed');}else if(r&&p){p.connected=false;emitRoom(r);}s.leave(code);s.data.roomCode=null;s.data.playerId=null;cb?.({ok:true});});
  s.on('disconnect',()=>{const r=rooms.get(s.data.roomCode),p=r&&by(r,s.data.playerId);if(r&&p){p.connected=false;emitRoom(r);}});
});

setInterval(()=>{const now=Date.now();for(const [c,r] of rooms){const humans=r.players.filter(p=>p.connected&&!p.isBot);if(!humans.length||now-(r.lastActivity||now)>10*60*1000){clearTimer(r);clearTimeout(r.botTimer);rooms.delete(c);io.to(c).emit('roomClosed')}}},60000);

server.listen(PORT,()=>console.log(`SOSO Party Game listening on ${PORT}`));
