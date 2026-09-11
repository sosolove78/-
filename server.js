const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' }, pingTimeout: 20000, pingInterval: 10000 });
const PORT = process.env.PORT || 3000;
const RECONNECT_GRACE_MS = 5 * 60 * 1000;

app.use(express.static(path.join(__dirname, 'public')));

const words = JSON.parse(fs.readFileSync(path.join(__dirname, 'data', 'words.json'), 'utf8'));
const questions = JSON.parse(fs.readFileSync(path.join(__dirname, 'data', 'questions.json'), 'utf8'));
const rooms = new Map();
const AVATARS = ['🦊','🐼','🐯','🐸','🐧','🐰','🐻','🐨','🦁','🐵','🐙','🦄','🐲','👻','🤖','🥷','🧙','🧛','🧑‍🚀','🕵️','🐺','🦖','🐱','🐶','🐹','🦝','🦋','🐝','🐳','🦈'];
const ALLOWED_TIMES = [0, 45, 60, 90, 120, 180, 300];
const ALLOWED_VOTE_TIMES = [15, 20, 30, 45, 60];

function makeCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  for (let tries = 0; tries < 100; tries++) {
    let code = '';
    for (let i = 0; i < 5; i++) code += chars[Math.floor(Math.random() * chars.length)];
    if (!rooms.has(code)) return code;
  }
  return String(Date.now()).slice(-5);
}
const uid = () => crypto.randomUUID();
const sanitizeName = name => String(name || '').trim().replace(/[<>]/g, '').slice(0, 12) || '플레이어';
const connectedPlayers = room => room.players.filter(p => p.connected);
const playerById = (room, id) => room.players.find(p => p.id === id);
const socketForPlayer = p => p.socketId ? io.sockets.sockets.get(p.socketId) : null;
const clamp = (n, min, max) => Math.max(min, Math.min(max, n));

function publicRoom(room) {
  return {
    code: room.code,
    hostId: room.hostId,
    phase: room.phase,
    mode: room.mode,
    round: room.round,
    players: room.players.map(p => ({
      id: p.id, name: p.name, avatar: p.avatar, connected: p.connected,
      score: p.score, streak: p.streak, isHost: p.id === room.hostId
    })),
    submitted: room.submitted,
    answersRevealed: room.answersRevealed,
    answers: room.answersRevealed ? room.answers : {},
    votesSubmitted: room.votesSubmitted,
    voteResult: room.voteResult,
    guessResult: room.guessResult,
    settings: room.settings,
    hasPassword: Boolean(room.password),
    deadline: room.deadline,
    promptMeta: room.phase !== 'lobby' && room.prompt ? (room.mode === 'question' ? { min: room.prompt?.min, max: room.prompt?.max } : { category: room.prompt?.category }) : null
  };
}

function emitState(room) {
  io.to(room.code).emit('roomState', publicRoom(room));
  for (const p of room.players) {
    const s = socketForPlayer(p);
    if (!s) continue;
    if (room.phase !== 'lobby' && room.prompt) {
      const isLiar = room.liarIds.includes(p.id);
      s.emit('privateRound', {
        isLiar,
        mode: room.mode,
        word: room.mode === 'normal' && !isLiar ? room.prompt.word : null,
        category: room.mode === 'normal' ? room.prompt.category : null,
        question: room.mode === 'question' && !isLiar ? room.prompt.question : null,
        min: room.mode === 'question' ? room.prompt.min : null,
        max: room.mode === 'question' ? room.prompt.max : null,
        canGuess: room.phase === 'liarGuess' && room.guessingLiarId === p.id,
        wordLength: room.mode === 'normal' && room.phase === 'liarGuess' && room.guessingLiarId === p.id ? [...room.prompt.word.replace(/\s/g, '')].length : null
      });
    }
  }
}

function clearTimer(room) {
  if (room.timer) clearTimeout(room.timer);
  room.timer = null;
  room.deadline = null;
}

function armTimer(room, seconds, onExpire) {
  clearTimer(room);
  room.deadline = Date.now() + seconds * 1000;
  room.timer = setTimeout(() => {
    room.timer = null;
    room.deadline = null;
    try { onExpire(); } catch (e) { console.error('timer error', e); }
  }, seconds * 1000);
}

function resetForRound(room) {
  clearTimer(room);
  room.answers = {};
  room.submitted = [];
  room.answersRevealed = false;
  room.votes = {};
  room.votesSubmitted = [];
  room.voteResult = null;
  room.guessResult = null;
  room.guessingLiarId = null;
}

function pickPrompt(room) {
  const pool = room.mode === 'normal' ? words : questions;
  let candidate;
  for (let i = 0; i < 12; i++) {
    candidate = pool[Math.floor(Math.random() * pool.length)];
    const key = room.mode === 'normal' ? candidate.word : candidate.question;
    if (!room.recentPrompts.includes(key)) {
      room.recentPrompts.push(key);
      if (room.recentPrompts.length > 30) room.recentPrompts.shift();
      return candidate;
    }
  }
  return candidate;
}

function chooseLiars(room) {
  const active = connectedPlayers(room);
  const count = clamp(room.settings.liarCount, 1, Math.max(1, Math.min(3, active.length - 1)));
  return [...active].sort(() => Math.random() - 0.5).slice(0, count).map(p => p.id);
}

function startDiscussionTimer(room) {
  if (room.settings.roundTime > 0) armTimer(room, room.settings.roundTime, () => openVoting(room, true));
  else clearTimer(room);
}

function startRound(room) {
  const active = connectedPlayers(room);
  if (active.length < 3) throw new Error('접속 중인 플레이어가 최소 3명 필요합니다.');
  room.round += 1;
  room.phase = 'play';
  resetForRound(room);
  room.liarIds = chooseLiars(room);
  room.prompt = pickPrompt(room);
  if (room.mode === 'normal') startDiscussionTimer(room);
  else if (room.settings.roundTime > 0) armTimer(room, room.settings.roundTime, () => revealQuestionAnswers(room, true));
  emitState(room);
}

function revealQuestionAnswers(room, timedOut = false) {
  if (room.phase !== 'play' || room.mode !== 'question') return;
  clearTimer(room);
  room.answersRevealed = true;
  room.phase = 'reveal';
  if (timedOut) {
    for (const p of connectedPlayers(room)) if (room.answers[p.id] === undefined) room.answers[p.id] = null;
  }
  startDiscussionTimer(room);
  emitState(room);
}

function openVoting(room, automatic = false) {
  if (!['play','reveal'].includes(room.phase)) return;
  if (room.mode === 'question' && !room.answersRevealed) {
    if (!automatic) throw new Error('모든 답변이 공개된 뒤 투표를 열어주세요.');
    revealQuestionAnswers(room, true);
    return;
  }
  clearTimer(room);
  room.phase = 'vote';
  room.votes = {};
  room.votesSubmitted = [];
  armTimer(room, room.settings.voteTime, () => tallyVotes(room));
  emitState(room);
}

function awardResults(room, caught, targetId) {
  const active = connectedPlayers(room);
  if (caught) {
    for (const p of active) {
      if (!room.liarIds.includes(p.id)) {
        p.score += 1;
        if (room.votes[p.id] === targetId) p.score += 1;
        p.streak += 1;
      } else p.streak = 0;
    }
  } else {
    for (const p of active) {
      if (room.liarIds.includes(p.id)) { p.score += 3; p.streak += 1; }
      else p.streak = 0;
    }
  }
}

function finalizeResult(room, caught, targetId) {
  clearTimer(room);
  awardResults(room, caught, targetId);
  room.phase = 'result';
  emitState(room);
}

function tallyVotes(room) {
  if (room.phase !== 'vote') return;
  clearTimer(room);
  const counts = {};
  Object.values(room.votes).forEach(id => counts[id] = (counts[id] || 0) + 1);
  const max = Math.max(0, ...Object.values(counts));
  const top = Object.entries(counts).filter(([,v]) => v === max && max > 0).map(([id]) => id);
  const targetId = top.length === 1 ? top[0] : null;
  const caught = Boolean(targetId && room.liarIds.includes(targetId));
  room.voteResult = { counts, top, targetId, liarIds: room.liarIds, caught, tie: top.length !== 1 };

  if (caught && room.mode === 'normal' && room.settings.liarFinalGuess) {
    room.phase = 'liarGuess';
    room.guessingLiarId = targetId;
    armTimer(room, 25, () => {
      room.guessResult = { attempted: false, correct: false, answer: room.prompt.word };
      finalizeResult(room, true, targetId);
    });
    emitState(room);
  } else finalizeResult(room, caught, targetId);
}

function removePlayer(room, playerId, reason = '퇴장') {
  const p = playerById(room, playerId);
  if (!p) return;
  const s = socketForPlayer(p);
  if (s) {
    s.emit('removedFromRoom', { reason });
    s.leave(room.code);
    s.data.roomCode = null;
    s.data.playerId = null;
  }
  room.players = room.players.filter(x => x.id !== playerId);
  delete room.answers[playerId];
  delete room.votes[playerId];
  room.submitted = room.submitted.filter(id => id !== playerId);
  room.votesSubmitted = room.votesSubmitted.filter(id => id !== playerId);
  room.liarIds = room.liarIds.filter(id => id !== playerId);
  if (!room.players.length) { clearTimer(room); rooms.delete(room.code); return; }
  if (room.hostId === playerId) room.hostId = room.players.find(x => x.connected)?.id || room.players[0].id;
  if (connectedPlayers(room).length < 3 && room.phase !== 'lobby') {
    room.phase = 'lobby'; room.round = 0; resetForRound(room);
  }
  emitState(room);
}

function bindSocketToPlayer(socket, room, player) {
  player.socketId = socket.id;
  player.connected = true;
  player.disconnectedAt = null;
  socket.join(room.code);
  socket.data.roomCode = room.code;
  socket.data.playerId = player.id;
}

function newPlayer(name, avatar, sessionId) {
  return {
    id: uid(), sessionId, socketId: null,
    name: sanitizeName(name), avatar: AVATARS.includes(avatar) ? avatar : AVATARS[0],
    connected: true, disconnectedAt: null, score: 0, streak: 0
  };
}

setInterval(() => {
  const now = Date.now();
  for (const room of rooms.values()) {
    for (const p of [...room.players]) {
      if (!p.connected && p.disconnectedAt && now - p.disconnectedAt > RECONNECT_GRACE_MS) removePlayer(room, p.id, '재접속 시간이 만료되었습니다.');
    }
  }
}, 30000).unref();

io.on('connection', socket => {
  socket.on('createRoom', ({name, avatar, mode, sessionId, password}, cb) => {
    try {
      const code = makeCode();
      const sid = String(sessionId || uid());
      const player = newPlayer(name, avatar, sid);
      const room = {
        code, hostId: player.id, players:[player], phase:'lobby',
        mode: mode === 'question' ? 'question':'normal', round:0,
        password: String(password || '').trim().slice(0, 24),
        settings:{maxPlayers:10, liarCount:1, roundTime:120, voteTime:30, liarFinalGuess:true},
        submitted:[], answersRevealed:false, votesSubmitted:[], liarIds:[], recentPrompts:[], deadline:null, timer:null
      };
      rooms.set(code, room);
      bindSocketToPlayer(socket, room, player);
      cb?.({ok:true, code, playerId:player.id, sessionId:sid});
      emitState(room);
    } catch (e) { cb?.({ok:false, error:e.message}); }
  });

  socket.on('joinRoom', ({code,name,avatar,sessionId,password}, cb) => {
    try {
      code = String(code || '').trim().toUpperCase();
      const room = rooms.get(code);
      if (!room) throw new Error('방을 찾을 수 없습니다.');
      if (room.password && String(password || '') !== room.password) throw new Error('방 비밀번호가 올바르지 않습니다.');
      const sid = String(sessionId || uid());
      const existing = room.players.find(p => p.sessionId === sid);
      if (existing) {
        if (existing.socketId && existing.socketId !== socket.id) io.sockets.sockets.get(existing.socketId)?.disconnect(true);
        existing.name = sanitizeName(name || existing.name);
        existing.avatar = AVATARS.includes(avatar) ? avatar : existing.avatar;
        bindSocketToPlayer(socket, room, existing);
        cb?.({ok:true, code, playerId:existing.id, sessionId:sid, reconnected:true});
        emitState(room); return;
      }
      if (room.phase !== 'lobby') throw new Error('이미 게임이 시작된 방입니다. 기존 참가자는 재접속할 수 있습니다.');
      if (room.players.length >= room.settings.maxPlayers) throw new Error('최대 10명까지 입장할 수 있습니다.');
      const player = newPlayer(name, avatar, sid);
      room.players.push(player);
      bindSocketToPlayer(socket, room, player);
      cb?.({ok:true, code, playerId:player.id, sessionId:sid});
      emitState(room);
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('resumeSession', ({code, sessionId}, cb) => {
    try {
      const room = rooms.get(String(code || '').toUpperCase());
      if (!room) throw new Error('방이 종료되었습니다.');
      const player = room.players.find(p => p.sessionId === sessionId);
      if (!player) throw new Error('재접속할 참가자 정보를 찾지 못했습니다.');
      bindSocketToPlayer(socket, room, player);
      cb?.({ok:true, code:room.code, playerId:player.id, sessionId});
      emitState(room);
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('updateSettings', (settings, cb) => {
    const room = rooms.get(socket.data.roomCode);
    try {
      if (!room || room.hostId !== socket.data.playerId || room.phase !== 'lobby') throw new Error('대기실의 방장만 설정을 변경할 수 있습니다.');
      if (settings.mode) room.mode = settings.mode === 'question' ? 'question' : 'normal';
      if (settings.liarCount !== undefined) room.settings.liarCount = clamp(Number(settings.liarCount)||1, 1, 3);
      if (settings.roundTime !== undefined && ALLOWED_TIMES.includes(Number(settings.roundTime))) room.settings.roundTime = Number(settings.roundTime);
      if (settings.voteTime !== undefined && ALLOWED_VOTE_TIMES.includes(Number(settings.voteTime))) room.settings.voteTime = Number(settings.voteTime);
      if (settings.liarFinalGuess !== undefined) room.settings.liarFinalGuess = Boolean(settings.liarFinalGuess);
      if (settings.clearPassword) room.password = '';
      else if (settings.password !== undefined) room.password = String(settings.password || '').trim().slice(0, 24);
      emitState(room); cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('startGame', (_, cb) => {
    const room = rooms.get(socket.data.roomCode);
    try {
      if (!room || room.hostId !== socket.data.playerId) throw new Error('방장만 시작할 수 있습니다.');
      startRound(room); cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('submitAnswer', ({value}, cb) => {
    const room = rooms.get(socket.data.roomCode); const id = socket.data.playerId;
    try {
      if (!room || room.phase !== 'play' || room.mode !== 'question') throw new Error('지금은 답변할 수 없습니다.');
      if (room.answers[id] !== undefined) throw new Error('이미 답변했습니다.');
      const n = Number(value);
      if (!Number.isFinite(n) || n < room.prompt.min || n > room.prompt.max) throw new Error(`답은 ${room.prompt.min}~${room.prompt.max} 범위여야 합니다.`);
      room.answers[id] = Math.round(n);
      room.submitted = Object.keys(room.answers);
      if (connectedPlayers(room).every(p => room.answers[p.id] !== undefined)) revealQuestionAnswers(room);
      else emitState(room);
      cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('openVoting', (_, cb) => {
    const room = rooms.get(socket.data.roomCode);
    try {
      if (!room || room.hostId !== socket.data.playerId) throw new Error('방장만 투표를 열 수 있습니다.');
      if (!['play','reveal'].includes(room.phase)) throw new Error('지금은 투표를 열 수 없습니다.');
      openVoting(room); cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('vote', ({targetId}, cb) => {
    const room = rooms.get(socket.data.roomCode); const id = socket.data.playerId;
    try {
      if (!room || room.phase !== 'vote') throw new Error('투표 시간이 아닙니다.');
      if (room.votes[id]) throw new Error('이미 투표했습니다.');
      if (!connectedPlayers(room).some(p => p.id === targetId)) throw new Error('잘못된 대상입니다.');
      if (id === targetId) throw new Error('자기 자신에게는 투표할 수 없습니다.');
      room.votes[id] = targetId;
      room.votesSubmitted = Object.keys(room.votes);
      if (connectedPlayers(room).every(p => room.votes[p.id])) tallyVotes(room);
      else emitState(room);
      cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('submitLiarGuess', ({guess}, cb) => {
    const room = rooms.get(socket.data.roomCode); const id = socket.data.playerId;
    try {
      if (!room || room.phase !== 'liarGuess' || room.guessingLiarId !== id) throw new Error('지금은 최종 추측을 할 수 없습니다.');
      const g = String(guess || '').trim();
      if (!g) throw new Error('단어를 입력해주세요.');
      const answer = String(room.prompt.word || '').trim();
      const normalize = x => x.replace(/\s+/g,'').toLowerCase();
      const correct = normalize(g) === normalize(answer);
      room.guessResult = { attempted:true, correct, guess:g, answer };
      const liar = playerById(room, id);
      if (correct && liar) liar.score += 2;
      finalizeResult(room, true, id);
      cb?.({ok:true, correct});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('nextRound', (_, cb) => {
    const room = rooms.get(socket.data.roomCode);
    try {
      if (!room || room.hostId !== socket.data.playerId) throw new Error('방장만 다음 라운드를 시작할 수 있습니다.');
      if (room.phase !== 'result') throw new Error('결과 화면에서 다음 라운드를 시작해주세요.');
      startRound(room); cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('backToLobby', (_, cb) => {
    const room = rooms.get(socket.data.roomCode);
    if (!room || room.hostId !== socket.data.playerId) return cb?.({ok:false,error:'방장만 가능합니다.'});
    room.phase='lobby'; room.round=0; room.liarIds=[]; room.prompt=null; resetForRound(room); emitState(room); cb?.({ok:true});
  });

  socket.on('kickPlayer', ({playerId}, cb) => {
    const room = rooms.get(socket.data.roomCode);
    try {
      if (!room || room.hostId !== socket.data.playerId) throw new Error('방장만 강퇴할 수 있습니다.');
      if (playerId === room.hostId) throw new Error('방장 자신은 강퇴할 수 없습니다.');
      if (!playerById(room, playerId)) throw new Error('플레이어를 찾을 수 없습니다.');
      removePlayer(room, playerId, '방장에 의해 강퇴되었습니다.'); cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('transferHost', ({playerId}, cb) => {
    const room = rooms.get(socket.data.roomCode);
    try {
      if (!room || room.hostId !== socket.data.playerId) throw new Error('방장만 위임할 수 있습니다.');
      const target = playerById(room, playerId);
      if (!target || !target.connected) throw new Error('접속 중인 플레이어에게만 위임할 수 있습니다.');
      if (target.id === room.hostId) throw new Error('이미 방장입니다.');
      room.hostId = target.id; emitState(room); cb?.({ok:true});
    } catch(e) { cb?.({ok:false,error:e.message}); }
  });

  socket.on('leaveRoom', (_, cb) => {
    const room = rooms.get(socket.data.roomCode);
    if (room) removePlayer(room, socket.data.playerId, '방을 나갔습니다.');
    cb?.({ok:true});
  });

  socket.on('disconnect', () => {
    const room = rooms.get(socket.data.roomCode); if (!room) return;
    const p = playerById(room, socket.data.playerId); if (!p) return;
    p.connected = false; p.socketId = null; p.disconnectedAt = Date.now();
    emitState(room);
  });
});

app.get('/health', (_,res)=>res.json({ok:true, rooms:rooms.size, words:words.length, questions:questions.length, version:'3.0.0'}));
server.listen(PORT, () => console.log(`Liar game v3 running on http://localhost:${PORT}`));
