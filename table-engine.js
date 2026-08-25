const { randomInt } = require('crypto')
const botV1 = require('./bot-v1')
const botV2 = require('./bot-v2')

const PORT = 3000
const MAX_PLAYERS = 4
const MAX_ROUNDS = 5
const INITIAL_STOCK_COUNT = 20
const TEA_MIN_SIP_FRACTION = 0.08
const TEA_MAX_SIP_FRACTION = 0.15
const TEA_DRINK_ACTION_MS = 2300
const TEA_REFILL_ACTION_MS = 3000
const ROUND_END_HOLD_MS = 2200
const CHAT_MAX_LENGTH = 180
const CHAT_RATE_LIMIT_MS = 650
const EMOJI_RATE_LIMIT_MS = 700
const POKE_COOLDOWN_MS = 6000
const SEAT_SWAP_REQUEST_TIMEOUT_MS = 15000
const SOCIAL_EMOJIS = new Set([
  '😂', '😎', '😡', '😭', '❤️', '👍', '👏', '🔥', '🤔', '😴', '🎉', '👀',
])
const BOT_COUNT = Math.max(
  0,
  Math.min(3, Number.parseInt(process.env.BOT_COUNT || '0', 10) || 0)
)
const BOT_VERSION = String(process.env.BOT_VERSION || 'v2').toLowerCase() === 'v1'
  ? 'v1'
  : 'v2'
const BOT_TURN_DELAY_MS = Math.max(
  0,
  Number.parseInt(process.env.BOT_TURN_DELAY_MS || '450', 10) || 0
)
const BOT_DECISION_DELAY_MS = Math.max(
  0,
  Number.parseInt(process.env.BOT_DECISION_DELAY_MS || '900', 10) || 0
)
const BOT_OPENING_CAMERA_LEAD_MS = Math.max(
  0,
  Number.parseInt(process.env.BOT_OPENING_CAMERA_LEAD_MS || '700', 10) || 0
)
const BOT_OPENING_GROUP_DELAY_MS = Math.max(
  120,
  Number.parseInt(process.env.BOT_OPENING_GROUP_DELAY_MS || '1000', 10) || 1000
)
const BOT_TABLE_ACTION_DELAY_MS = Math.max(
  0,
  Number.parseInt(process.env.BOT_TABLE_ACTION_DELAY_MS || '1000', 10) || 0
)
const BOT_BEFORE_DISCARD_DELAY_MS = Math.max(
  0,
  Number.parseInt(process.env.BOT_BEFORE_DISCARD_DELAY_MS || '1100', 10) || 0
)

// Kullanıcının istediği ana profil: Türkçe Vikipedi Okey 101 kuralları.
// Pagat açıklaması yalnızca Vikipedi'deki belirsiz puan kombinasyonlarını
// netleştirmek için referans alınmıştır.
const RULES_PROFILE = 'tr-wikipedia-okey-101'

// Vikipedi "Ek Kurallar" bölümündeki yandan alınan taşla açıldığında
// taşı atan oyuncuya taşın sayı değerinin 10 katı ceza yazma kuralı.
// Oyun varsayılan olarak eşlidir: karşılıklı oturan oyuncular aynı takımdadır.
// Bu bayrak yine bireysel hamlenin kaynağına yazılan ceza davranışını korur.
const APPLY_WIKI_TAKEN_DISCARD_SOURCE_PENALTY = true

const COLORS = [
  'red',
  'blue',
  'black',
  'yellow',
]

// Saat yönünün tersine oyun sırası.
const SEATS = [
  'player-bottom',
  'player-right',
  'player-top',
  'player-left',
]

const TEAM_DEFINITIONS = Object.freeze([
  Object.freeze({
    id: 'team-bottom-top',
    seats: Object.freeze(['player-bottom', 'player-top']),
  }),
  Object.freeze({
    id: 'team-right-left',
    seats: Object.freeze(['player-right', 'player-left']),
  }),
])


function createTableRuntime(rawIo, tableId, options = {}) {
  const roomName = `table:${tableId}`
  const onStateChanged = typeof options.onStateChanged === 'function'
    ? options.onStateChanged
    : null
  let destroyed = false
  let changeQueued = false
  let lastNotifiedSummaryKey = null

  function queueStateChanged() {
    if (!onStateChanged || changeQueued) return
    changeQueued = true
    setImmediate(() => {
      changeQueued = false
      if (destroyed) return

      const summary = getSummary()
      const summaryKey = [
        summary.playerCount,
        summary.humanCount,
        summary.botCount,
        summary.phase,
        summary.round,
        summary.joinable ? 1 : 0,
      ].join('|')

      if (summaryKey === lastNotifiedSummaryKey) return
      lastNotifiedSummaryKey = summaryKey
      onStateChanged(tableId)
    })
  }

  // Existing game engine expects an io-like object. Room broadcasts are scoped
  // here so the rule engine itself stays table-local without thousands of
  // roomId parameters. Direct socket-id sends remain direct.
  const io = {
    emit(eventName, ...args) {
      if (destroyed) return
      rawIo.to(roomName).emit(eventName, ...args)
      // The match finder only depends on roster/phase summaries. Chat, SFX,
      // emoji and tea events must not fan out a global table-list refresh.
      if (eventName === 'players-state' || eventName === 'game-state') {
        queueStateChanged()
      }
    },
    to(target) {
      return rawIo.to(target)
    },
    sockets: rawIo.sockets,
  }

  const players = new Map()
  let game = null
  let tileIdCounter = 1
  let botSerial = 0
  let kickVoteSerial = 0
  let kickVote = null
  let lobbyReadyResetSerial = 0
  let seatSwapRequestSerial = 0

  const pendingSeatSwapRequests = new Map()
  const lastChatAtByPlayerId = new Map()
  const lastEmojiAtByPlayerId = new Map()
  const lastPokeAtByTargetId = new Map()

  const KICK_VOTE_TIMEOUT_MS = 30000

  // =====================================================
  // GENEL HELPERS
  // =====================================================

  function clonePlain(value) {
    return JSON.parse(JSON.stringify(value))
  }

  function emitGameSfx(type, extra = {}) {
    io.emit('game-sfx', {
      type,
      ...extra,
    })
  }

  function waitMs(ms) {
    if (!(ms > 0)) return Promise.resolve()
    return new Promise(resolve => setTimeout(resolve, ms))
  }

  function nextTileId() {
    return `tile-${tileIdCounter++}`
  }

  function nextSeat(seat) {
    const index = SEATS.indexOf(seat)

    if (index < 0) {
      return SEATS[0]
    }

    return SEATS[(index + 1) % SEATS.length]
  }

  function previousSeat(seat) {
    const index = SEATS.indexOf(seat)

    if (index < 0) {
      return SEATS[SEATS.length - 1]
    }

    return SEATS[(index - 1 + SEATS.length) % SEATS.length]
  }

  function getPlayerById(id) {
    return players.get(id)
  }

  function getSeatPlayer(seat) {
    return [...players.values()].find(
      player => player.seat === seat
    )
  }

  function getTeamDefinitionForSeat(seat) {
    return TEAM_DEFINITIONS.find(team =>
      team.seats.includes(seat)
    ) || null
  }

  function getTeamIdForSeat(seat) {
    return getTeamDefinitionForSeat(seat)?.id || null
  }

  function getTeamPlayers(teamDefinition) {
    if (!teamDefinition) return []

    return teamDefinition.seats
      .map(seat => getSeatPlayer(seat))
      .filter(Boolean)
  }

  function getPublicTeams() {
    return TEAM_DEFINITIONS.map(team => {
      const members = getTeamPlayers(team)
      const roundCount = members.reduce(
        (max, player) => Math.max(max, player.roundScores?.length || 0),
        0
      )

      const roundScores = Array.from(
        { length: roundCount },
        (_, index) => members.reduce(
          (sum, player) => sum + (Number(player.roundScores?.[index]) || 0),
          0
        )
      )

      return {
        id: team.id,
        seats: [...team.seats],
        playerIds: members.map(player => player.id),
        playerNames: members.map(player => player.name),
        totalScore: members.reduce(
          (sum, player) => sum + (Number(player.totalScore) || 0),
          0
        ),
        roundScores,
      }
    })
  }

  function getTeamScoresFromPlayerScores(playerScores = {}) {
    return Object.fromEntries(
      TEAM_DEFINITIONS.map(team => [
        team.id,
        getTeamPlayers(team).reduce(
          (sum, player) => sum + (Number(playerScores[player.id]) || 0),
          0
        ),
      ])
    )
  }

  function selectWinningTeams(teams = []) {
    const eligible = teams.filter(team =>
      Array.isArray(team.playerIds) && team.playerIds.length > 0
    )

    if (!eligible.length) return []

    const bestScore = Math.min(
      ...eligible.map(team => Number(team.totalScore) || 0)
    )

    return eligible.filter(
      team => (Number(team.totalScore) || 0) === bestScore
    )
  }

  function getFreeSeat() {
    const occupied = new Set(
      [...players.values()].map(player => player.seat)
    )

    return SEATS.find(seat => !occupied.has(seat))
  }

  function createPlayerState(id, name, seat, isBot = false) {
    return {
      id,
      name,
      seat,
      isBot,
      // Botlar lobi hazirligini beklemez; gercek oyuncular acikca HAZIR vermelidir.
      ready: Boolean(isBot),
      // Cay miktari server-authoritative 0..1 seviye olarak tutulur.
      // Her yudumda %8-%15 arasi rastgele azalir; bos bardaga sonraki tik yeni cay ister.
      teaLevel: 1,
      teaBusyUntil: 0,
      lookX: 0,
      lookY: 0,
      hand: [],
      opened: false,
      openType: null,
      penalty: 0,
      currentPenaltyEntries: [],
      pickedDiscardId: null,
      pickedDiscardSourceId: null,
      pickedDiscardRequiresOpening: false,
      mustDiscard: false,
      // İlk açılış için o tur gerçekten stock/discard/gösterge taşı alınmış olmalı.
      // Başlangıç oyuncusunun 22. taşı bu bayrağı açmaz.
      turnHasAcquiredTile: false,
      turnTableActions: 0,
      turnLayoffHistory: [],
      openedAllAtOnceTurn: null,
      openedAllAtOnceNoOtherOpen: false,
      finalIndicatorId: null,
      finalIndicatorSnapshot: null,
      totalScore: 0,
      roundScores: [],
      scoreLedger: [],
      // İnsan oyuncunun discard anına kadar masada bekleyen geçici açılış taslağı.
      // Taşlar authoritative olarak hâlâ eldedir; yalnızca public görünür hale gelir.
      openingDraft: [],
      // Geçerli ilk açılışa dayanarak aynı turda işleme yapıldıysa,
      // bu çekirdek gruplar discard gelene kadar geri çekilemez.
      openingDraftLockedCore: [],
      // BOT V2 adaptif açılış hafızası.
      // V2 legal 101/5 çift gördüğünde yalnız anlamlı bir tek-çekiş gelişme
      // ihtimali varsa en fazla bir kendi turu bekleyebilir. Karar tur boyunca
      // kilitlenir; aynı state yayınları kararı değiştirmez.
      botOpeningWaitCount: 0,
      botOpeningDecisionTurn: null,
      botOpeningAllowedThisTurn: null,
      botOpeningDecisionMeta: null,
    }
  }

  function addBotPlayer() {
    const seat = getFreeSeat()
    if (!seat) return null

    let id
    do {
      id = `__bot-v1-${++botSerial}`
    } while (players.has(id))

    const bot = createPlayerState(id, `BOT ${botSerial}`, seat, true)
    players.set(id, bot)
    return bot
  }

  function ensureConfiguredBots() {
    const existingBots = [...players.values()].filter(
      player => player.isBot
    ).length

    while (
      [...players.values()].filter(player => player.isBot).length < BOT_COUNT &&
      players.size < MAX_PLAYERS
    ) {
      if (!addBotPlayer()) break
    }
  }

  // =====================================================
  // LOBI / HAZIRLIK
  // =====================================================

  function sanitizePlayerName(value) {
    return String(value || '')
      .trim()
      .replace(/\s+/g, ' ')
      .slice(0, 20)
  }

  function sanitizeChatMessage(value) {
    return String(value || '')
      .replace(/[\u0000-\u001f\u007f]/g, ' ')
      .trim()
      .replace(/\s+/g, ' ')
      .slice(0, CHAT_MAX_LENGTH)
  }

  function passesSocialRateLimit(map, playerId, minIntervalMs) {
    const now = Date.now()
    const previous = Number(map.get(playerId)) || 0
    if (now - previous < minIntervalMs) return false
    map.set(playerId, now)
    return true
  }

  function isLobbyEditable() {
    return !game || game.phase === 'waiting'
  }

  function resetHumanReadyState() {
    for (const player of players.values()) {
      player.ready = Boolean(player.isBot)
    }
  }

  function getPendingSeatSwapForPlayer(playerId) {
    for (const request of pendingSeatSwapRequests.values()) {
      if (request.sourceId === playerId || request.targetId === playerId) {
        return request
      }
    }
    return null
  }

  function emitSeatSwapCancelled(request, reason = 'cancelled') {
    if (!request) return

    const payload = {
      requestId: request.id,
      reason,
      sourcePlayerId: request.sourceId,
      sourceName: request.sourceName,
      targetPlayerId: request.targetId,
      targetName: request.targetName,
    }

    io.to(request.sourceId).emit('seat-swap-cancelled', payload)
    io.to(request.targetId).emit('seat-swap-cancelled', payload)
  }

  function cancelSeatSwapRequest(requestId, reason = 'cancelled', notify = true) {
    const request = pendingSeatSwapRequests.get(requestId)
    if (!request) return false

    pendingSeatSwapRequests.delete(requestId)
    if (request.timer) clearTimeout(request.timer)
    if (notify) emitSeatSwapCancelled(request, reason)
    return true
  }

  function cancelAllSeatSwapRequests(reason = 'lobby-reset') {
    for (const requestId of [...pendingSeatSwapRequests.keys()]) {
      cancelSeatSwapRequest(requestId, reason, true)
    }
  }

  function cancelOutgoingSeatSwapRequestsForPlayer(playerId, reason = 'requester-unavailable') {
    for (const request of [...pendingSeatSwapRequests.values()]) {
      if (request.sourceId === playerId) {
        cancelSeatSwapRequest(request.id, reason, true)
      }
    }
  }

  function createSeatSwapRequest(source, target) {
    const id = `seat-swap-${++seatSwapRequestSerial}`
    const expiresAt = Date.now() + SEAT_SWAP_REQUEST_TIMEOUT_MS
    const request = {
      id,
      sourceId: source.id,
      sourceName: source.name,
      targetId: target.id,
      targetName: target.name,
      createdAt: Date.now(),
      expiresAt,
      timer: null,
    }

    request.timer = setTimeout(() => {
      cancelSeatSwapRequest(id, 'expired', true)
    }, SEAT_SWAP_REQUEST_TIMEOUT_MS)
    request.timer.unref?.()

    pendingSeatSwapRequests.set(id, request)
    return request
  }

  function performSeatSwap(source, target) {
    if (!source || !target || source.id === target.id) {
      return { ok: false, message: 'Koltuk değişimi yapılamadı.' }
    }

    if (!isLobbyEditable()) {
      return { ok: false, message: 'Oyun başladıktan sonra koltuk değiştirilemez.' }
    }

    if (source.isBot || source.ready) {
      return { ok: false, message: 'Yer değiştirme isteği gönderen oyuncu hazır olmamalı.' }
    }

    const sourceSeat = source.seat
    const targetSeat = target.seat

    if (!SEATS.includes(sourceSeat) || !SEATS.includes(targetSeat)) {
      return { ok: false, message: 'Koltuk bilgisi geçersiz.' }
    }

    source.seat = targetSeat
    target.seat = sourceSeat

    // İsteği gönderen zaten hazır değildir. Gerçek hedef de koltuk değişiminden
    // sonra yeniden hazır vermelidir. Botlar lobi sisteminde otomatik hazırdır.
    source.ready = false
    target.ready = Boolean(target.isBot)

    io.emit('players-state', getPublicPlayers())
    broadcastGameState()

    const payload = {
      sourcePlayerId: source.id,
      sourceName: source.name,
      sourceSeat: source.seat,
      targetPlayerId: target.id,
      targetName: target.name,
      targetSeat: target.seat,
    }

    io.to(source.id).emit('seat-swap-completed', payload)
    if (!target.isBot) {
      io.to(target.id).emit('seat-swap-completed', payload)
    }

    return { ok: true, payload }
  }

  function broadcastLobbyReadyReset(reason = 'roster-change') {
    cancelAllSeatSwapRequests(reason)
    resetHumanReadyState()
    io.emit('lobby-ready-reset', {
      serial: ++lobbyReadyResetSerial,
      reason,
    })
  }

  function areAllHumanPlayersReady() {
    if (players.size !== MAX_PLAYERS) return false
    return [...players.values()].every(player => player.isBot || player.ready)
  }

  function getPublicTeaLevel(player) {
    const level = Number(player?.teaLevel)
    return Number.isFinite(level)
      ? Math.max(0, Math.min(1, level))
      : 1
  }

  function getRandomTeaSipFraction() {
    return TEA_MIN_SIP_FRACTION + Math.random() * (TEA_MAX_SIP_FRACTION - TEA_MIN_SIP_FRACTION)
  }

  // =====================================================
  // İNSAN OYUNCU KICK OYLAMASI
  // =====================================================
  // Botlar oy vermez ve kick oylamasının hedefi olamaz; onlar için ayrı
  // BOT ÇIKAR kontrolü vardır. Hedef oyuncu oy kullanmaz. Çoğunluk toplam insan
  // sayısına göre hesaplanır: 4 insanda 3, 3 insanda 2 EVET; yalnız 2 insan
  // kaldığında diğer tek kişinin oyu doğrudan yeterlidir.
  function getHumanPlayers() {
    return [...players.values()].filter(player => !player.isBot)
  }

  function getKickRequiredVotes(targetId) {
    const humans = getHumanPlayers()
    const targetExists = humans.some(player => player.id === targetId)

    if (!targetExists) return 0

    const eligibleVoterCount = humans.filter(
      player => player.id !== targetId
    ).length

    if (eligibleVoterCount <= 0) return 0

    // Çoğunluk toplam İNSAN oyuncu sayısına göre hesaplanır; botlar yok sayılır.
    // 4 insanda 3 EVET, 3 insanda 2 EVET gerekir. Yalnız 2 insan kaldığında
    // kullanıcı isteği gereği diğer tek oyuncunun oyu doğrudan yeterlidir.
    if (humans.length <= 2) return 1
    return Math.floor(humans.length / 2) + 1
  }

  function getPublicKickVoteState() {
    if (!kickVote) return null

    const target = players.get(kickVote.targetId)
    if (!target || target.isBot) return null

    const eligibleIds = new Set(
      getHumanPlayers()
        .filter(player => player.id !== target.id)
        .map(player => player.id)
    )

    const yesVoterIds = [...kickVote.yesVoterIds].filter(id => eligibleIds.has(id))
    const noVoterIds = [...kickVote.noVoterIds].filter(id => eligibleIds.has(id))

    return {
      id: kickVote.id,
      targetId: target.id,
      targetName: target.name,
      startedById: kickVote.startedById,
      yesVotes: yesVoterIds.length,
      noVotes: noVoterIds.length,
      requiredVotes: getKickRequiredVotes(target.id),
      yesVoterIds,
      noVoterIds,
      expiresAt: kickVote.expiresAt,
    }
  }

  function broadcastKickVoteState() {
    io.emit('kick-vote-state', getPublicKickVoteState())
  }

  function clearKickVote() {
    if (kickVote?.timeout) {
      clearTimeout(kickVote.timeout)
    }
    kickVote = null
    broadcastKickVoteState()
  }

  function pruneKickVoteAndEvaluate() {
    if (!kickVote) return false

    const target = players.get(kickVote.targetId)
    if (!target || target.isBot) {
      clearKickVote()
      return false
    }

    const eligibleIds = new Set(
      getHumanPlayers()
        .filter(player => player.id !== target.id)
        .map(player => player.id)
    )

    for (const id of [...kickVote.yesVoterIds]) {
      if (!eligibleIds.has(id)) kickVote.yesVoterIds.delete(id)
    }
    for (const id of [...kickVote.noVoterIds]) {
      if (!eligibleIds.has(id)) kickVote.noVoterIds.delete(id)
    }

    const required = getKickRequiredVotes(target.id)
    if (required > 0 && kickVote.yesVoterIds.size >= required) {
      const targetSocket = io.sockets.sockets.get(target.id)

      io.emit('kick-vote-passed', {
        targetId: target.id,
        targetName: target.name,
      })

      if (targetSocket) {
        targetSocket.emit('kicked', {
          message: 'Masa oylamasıyla oyundan çıkarıldın.',
        })
        targetSocket.disconnect(true)
      } else {
        players.delete(target.id)
        io.emit('players-state', getPublicPlayers())
        broadcastGameState()
      }

      clearKickVote()
      return true
    }

    broadcastKickVoteState()
    return false
  }

  function startKickVote(requester, targetId) {
    if (!requester || requester.isBot) {
      return { ok: false, message: 'Botlar kick oylaması başlatamaz.' }
    }

    const target = players.get(targetId)
    if (!target || target.isBot) {
      return { ok: false, message: 'Yalnız insan oyuncular için kick oylaması yapılabilir.' }
    }

    if (target.id === requester.id) {
      return { ok: false, message: 'Kendin için kick oylaması başlatamazsın.' }
    }

    if (kickVote) {
      if (kickVote.targetId !== target.id) {
        return { ok: false, message: 'Şu anda başka bir kick oylaması devam ediyor.' }
      }

      kickVote.noVoterIds.delete(requester.id)
      kickVote.yesVoterIds.add(requester.id)
      pruneKickVoteAndEvaluate()
      return { ok: true, joinedExistingVote: true }
    }

    const id = `kick-${++kickVoteSerial}`
    const expiresAt = Date.now() + KICK_VOTE_TIMEOUT_MS

    kickVote = {
      id,
      targetId: target.id,
      startedById: requester.id,
      yesVoterIds: new Set([requester.id]),
      noVoterIds: new Set(),
      expiresAt,
      timeout: setTimeout(() => {
        if (kickVote?.id === id) {
          clearKickVote()
        }
      }, KICK_VOTE_TIMEOUT_MS),
    }

    pruneKickVoteAndEvaluate()
    return { ok: true }
  }

  function castKickVote(voter, voteYes) {
    if (!kickVote) {
      return { ok: false, message: 'Aktif kick oylaması yok.' }
    }

    if (!voter || voter.isBot) {
      return { ok: false, message: 'Botların oy hakkı yok.' }
    }

    if (voter.id === kickVote.targetId) {
      return { ok: false, message: 'Hedef oyuncu kendi kick oylamasında oy kullanamaz.' }
    }

    kickVote.yesVoterIds.delete(voter.id)
    kickVote.noVoterIds.delete(voter.id)

    if (voteYes) kickVote.yesVoterIds.add(voter.id)
    else kickVote.noVoterIds.add(voter.id)

    pruneKickVoteAndEvaluate()
    return { ok: true }
  }

  // =====================================================
  // TAŞLAR / 106 TAŞLIK DESTE
  // =====================================================

  function createNormalTile(color, number, copy) {
    return {
      id: nextTileId(),
      type: 'normal',
      color,
      number,
      copy,
    }
  }

  function createFakeJoker(copy) {
    return {
      id: nextTileId(),
      type: 'fake-joker',
      color: null,
      number: null,
      copy,
    }
  }

  function createDeck() {
    tileIdCounter = 1

    const deck = []

    for (const color of COLORS) {
      for (let number = 1; number <= 13; number++) {
        deck.push(createNormalTile(color, number, 1))
        deck.push(createNormalTile(color, number, 2))
      }
    }

    deck.push(createFakeJoker(1))
    deck.push(createFakeJoker(2))

    return deck
  }

  function shuffle(array) {
    for (let i = array.length - 1; i > 0; i--) {
      const j = randomInt(i + 1)
      const tmp = array[i]
      array[i] = array[j]
      array[j] = tmp
    }

    return array
  }

  // =====================================================
  // GÖSTERGE / OKEY
  // =====================================================

  function chooseIndicator(deck) {
    const normalIndexes = []

    deck.forEach((tile, index) => {
      if (tile.type === 'normal') {
        normalIndexes.push(index)
      }
    })

    const randomIndex = normalIndexes[
      randomInt(normalIndexes.length)
    ]

    return deck.splice(randomIndex, 1)[0]
  }

  function getJokerInfo(indicator) {
    return {
      color: indicator.color,
      number: indicator.number === 13
        ? 1
        : indicator.number + 1,
    }
  }

  function isRealJoker(tile, joker) {
    return Boolean(
      tile &&
      joker &&
      tile.type === 'normal' &&
      tile.color === joker.color &&
      tile.number === joker.number
    )
  }

  function getEffectiveTile(tile, joker) {
    if (tile.type === 'fake-joker') {
      return {
        color: joker.color,
        number: joker.number,
        wildcard: false,
        original: tile,
      }
    }

    if (isRealJoker(tile, joker)) {
      return {
        color: null,
        number: null,
        wildcard: true,
        original: tile,
      }
    }

    return {
      color: tile.color,
      number: tile.number,
      wildcard: false,
      original: tile,
    }
  }

  function tileVisibleNumber(tile, joker) {
    if (tile.type === 'fake-joker') {
      return joker.number
    }

    return Number(tile.number) || 0
  }

  // Elde kalan GERÇEK okey 101 ceza değerindedir. Round sonu puanlamada
  // okeyi sıradan taş toplamına gömmek yerine ayrıca izliyoruz; böylece açmış
  // oyuncunun elinde kalan gerçek okey hiçbir score yolunda gözden kaçmaz.
  function tilePenaltyValue(tile, joker) {
    if (isRealJoker(tile, joker)) {
      return 101
    }

    return tileVisibleNumber(tile, joker)
  }

  function getHandPenaltyBreakdown(hand, joker) {
    let regular = 0
    let realJokerCount = 0

    for (const tile of hand || []) {
      if (isRealJoker(tile, joker)) {
        realJokerCount += 1
      }
      else {
        regular += tileVisibleNumber(tile, joker)
      }
    }

    const realJokerPenalty = realJokerCount * 101

    return {
      regular,
      realJokerCount,
      realJokerPenalty,
      total: regular + realJokerPenalty,
    }
  }

  function handValue(hand, joker) {
    return getHandPenaltyBreakdown(hand, joker).total
  }

  // =====================================================
  // SET VALIDATION
  // aynı sayı, 3/4 farklı renk
  // =====================================================

  function validateGroup(tiles, joker) {
    if (!Array.isArray(tiles) || tiles.length < 3 || tiles.length > 4) {
      return null
    }

    const normalized = tiles.map(tile => getEffectiveTile(tile, joker))
    const normal = normalized.filter(tile => !tile.wildcard)
    const wildcards = normalized.filter(tile => tile.wildcard)

    if (normal.length === 0) {
      return null
    }

    const number = normal[0].number

    if (normal.some(tile => tile.number !== number)) {
      return null
    }

    const usedColors = new Set(normal.map(tile => tile.color))

    if (usedColors.size !== normal.length) {
      return null
    }

    const freeColors = COLORS.filter(color => !usedColors.has(color))

    if (wildcards.length > freeColors.length) {
      return null
    }

    const assignments = {}

    for (const item of normal) {
      assignments[item.original.id] = {
        color: item.color,
        number,
      }
    }

    wildcards.forEach((item, index) => {
      assignments[item.original.id] = {
        color: freeColors[index],
        number,
      }
    })

    const arrangedTiles = [...tiles].sort((a, b) => {
      const colorA = assignments[a.id]?.color
      const colorB = assignments[b.id]?.color

      return COLORS.indexOf(colorA) - COLORS.indexOf(colorB)
    })

    return {
      type: 'group',
      score: number * tiles.length,
      number,
      assignments,
      arrangedTiles,
    }
  }

  // =====================================================
  // RUN VALIDATION
  // aynı renk, 3+ ardışık; 13 -> 1 dönüşü yok
  // =====================================================

  function validateRun(tiles, joker) {
    if (!Array.isArray(tiles) || tiles.length < 3 || tiles.length > 13) {
      return null
    }

    const normalized = tiles.map(tile => getEffectiveTile(tile, joker))
    const normal = normalized.filter(tile => !tile.wildcard)

    if (normal.length === 0) {
      return null
    }

    const color = normal[0].color

    if (normal.some(tile => tile.color !== color)) {
      return null
    }

    // DİZİLİŞ KURALDIR: tiles dizisi oyuncunun soldan-sağa gerçek sırasıdır.
    // Server artık 6-5-4 veya 4-6-5 gibi grupları sort edip 4-5-6'ya
    // çevirmiyor. Joker yalnız bulunduğu slotta eksik olan sayıyı temsil eder.
    // Böylece Okey-10-11 => 9-10-11, 10-11-Okey => 10-11-12 olur.
    const length = tiles.length
    const candidates = []

    for (let start = 1; start <= 14 - length; start++) {
      let valid = true
      const assignments = {}

      for (let index = 0; index < normalized.length; index++) {
        const item = normalized[index]
        const expectedNumber = start + index

        if (!item.wildcard && Number(item.number) !== expectedNumber) {
          valid = false
          break
        }

        assignments[item.original.id] = {
          color,
          number: expectedNumber,
        }
      }

      if (!valid) continue

      const sequence = Array.from(
        { length },
        (_, index) => start + index
      )

      candidates.push({
        sequence,
        assignments,
        score: sequence.reduce((total, number) => total + number, 0),
      })
    }

    if (candidates.length === 0) {
      return null
    }

    // Fiziksel slotlar jokerin anlamını neredeyse her zaman tekilleştirir.
    // Birden fazla seçenek kalırsa (teorik olarak yalnız joker-ağırlıklı
    // uç durumlar) soldaki en küçük yasal seri deterministik seçilir.
    candidates.sort((a, b) => a.sequence[0] - b.sequence[0])
    const best = candidates[0]

    return {
      type: 'run',
      score: best.score,
      color,
      sequence: best.sequence,
      assignments: best.assignments,
      // Girdi zaten oyuncunun doğru soldan-sağa dizilişidir; server bunu
      // yeniden sıralamaz. Bu, fiziksel sıra semantiğini korur.
      arrangedTiles: [...tiles],
    }
  }

  // Bot ıstakada fiziksel bir sıra taşımadığı için, elindeki aynı taş setini
  // legal bir sıraya dizip sonra normal authoritative validator'a sunabilir.
  // İnsan istekleri BU fonksiyonu kullanmaz; onlar validateMeld ile gönderilen
  // gerçek sıraya göre doğrulanır.
  function validateBotMeld(tiles, joker) {
    const group = validateGroup(tiles, joker)
    if (group) return group

    if (!Array.isArray(tiles) || tiles.length < 3 || tiles.length > 13) {
      return null
    }

    const normalized = tiles.map(tile => getEffectiveTile(tile, joker))
    const normal = normalized.filter(tile => !tile.wildcard)
    const wildcards = normalized.filter(tile => tile.wildcard)

    if (normal.length === 0) return null

    const color = normal[0].color
    if (normal.some(tile => tile.color !== color)) return null

    const numbers = normal.map(tile => Number(tile.number))
    if (numbers.some(number => !Number.isFinite(number))) return null
    if (new Set(numbers).size !== numbers.length) return null

    for (let start = 14 - tiles.length; start >= 1; start--) {
      const sequence = Array.from(
        { length: tiles.length },
        (_, index) => start + index
      )

      if (!numbers.every(number => sequence.includes(number))) continue

      const missing = sequence.filter(number => !numbers.includes(number))
      if (missing.length !== wildcards.length) continue

      const naturalByNumber = new Map()
      for (const item of normal) {
        naturalByNumber.set(Number(item.number), item.original)
      }

      const arranged = []
      let jokerIndex = 0
      for (const number of sequence) {
        const natural = naturalByNumber.get(number)
        if (natural) arranged.push(natural)
        else arranged.push(wildcards[jokerIndex++].original)
      }

      const validation = validateRun(arranged, joker)
      if (validation) return validation
    }

    return null
  }

  function validateMeld(tiles, joker) {
    return validateGroup(tiles, joker) || validateRun(tiles, joker)
  }

  function meldMetaFromValidation(validation) {
    if (validation.type === 'group') {
      return {
        number: validation.number,
        assignments: validation.assignments,
      }
    }

    return {
      color: validation.color,
      sequence: validation.sequence,
      assignments: validation.assignments,
    }
  }

  function createTableMeld(player, tiles, validation) {
    return {
      ownerId: player.id,
      ownerSeat: player.seat,
      tiles: validation.arrangedTiles,
      type: validation.type,
      meta: meldMetaFromValidation(validation),
    }
  }

  function ensureMeldMeta(meld) {
    if (meld?.meta && meld?.type) {
      return true
    }

    const validation = validateMeld(meld?.tiles || [], game.joker)

    if (!validation) {
      return false
    }

    meld.type = validation.type
    meld.tiles = validation.arrangedTiles
    meld.meta = meldMetaFromValidation(validation)

    return true
  }

  // Joker masaya indikten sonra temsil ettiği konum değiştirilmez.
  // Bu nedenle layoff mevcut meldin meta bilgisini koruyarak yalnız uçtan
  // genişletilir veya sete eksik renk eklenir.
  function previewLayoff(meld, tile, preferredSide = null) {
    if (!meld || !tile || !ensureMeldMeta(meld)) {
      return null
    }

    const effective = getEffectiveTile(tile, game.joker)

    if (meld.type === 'group') {
      // Setlerde okeyin RENK ataması sabit değildir. Yeni doğal 13 geldiğinde
      // 13-13-Okey -> 13-13-13-Okey legal kalabilsin diye seti yeniden
      // doğrularız; okey gerekiyorsa kalan eksik renge kayar.
      const validation = validateGroup([...meld.tiles, tile], game.joker)
      if (!validation) return null

      return {
        tiles: validation.arrangedTiles,
        meta: meldMetaFromValidation(validation),
      }
    }

    if (meld.type === 'run') {
      // Seride ise okeyin SAYI ataması masaya indiği anda sabittir. Yeni taş
      // yalnız mevcut serinin gerçek sol veya sağ ucuna eklenebilir; okey başka
      // boşluğa kaydırılarak ortadaki seri yeniden yorumlanmaz.
      const color = meld.meta.color
      const sequence = [...(meld.meta.sequence || [])].map(Number)
      const assignments = clonePlain(meld.meta.assignments || {})

      if (sequence.length === 0) return null

      const left = sequence[0] - 1
      const right = sequence[sequence.length - 1] + 1
      let assignedNumber = null

      if (effective.wildcard) {
        // Yeni işlenen gerçek okey iki uçtan birini doldurabilir. Client fareyi
        // sol/sağ boş uca götürdüğünde bu tercih authoritative olarak korunur.
        // Bot/eski client side göndermiyorsa eski deterministik sağ-öncelik devam eder.
        const requestedSide = preferredSide === 'left' || preferredSide === 'right'
          ? preferredSide
          : null

        if (requestedSide === 'left') {
          if (left < 1) return null
          assignedNumber = left
        }
        else if (requestedSide === 'right') {
          if (right > 13) return null
          assignedNumber = right
        }
        else if (right <= 13) assignedNumber = right
        else if (left >= 1) assignedNumber = left
      }
      else {
        if (effective.color !== color) return null

        if (left >= 1 && Number(effective.number) === left) {
          assignedNumber = left
        }
        else if (right <= 13 && Number(effective.number) === right) {
          assignedNumber = right
        }
      }

      if (!assignedNumber) return null

      assignments[tile.id] = {
        color,
        number: assignedNumber,
      }

      const nextSequence = assignedNumber === left
        ? [assignedNumber, ...sequence]
        : [...sequence, assignedNumber]

      const nextTiles = assignedNumber === left
        ? [tile, ...meld.tiles]
        : [...meld.tiles, tile]

      return {
        tiles: nextTiles,
        meta: {
          color,
          sequence: nextSequence,
          assignments,
        },
      }
    }

    return null
  }

  // =====================================================
  // ÇİFT VALIDATION
  // Gerçek okey bir eşin yerine joker olarak kullanılabilir.
  // =====================================================

  function validatePair(pair, joker) {
    if (!Array.isArray(pair) || pair.length !== 2) {
      return null
    }

    const [a, b] = pair.map(tile => getEffectiveTile(tile, joker))

    if (a.wildcard && b.wildcard) {
      return {
        color: joker.color,
        number: joker.number,
      }
    }

    if (a.wildcard) {
      return {
        color: b.color,
        number: b.number,
      }
    }

    if (b.wildcard) {
      return {
        color: a.color,
        number: a.number,
      }
    }

    if (
      a.color !== b.color ||
      a.number !== b.number
    ) {
      return null
    }

    return {
      color: a.color,
      number: a.number,
    }
  }

  function validatePairs(pairs, joker) {
    if (!Array.isArray(pairs) || pairs.length === 0) {
      return null
    }

    const representations = []

    for (const pair of pairs) {
      const validation = validatePair(pair, joker)

      if (!validation) {
        return null
      }

      representations.push(validation)
    }

    return representations
  }


  // =====================================================
  // PUAN DEFTERI / CEZA KAYDI
  // =====================================================

  function ensureScoreTracking(player) {
    if (!Array.isArray(player.currentPenaltyEntries)) {
      player.currentPenaltyEntries = []
    }

    if (!Array.isArray(player.scoreLedger)) {
      player.scoreLedger = []
    }
  }

  const SCORE_COLOR_NAMES = Object.freeze({
    red: 'Kırmızı',
    blue: 'Mavi',
    black: 'Siyah',
    yellow: 'Sarı',
  })

  function describeTileForScore(tile) {
    if (!tile) return 'taş'
    if (isRealJoker(tile, game?.joker)) return 'Okey'

    const effective = getEffectiveTile(tile, game?.joker)
    const color = SCORE_COLOR_NAMES[effective?.color] || String(effective?.color || '').trim()
    const number = Number(effective?.number) || tileVisibleNumber(tile, game?.joker)

    return `${color ? `${color} ` : ''}${number || ''}`.trim() || 'taş'
  }

  function addPenalty(player, amount, reason) {
    if (!player || !Number.isFinite(amount) || amount === 0) {
      return
    }

    ensureScoreTracking(player)

    player.penalty += amount
    player.currentPenaltyEntries.push({
      label: reason || 'Kural cezası',
      amount,
    })
  }

  function makeScoreItem(label, amount, kind = 'round') {
    return {
      label,
      amount,
      kind,
    }
  }

  function getPenaltyScoreItems(player) {
    ensureScoreTracking(player)

    return player.currentPenaltyEntries.map(entry =>
      makeScoreItem(
        entry.label,
        entry.amount,
        'penalty'
      )
    )
  }

  function buildRoundScoreDetails(
    winner,
    finishTile,
    options = {}
  ) {
    const {
      stockExhausted = false,
      elden = false,
    } = options

    const details = {}
    const jokerFinish = Boolean(
      winner &&
      finishTile &&
      isRealJoker(finishTile, game.joker)
    )
    const pairFinish = Boolean(
      winner && winner.openType === 'pairs'
    )
    const winnerTeamId = winner
      ? getTeamIdForSeat(winner.seat)
      : null

    for (const player of players.values()) {
      const items = []
      let baseScore = 0
      const isWinnerTeammate = Boolean(
        winner &&
        player.id !== winner.id &&
        winnerTeamId &&
        getTeamIdForSeat(player.seat) === winnerTeamId
      )

      if (stockExhausted || !winner) {
        if (!player.opened) {
          baseScore = 202
          items.push(
            makeScoreItem(
              'Balya bitti: el açılmadı',
              baseScore
            )
          )
        }
        else {
          const handBreakdown =
            getHandPenaltyBreakdown(player.hand, game.joker)
          const multiplier = player.openType === 'pairs' ? 2 : 1
          baseScore = handBreakdown.total * multiplier

          if (handBreakdown.regular > 0 || handBreakdown.realJokerCount === 0) {
            items.push(
              makeScoreItem(
                multiplier > 1
                  ? `Balya bitti: elde kalan normal taşlar ${handBreakdown.regular} ×${multiplier} (çift açma)`
                  : 'Balya bitti: elde kalan taşlar',
                handBreakdown.regular * multiplier
              )
            )
          }

          if (handBreakdown.realJokerCount > 0) {
            const jokerBase = handBreakdown.realJokerPenalty
            items.push(
              makeScoreItem(
                multiplier > 1
                  ? `Balya bitti: elde kalan okey ${jokerBase} ×${multiplier} (çift açma)`
                  : handBreakdown.realJokerCount > 1
                    ? `Balya bitti: elde kalan ${handBreakdown.realJokerCount} okey`
                    : 'Balya bitti: elde kalan okey',
                jokerBase * multiplier
              )
            )
          }
        }
      }
      else if (elden) {
        if (player.id === winner.id) {
          baseScore = jokerFinish ? -808 : -404
          items.push(
            makeScoreItem(
              jokerFinish
                ? 'Elden + okeyle bitiş'
                : 'Elden bitiş',
              baseScore
            )
          )
        }
        else if (isWinnerTeammate) {
          // Eşli oyunda bitiren oyuncunun takım arkadaşı round-sonu el
          // cezası yemez. Daha önce gerçekten işlenmiş +101 vb. bağımsız
          // kural cezaları aşağıdaki penaltyItems ile aynen korunur.
          baseScore = 0
          items.push(
            makeScoreItem(
              'Eş elden bitti: el cezası yok',
              0
            )
          )
        }
        else {
          baseScore = jokerFinish ? 808 : 404
          items.push(
            makeScoreItem(
              jokerFinish
                ? 'Rakip elden + okeyle bitti'
                : 'Rakip elden bitti',
              baseScore
            )
          )
        }
      }
      else if (player.id === winner.id) {
        let winnerMultiplier = 1
        const labels = []

        if (pairFinish) {
          winnerMultiplier *= 2
          labels.push('çiftten')
        }

        if (jokerFinish) {
          winnerMultiplier *= 2
          labels.push('okeyle')
        }

        // Tüm kazanan bitiş puanları iki kat tabanla hesaplanır:
        // normal -202, çiftten/okeyle -404, çiftten+okeyle -808.
        baseScore = -202 * winnerMultiplier

        items.push(
          makeScoreItem(
            labels.length
              ? `${labels.join(' + ')} bitiş`
              : 'Normal bitiş',
            baseScore
          )
        )
      }
      else if (isWinnerTeammate) {
        // Kazananın eşi açmış/açmamış veya elinde kaç puan kalmış olursa
        // olsun bitişten kaynaklanan round-sonu el cezası almaz. Böylece
        // takım raund puanı kazananın -202/-404/-808 değerini gerçekten korur.
        baseScore = 0
        items.push(
          makeScoreItem(
            'Eş bitirdi: el cezası yok',
            0
          )
        )
      }
      else if (!player.opened) {
        baseScore =
          (pairFinish || jokerFinish)
            ? 404
            : 202

        let label = 'El açılmadı'

        if (pairFinish && jokerFinish) {
          label += ': rakip çiftten + okeyle bitti'
        }
        else if (pairFinish) {
          label += ': rakip çiftten bitti'
        }
        else if (jokerFinish) {
          label += ': rakip okeyle bitti'
        }

        items.push(
          makeScoreItem(label, baseScore)
        )
      }
      else {
        const handBreakdown =
          getHandPenaltyBreakdown(player.hand, game.joker)
        let multiplier = 1
        const multiplierReasons = []

        if (player.openType === 'pairs') {
          multiplier *= 2
          multiplierReasons.push('çift açma')
        }

        if (pairFinish) {
          multiplier *= 2
          multiplierReasons.push('rakip çiftten bitti')
        }

        if (jokerFinish) {
          multiplier *= 2
          multiplierReasons.push('rakip okeyle bitti')
        }

        baseScore = handBreakdown.total * multiplier

        if (handBreakdown.regular > 0 || handBreakdown.realJokerCount === 0) {
          items.push(
            makeScoreItem(
              multiplier > 1
                ? `Elde kalan normal taşlar ${handBreakdown.regular} ×${multiplier} (${multiplierReasons.join(', ')})`
                : 'Elde kalan taşlar',
              handBreakdown.regular * multiplier
            )
          )
        }

        if (handBreakdown.realJokerCount > 0) {
          const jokerBase = handBreakdown.realJokerPenalty
          items.push(
            makeScoreItem(
              multiplier > 1
                ? `Elde kalan okey ${jokerBase} ×${multiplier} (${multiplierReasons.join(', ')})`
                : handBreakdown.realJokerCount > 1
                  ? `Elde kalan ${handBreakdown.realJokerCount} okey`
                  : 'Elde kalan okey',
              jokerBase * multiplier
            )
          )
        }
      }

      const penaltyItems =
        getPenaltyScoreItems(player)

      items.push(...penaltyItems)

      const total = items.reduce(
        (sum, item) => sum + item.amount,
        0
      )

      details[player.id] = {
        round: game.round,
        reason:
          options.reason ||
          game.roundEndReason ||
          (winner ? 'player-finished' : 'stock-exhausted'),
        total,
        items,
      }
    }

    return details
  }

  function appendScoreLedger(details) {
    for (const player of players.values()) {
      ensureScoreTracking(player)

      const detail = details[player.id]

      if (!detail) {
        continue
      }

      player.scoreLedger.push(
        clonePlain(detail)
      )
    }
  }

  // =====================================================
  // GAME / PLAYER STATE
  // =====================================================

  function createGame() {
    return {
      round: 0,
      maxRounds: MAX_ROUNDS,
      dealerSeat: null,
      starterSeat: null,
      currentSeat: null,
      phase: 'waiting',
      stock: [],
      indicator: null,
      joker: null,
      indicatorPairUsed: false,
      indicatorPairOwnerId: null,
      discardPile: [],
      lastDiscardOwnerId: null,
      lastDiscardOwnerSeat: null,
      // Son discard atıldığı anda masadaki normal perlerden birine işlenebilir miydi?
      // Böyle bir taş yandan alınamaz.
      lastDiscardWasPlayable: false,
      tableMelds: [],
      pairOpens: [],
      roundWinner: null,
      roundEndReason: null,
      roundEndSummary: null,
      lastRoundScores: null,
      lastRoundTeamScores: null,
      teamMode: 'partners',
      matchWinner: null,
      matchWinners: [],
      matchWinnerTeam: null,
      matchWinnerTeams: [],
      // Maç bittiği anda takım üyeleri ve puanları burada dondurulur. Lobby'de
      // seat swap/nick değişimi sonucun geçmişini yeniden yazmamalıdır.
      matchFinalTeams: null,
      turnCounter: 0,
      transitionToken: 0,
      // Aktif elde bot/oyuncu kadrosu değişirse mevcut skoru sıfırlamadan
      // güvenli bir yeniden dağıtım için hangi round seçenekleriyle devam
      // edeceğimizi burada tutuyoruz.
      rosterResumeOptions: null,
      // İnsan oyuncu ayrılıp masa tekrar dolduğunda yeni maç başlatılıyorsa
      // eski puan defteri/round toplamları kesinlikle taşınmasın.
      resetMatchOnRosterResume: false,
      // Bir oyuncu ilk açılışa başladığında tüm client kameraları o oyuncunun
      // sırası bitene kadar burada kilitli kalır. Bot açılışı da aynı yolu kullanır.
      openingCameraLockSeat: null,
    }
  }

  function resetTurnState(player) {
    player.turnHasAcquiredTile = false
    player.turnTableActions = 0
    player.turnLayoffHistory = []
    player.finalIndicatorId = null
    player.finalIndicatorSnapshot = null
    player.openingDraftLockedCore = []
  }

  function clearPickedDiscardState(player) {
    player.pickedDiscardId = null
    player.pickedDiscardSourceId = null
    player.pickedDiscardRequiresOpening = false
  }

  function resetPlayerRound(player) {
    player.hand = []
    player.opened = false
    player.openType = null
    player.penalty = 0
    player.currentPenaltyEntries = []
    player.mustDiscard = false
    player.openedAllAtOnceTurn = null
    player.openedAllAtOnceNoOtherOpen = false
    player.openingDraft = []
    player.openingDraftLockedCore = []
    player.botOpeningWaitCount = 0
    player.botOpeningDecisionTurn = null
    player.botOpeningAllowedThisTurn = null
    player.botOpeningDecisionMeta = null
    clearPickedDiscardState(player)
    resetTurnState(player)
  }

  function startRound(options = {}) {
    const {
      countRound = true,
      rotateDealer = true,
    } = options

    if (countRound) {
      game.round++
    }

    game.phase = 'playing'
    game.tableMelds = []
    game.pairOpens = []
    game.discardPile = []
    game.lastDiscardOwnerId = null
    game.lastDiscardOwnerSeat = null
    game.lastDiscardWasPlayable = false
    game.openingCameraLockSeat = null
    game.indicatorPairUsed = false
    game.indicatorPairOwnerId = null
    game.roundWinner = null
    game.roundEndReason = null
    game.roundEndSummary = null
    game.lastRoundScores = null
    game.lastRoundTeamScores = null
    game.matchWinner = null
    game.matchWinners = []
    game.matchWinnerTeam = null
    game.matchWinnerTeams = []
    game.matchFinalTeams = null
    game.turnCounter++

    for (const player of players.values()) {
      resetPlayerRound(player)
    }

    if (!game.dealerSeat) {
      game.dealerSeat = SEATS[
        randomInt(SEATS.length)
      ]
    }
    else if (rotateDealer) {
      // SEATS oyun sırasını saat yönünün tersine tutuyor. Masada önceki
      // raundu başlatan oyuncunun SAĞINDAKİ oyuncunun başlaması için dealer
      // fiziksel olarak saat yönünde, yani previousSeat() yönünde dönmeli.
      // starterSeat = nextSeat(dealerSeat) ilişkisini koruduğumuz için 22 taşı
      // alan oyuncu da her yeni dağıtımda önceki starter'ın sağına geçer.
      game.dealerSeat = previousSeat(game.dealerSeat)
    }

    game.starterSeat = nextSeat(game.dealerSeat)
    game.currentSeat = game.starterSeat

    let deck = shuffle(createDeck())

    game.indicator = chooseIndicator(deck)
    game.joker = getJokerInfo(game.indicator)
    deck = shuffle(deck)

    // 4 oyuncuya 21'er taş = 84.
    for (let pass = 0; pass < 21; pass++) {
      for (const seat of SEATS) {
        const player = getSeatPlayer(seat)
        player.hand.push(deck.pop())
      }
    }

    // Dağıtıcının sağındaki başlangıç oyuncusu 22 taşla başlar.
    const starter = getSeatPlayer(game.starterSeat)
    starter.hand.push(deck.pop())
    starter.mustDiscard = true

    game.stock = deck

    if (game.stock.length !== INITIAL_STOCK_COUNT) {
      throw new Error(
        `101 Okey dağıtım hatası: beklenen orta taş ${INITIAL_STOCK_COUNT}, oluşan ${game.stock.length}`
      )
    }

    console.log(`ROUND ${game.round}`)
    console.log('Gösterge:', game.indicator)
    console.log('Okey:', game.joker)
    console.log('Ortadaki çekilebilir taş:', game.stock.length)

    broadcastGameState()
    scheduleBotTurnIfNeeded()
  }

  function startMatch() {
    game = createGame()

    for (const player of players.values()) {
      player.totalScore = 0
      player.roundScores = []
      player.scoreLedger = []
      player.currentPenaltyEntries = []
      // Çay yalnız YENİ MAÇ tamamen baştan başladığında dolar.
      // Normal raund geçişlerinde bu değer korunur.
      player.teaLevel = 1
      player.teaBusyUntil = 0
    }

    startRound()
  }

  function pauseForRosterChange() {
    if (!game) return

    if (game.phase === 'playing') {
      // El tamamlanmadan kadro değişti: puan yazmadan aynı round numarasını
      // yeniden dağıt. Dealer/starter da aynı kalsın.
      game.rosterResumeOptions = {
        countRound: false,
        rotateDealer: false,
      }
      game.phase = 'waiting'
      resetHumanReadyState()
      game.transitionToken++
      return
    }

    if (game.phase === 'round-ended') {
      // El zaten skorlandıysa sıradaki eli normal rotasyonla başlat.
      game.rosterResumeOptions = {
        countRound: true,
        rotateDealer: true,
      }
      game.phase = 'waiting'
      resetHumanReadyState()
      game.transitionToken++
    }
  }

  function resetMatchToFreshLobbyAfterHumanLeave() {
    // Aktif maçta gerçek oyuncu ayrılırsa o maç artık devam ettirilmez.
    // Eski round/skor/el state'ini lobby ekranına taşımadan tamamen temizle;
    // yeni kadro ancak herkes tekrar hazır verdikten sonra Round 1'den başlar.
    const nextGame = createGame()
    nextGame.transitionToken = Number(game?.transitionToken || 0) + 1
    game = nextGame

    for (const player of players.values()) {
      resetPlayerRound(player)
      player.totalScore = 0
      player.roundScores = []
      player.scoreLedger = []
      player.currentPenaltyEntries = []
      player.ready = Boolean(player.isBot)
    }
  }

  function returnCompletedMatchToLobby() {
    if (!game || game.phase !== 'match-ended') {
      return false
    }

    // Match sonucu artık yalnız bir client overlay'i değildir. DEVAM ET ile
    // server da gerçek waiting/lobby state'ine geçer; eski el, round ve skor
    // snapshot'ları yeni maça sızamaz. Socket/player kimlikleri, nickler,
    // koltuklar ve bot kadrosu ise aynı masada kalır.
    const nextGame = createGame()
    nextGame.transitionToken = Number(game.transitionToken || 0) + 1
    game = nextGame

    for (const player of players.values()) {
      resetPlayerRound(player)
      player.totalScore = 0
      player.roundScores = []
      player.scoreLedger = []
      player.currentPenaltyEntries = []
      player.ready = Boolean(player.isBot)
    }

    clearKickVote()
    broadcastLobbyReadyReset('match-completed')
    io.emit('players-state', getPublicPlayers())
    broadcastGameState()
    return true
  }

  function startOrResumeWhenTableIsFull() {
    if (players.size !== MAX_PLAYERS) return false
    if (!areAllHumanPlayersReady()) return false

    if (game?.phase === 'waiting' && game.rosterResumeOptions) {
      if (game.resetMatchOnRosterResume) {
        // İnsan oyuncu ayrıldığı için masa yeniden kuruluyorsa bu artık yeni maçtır.
        // Puan defteri, toplamlar ve round geçmişi sıfırdan başlar.
        startMatch()
        return true
      }

      const options = game.rosterResumeOptions
      game.rosterResumeOptions = null
      startRound(options)
      return true
    }

    if (!game || game.phase === 'waiting') {
      startMatch()
      return true
    }

    return false
  }

  // =====================================================
  // PRIVATE / PUBLIC STATE
  // =====================================================

  function sendHand(player) {
    const draftStatus = getOpeningDraftStatus(player)

    io.to(player.id).emit(
      'hand-state',
      {
        hand: player.hand,
        opened: player.opened,
        openType: player.openType,
        penalty: player.penalty,
        mustDiscard: player.mustDiscard,
        turnHasAcquiredTile: Boolean(player.turnHasAcquiredTile),
        pickedDiscardId: player.pickedDiscardId,
        finalIndicatorId: player.finalIndicatorId,
        // Resmi açılış discardta commit edilir; fakat doğru 101/5 çift masadaysa
        // aynı tur içinde işleme önizlemesi/hamlesi açılabilir.
        openingDraftReady: draftStatus.ready,
        openingDraftType: draftStatus.type,
        openingDraftScore: draftStatus.score,
      }
    )
  }

  function getPublicPlayers() {
    return [...players.values()].map(player => {
      const publicDraftHandIds = getOpeningDraftHandIdSet(player)

      return {
        id: player.id,
        name: player.name,
        seat: player.seat,
        teamId: getTeamIdForSeat(player.seat),
        isBot: Boolean(player.isBot),
        ready: Boolean(player.isBot || player.ready),
        teaLevel: getPublicTeaLevel(player),
        lookX: player.lookX,
        lookY: player.lookY,
        // Taslakta masaya bırakılan gerçek el taşları artık herkese açık olduğu
        // için gizli ıstaka sayısından düşülür.
        tileCount: Math.max(
          0,
          (player.hand ? player.hand.length : 0) - publicDraftHandIds.size
        ),
        opened: player.opened,
        openType: player.openType,
        roundPenalty: player.penalty,
        currentPenaltyEntries: player.currentPenaltyEntries || [],
        totalScore: player.totalScore,
        roundScores: player.roundScores,
        scoreLedger: player.scoreLedger || [],
      }
    })
  }

  function broadcastGameState() {
    if (!game) {
      return
    }

    io.emit(
      'game-state',
      {
        rulesProfile: RULES_PROFILE,
        round: game.round,
        maxRounds: game.maxRounds,
        phase: game.phase,
        dealerSeat: game.dealerSeat,
        starterSeat: game.starterSeat,
        currentSeat: game.currentSeat,
        indicator: game.indicator,
        joker: game.joker,
        stockCount: game.stock.length,
        initialStockCount: INITIAL_STOCK_COUNT,
        finalIndicatorAvailable: false,
        indicatorPairUsed: Boolean(game.indicatorPairUsed),
        indicatorPairOwnerId: game.indicatorPairOwnerId,
        openingDrafts: getPublicOpeningDrafts(),
        activeOpeningSeat: getActiveOpeningSeat(),
        discardTop: game.discardPile.at(-1) || null,
        discardTopPlayable: Boolean(game.lastDiscardWasPlayable),
        lastDiscardOwnerId: game.lastDiscardOwnerId,
        lastDiscardOwnerSeat: game.lastDiscardOwnerSeat,
        tableMelds: game.tableMelds,
        pairOpens: game.pairOpens,
        players: getPublicPlayers(),
        teamMode: game.teamMode,
        teams: game.phase === 'match-ended' && Array.isArray(game.matchFinalTeams)
          ? clonePlain(game.matchFinalTeams)
          : getPublicTeams(),
        roundWinner: game.roundWinner,
        roundEndReason: game.roundEndReason,
        roundEndSummary: game.roundEndSummary,
        roundEndDisplayMs: Math.min(2000, ROUND_END_HOLD_MS - 100),
        lastRoundScores: game.lastRoundScores,
        lastRoundTeamScores: game.lastRoundTeamScores,
        matchWinner: game.matchWinner,
        matchWinners: game.matchWinners,
        matchWinnerTeam: game.matchWinnerTeam,
        matchWinnerTeams: game.matchWinnerTeams,
      }
    )

    for (const player of players.values()) {
      sendHand(player)
    }
  }

  // =====================================================
  // TURN / HAND HELPERS
  // =====================================================

  function getCurrentPlayer(socket) {
    if (!game || game.phase !== 'playing') {
      return null
    }

    const player = players.get(socket.id)

    if (!player || player.seat !== game.currentSeat) {
      return null
    }

    return player
  }

  function handTilesFromIds(player, ids) {
    if (!Array.isArray(ids)) {
      return null
    }

    if (new Set(ids).size !== ids.length) {
      return null
    }

    const result = []

    for (const id of ids) {
      const tile = player.hand.find(item => item.id === id)

      if (!tile) {
        return null
      }

      result.push(tile)
    }

    return result
  }

  function removeTilesFromHand(player, ids) {
    const idSet = new Set(ids)

    player.hand = player.hand.filter(
      tile => !idSet.has(tile.id)
    )
  }

  function requirePostDrawAction(player) {
    if (player.mustDiscard) {
      return null
    }

    return {
      ok: false,
      message:
        'Önce ortadan taş çekmeli veya önceki oyuncunun attığı taşı almalısın.',
    }
  }

  function requireAcquiredTileForInitialOpening(player) {
    if (player?.opened || player?.turnHasAcquiredTile) return null

    return {
      ok: false,
      message: 'Elini açmadan önce bu tur bir taş çekmeli veya yandan taş almalısın.',
    }
  }

  function allPlayersOpenedPairs() {
    return (
      players.size === MAX_PLAYERS &&
      [...players.values()].every(
        player => player.opened && player.openType === 'pairs'
      )
    )
  }

  // =====================================================
  // CANLI AÇILIŞ TASLAĞI / ÇİFTTE GÖSTERGE JOKERİ
  // =====================================================

  function isIndicatorTwinForIndicator(tile, indicator) {
    return Boolean(
      tile &&
      indicator &&
      tile.id !== indicator.id &&
      tile.type === 'normal' &&
      tile.color === indicator.color &&
      Number(tile.number) === Number(indicator.number)
    )
  }

  function isIndicatorTwinTile(tile) {
    return isIndicatorTwinForIndicator(tile, game?.indicator)
  }

  function getOpeningDraftHandIdSet(player) {
    const ids = new Set()

    for (const group of player?.openingDraft || []) {
      for (const id of group.tileIds || []) {
        ids.add(id)
      }
    }

    return ids
  }

  // Özel çift kuralı: masadaki açık gösterge DEĞİL, destede kalan aynı
  // renk/sayıdaki ikinci fiziksel taş çift açılışında tek seferlik eş jokeridir.
  // Örn. açık gösterge mavi 5 ise eldeki diğer mavi 5 + herhangi bir taş,
  // yalnız ilk çift açılışında geçerli bir çift sayılabilir.
  function validateOpeningPair(pair, player, allowIndicatorTwinWildcard = !player?.opened) {
    if (!Array.isArray(pair) || pair.length !== 2) return null

    // Önce normal çift/gerçek-okey kuralını dene. Gösterge-eşi özel hakkı
    // yalnız normalde çift olmayan iki taşı ilk çift açılışında tamamlar.
    const naturalValidation = validatePair(pair, game.joker)
    if (naturalValidation) return naturalValidation

    const twinCount = pair.filter(isIndicatorTwinTile).length

    if (
      !allowIndicatorTwinWildcard ||
      twinCount !== 1 ||
      game.indicatorPairUsed
    ) {
      return null
    }

    const mate = pair.find(tile => !isIndicatorTwinTile(tile))
    if (!mate) return null

    const effectiveMate = getEffectiveTile(mate, game.joker)

    return {
      color: effectiveMate.color,
      number: effectiveMate.number,
      indicatorWildcard: true,
      indicatorTwinId: pair.find(isIndicatorTwinTile)?.id || null,
    }
  }

  function sanitizeOpeningDraft(player, rawGroups) {
    if (!Array.isArray(rawGroups)) {
      return { ok: false, message: 'Açılış taslağı geçersiz.' }
    }

    if (rawGroups.length > 12) {
      return { ok: false, message: 'Açılış taslağında çok fazla grup var.' }
    }

    const usedIds = new Set()
    let indicatorUseCount = 0
    const groups = []

    for (let index = 0; index < rawGroups.length; index++) {
      const raw = rawGroups[index] || {}
      const tileIds = Array.isArray(raw.tileIds)
        ? raw.tileIds.map(String)
        : []

      if (tileIds.length < 2 || tileIds.length > 13) {
        return { ok: false, message: 'Taslak gruplarından biri geçersiz.' }
      }

      if (tileIds.some(id => usedIds.has(id))) {
        return { ok: false, message: 'Aynı taş iki taslak grupta kullanılamaz.' }
      }

      tileIds.forEach(id => usedIds.add(id))

      const tiles = handTilesFromIds(player, tileIds)
      if (!tiles) {
        return { ok: false, message: 'Taslak taşlarından biri elde bulunamadı.' }
      }

      let kind
      let meldType = null
      let meldMeta = null

      if (tiles.length === 2) {
        const pairValidation = validateOpeningPair(tiles, player, true)
        if (!pairValidation) {
          return { ok: false, message: 'Masaya yalnız geçerli per veya çift bırakılabilir.' }
        }
        kind = 'pair'
        if (pairValidation.indicatorWildcard) indicatorUseCount++
      }
      else if (tiles.length >= 3) {
        const meldValidation = validateMeld(tiles, game.joker)
        if (!meldValidation) {
          return { ok: false, message: 'Masaya yalnız geçerli per veya çift bırakılabilir.' }
        }
        kind = 'meld'
        meldType = meldValidation.type
        meldMeta = meldMetaFromValidation(meldValidation)
      }
      else {
        return { ok: false, message: 'Masaya yalnız geçerli per veya çift bırakılabilir.' }
      }

      const placement = raw.placement && typeof raw.placement === 'object'
        ? {
            row: Math.max(0, Math.min(5, Number(raw.placement.row) || 0)),
            startCol: Math.max(0, Math.min(12, Number(raw.placement.startCol) || 0)),
            kind,
            seat: player.seat,
          }
        : null

      groups.push({
        stageId: String(raw.stageId || `server-stage-${index + 1}`).slice(0, 80),
        tileIds,
        kind,
        placement,
        meldType,
        meldMeta,
      })
    }

    if (indicatorUseCount > 1) {
      return { ok: false, message: 'Gösterge-eşi taş yalnız bir çiftte kullanılabilir.' }
    }

    if (usedIds.size >= player.hand.length) {
      return { ok: false, message: 'Turu bitirmek için elde en az bir discard taşı kalmalı.' }
    }

    return { ok: true, groups }
  }

  function getOpeningDraftStatus(player, draft = player?.openingDraft || []) {
    if (!player || !Array.isArray(draft) || draft.length === 0) {
      return { ready: false, type: null, score: 0 }
    }

    const initialOpen = !player.opened
    const flatIds = draft.flatMap(group => group.tileIds || [])
    const handIds = [...flatIds]

    // İlk açılışta yandan alınan taş mutlaka açılışın içinde bulunmalıdır.
    // Oyuncu zaten açılmışsa yeni per taslağının geçerliliği bundan bağımsızdır;
    // yandan alınan taşın gerçekten kullanılıp kullanılmadığı ayrı helper ile izlenir.
    const usesPickedDiscard = (
      !player.pickedDiscardRequiresOpening ||
      !player.pickedDiscardId ||
      handIds.includes(player.pickedDiscardId)
    )

    if (initialOpen && !usesPickedDiscard) {
      return { ready: false, type: null, score: 0 }
    }

    const allMelds = draft.every(group => group.kind === 'meld')
    if (allMelds) {
      if (!initialOpen && player.openType === 'pairs') {
        return { ready: false, type: 'normal', score: 0 }
      }

      let totalScore = 0

      for (const group of draft) {
        const tiles = handTilesFromIds(player, group.tileIds)
        const validation = tiles && validateMeld(tiles, game.joker)
        if (!validation) return { ready: false, type: 'normal', score: 0 }
        totalScore += validation.score
      }

      if (!initialOpen) {
        return {
          ready: true,
          type: 'normal',
          score: totalScore,
          openingAll21AtOnce: false,
        }
      }

      const openingAll21AtOnce = (
        player.hand.length === 22 &&
        handIds.length === 21 &&
        handIds.length === player.hand.length - 1
      )

      return {
        ready: totalScore >= 101 || openingAll21AtOnce,
        type: 'normal',
        score: totalScore,
        openingAll21AtOnce,
      }
    }

    const allPairs = draft.every(group => group.kind === 'pair')
    if (allPairs) {
      if (!initialOpen && player.openType === 'normal') {
        return { ready: false, type: 'pairs', score: 0 }
      }

      const minimumPairCount = initialOpen ? 5 : 1
      if (draft.length < minimumPairCount) {
        return { ready: false, type: 'pairs', score: 0 }
      }

      let indicatorUseCount = 0
      for (const group of draft) {
        const pair = handTilesFromIds(player, group.tileIds)
        const validation = pair && validateOpeningPair(pair, player, initialOpen)
        if (!validation) return { ready: false, type: 'pairs', score: 0 }
        if (validation.indicatorWildcard) indicatorUseCount++
      }

      return {
        ready: !initialOpen || indicatorUseCount <= 1,
        type: 'pairs',
        score: 0,
      }
    }

    return { ready: false, type: null, score: 0 }
  }

  function canPlayerProcessTable(player) {
    return Boolean(player?.opened || getOpeningDraftStatus(player).ready)
  }

  function getReadyOpeningDraftHandIds(player) {
    if (!getOpeningDraftStatus(player).ready) {
      return new Set()
    }
    return getOpeningDraftHandIdSet(player)
  }

  function openingDraftUsesPickedDiscard(player) {
    if (!player?.pickedDiscardId) return false
    return getReadyOpeningDraftHandIds(player).has(player.pickedDiscardId)
  }

  function isTileReservedInReadyOpeningDraft(player, tileId) {
    return Boolean(tileId && getReadyOpeningDraftHandIds(player).has(tileId))
  }

  function getAvailableHandCountAfterReadyDraft(player) {
    return Math.max(0, (player?.hand?.length || 0) - getReadyOpeningDraftHandIds(player).size)
  }

  function lockReadyOpeningDraft(player) {
    if (!player || !getOpeningDraftStatus(player).ready) return
    if (Array.isArray(player.openingDraftLockedCore) && player.openingDraftLockedCore.length > 0) return
    player.openingDraftLockedCore = clonePlain(player.openingDraft || [])
  }

  function draftContainsLockedCore(nextDraft, lockedCore) {
    if (!Array.isArray(lockedCore) || lockedCore.length === 0) return true
    if (!Array.isArray(nextDraft)) return false

    return lockedCore.every(coreGroup => {
      const coreIds = [...(coreGroup.tileIds || [])].map(String).sort()
      return nextDraft.some(group => {
        if (group.kind !== coreGroup.kind) return false
        const ids = [...(group.tileIds || [])].map(String).sort()
        return ids.length === coreIds.length && ids.every((id, index) => id === coreIds[index])
      })
    })
  }

  function setOpeningDraft(player, rawGroups) {
    const turnError = requirePostDrawAction(player)
    if (turnError) return turnError

    const acquireError = requireAcquiredTileForInitialOpening(player)
    if (acquireError) return acquireError

    const previousDraft = Array.isArray(player.openingDraft)
      ? player.openingDraft
      : []
    const previousStatus = getOpeningDraftStatus(player, previousDraft)

    const sanitized = sanitizeOpeningDraft(player, rawGroups)
    if (!sanitized.ok) return sanitized

    const collectingInvalidInitialDraft = Boolean(
      !player.opened &&
      previousDraft.length > 0 &&
      !previousStatus.ready &&
      sanitized.groups.length === 0
    )

    const lockedCore = Array.isArray(player.openingDraftLockedCore)
      ? player.openingDraftLockedCore
      : []

    if (lockedCore.length > 0) {
      const nextStatus = getOpeningDraftStatus(player, sanitized.groups)
      if (!nextStatus.ready || !draftContainsLockedCore(sanitized.groups, lockedCore)) {
        return {
          ok: false,
          message: 'Masaya koyduğun geçerli perlere dayanarak işleme yaptığın için bu perleri artık geri çekemezsin.',
        }
      }
    }

    player.openingDraft = sanitized.groups

    if (
      !player.opened &&
      player.openingDraft.length > 0 &&
      game?.currentSeat === player.seat
    ) {
      // Otomatik kamera yalnız oyuncunun İLK açılışında tetiklenir. Sonraki
      // turlarda yeni per eklemesi diğer oyuncuların kamerasını çekmez.
      game.openingCameraLockSeat = player.seat
    }
    else if (
      player.openingDraft.length === 0 &&
      game?.openingCameraLockSeat === player.seat
    ) {
      game.openingCameraLockSeat = null
    }

    if (collectingInvalidInitialDraft) {
      addPenalty(player, 101, 'Yanlış/eksik açmayı geri topladı')
    }

    const status = getOpeningDraftStatus(player)

    return {
      ok: true,
      groupCount: player.openingDraft.length,
      openingDraftReady: status.ready,
      openingDraftType: status.type,
      openingDraftScore: status.score,
      penalty: collectingInvalidInitialDraft ? 101 : 0,
      message: collectingInvalidInitialDraft
        ? 'Yanlış/eksik açılışı geri topladın. +101 ceza.'
        : undefined,
    }
  }

  function clearOpeningDraft(player) {
    if (!player) return
    player.openingDraft = []
    player.openingDraftLockedCore = []
  }

  function getPublicOpeningDrafts() {
    const result = []

    for (const player of players.values()) {
      for (const group of player.openingDraft || []) {
        const tiles = group.tileIds
          .map(id => player.hand.find(tile => tile.id === id) || null)
          .filter(Boolean)

        if (tiles.length !== group.tileIds.length) continue

        result.push({
          stageId: group.stageId,
          ownerId: player.id,
          ownerSeat: player.seat,
          kind: group.kind,
          placement: group.placement,
          pendingOpening: true,
          meldType: group.meldType || null,
          meldMeta: group.meldMeta || null,
          tiles: clonePlain(tiles),
        })
      }
    }

    return result
  }

  function getActiveOpeningSeat() {
    if (
      game?.phase === 'playing' &&
      game.openingCameraLockSeat &&
      game.openingCameraLockSeat === game.currentSeat
    ) {
      return game.openingCameraLockSeat
    }

    const current = getSeatPlayer(game?.currentSeat)
    return (!current?.opened && current?.openingDraft?.length) ? current.seat : null
  }

  function commitOpeningDraft(player) {
    const draft = Array.isArray(player?.openingDraft)
      ? player.openingDraft
      : []

    if (draft.length === 0) {
      return { ok: true, committed: false }
    }

    const groups = draft.map(group => [...group.tileIds])
    const allMelds = draft.every(group => group.kind === 'meld')
    const allPairs = draft.every(group => group.kind === 'pair')
    const initialOpen = !player.opened

    const penaltyBefore = Number(player.penalty) || 0
    let result

    if (allMelds) {
      result = attemptOpenMelds(player, groups)
    }
    else if (allPairs) {
      result = attemptOpenPairs(player, groups)
    }
    else {
      if (initialOpen) {
        addPenalty(player, 101, 'Karışık/yanlış açma denemesi')
      }

      result = {
        ok: false,
        penalty: initialOpen ? 101 : 0,
        message: initialOpen
          ? 'Normal perler ile çiftler aynı ilk açılışta karıştırılamaz. +101 ceza.'
          : 'Bu açılış taslağı mevcut açma türünle uyumlu değil.',
      }
    }

    // İlk açılışta masaya gerçekten bir taslak bırakıp discard ile onaylamaya
    // çalışan oyuncu başarısızsa her durumda +101 yanlış açma cezası alır.
    // Alt validator zaten ceza yazdıysa ikinci kez yazmayız.
    if (initialOpen && !result?.ok && (Number(player.penalty) || 0) === penaltyBefore) {
      addPenalty(player, 101, 'Yanlış/eksik açma denemesi')
      result = {
        ...result,
        penalty: 101,
        message: `${result?.message || 'Açılış geçersiz.'} +101 yanlış açma cezası.`,
      }
    }

    clearOpeningDraft(player)

    return {
      ...result,
      committed: Boolean(result?.ok),
    }
  }

  // =====================================================
  // YANDAN ALINAN TAŞIN KULLANIMI
  // =====================================================

  function applyPickedDiscardSourcePenalty(player, usedTile, multiplier = 1) {
    if (
      !APPLY_WIKI_TAKEN_DISCARD_SOURCE_PENALTY ||
      !player.pickedDiscardSourceId ||
      !usedTile
    ) {
      return
    }

    const source = getPlayerById(player.pickedDiscardSourceId)

    if (!source) {
      return
    }

    // Gerçek okey kendi discard anında zaten sabit +101 ceza yazar. O okeyi
    // yandaki oyuncu daha sonra ilk açılışında kullansa bile atan kişiye
    // sayı x10 / çift açılışı x20 kaynak cezası ikinci kez uygulanmaz.
    if (isRealJoker(usedTile, game.joker)) {
      return
    }

    const value = tileVisibleNumber(usedTile, game.joker)
    const safeMultiplier = Math.max(1, Number(multiplier) || 1)

    if (value > 0) {
      addPenalty(
        source,
        value * 10 * safeMultiplier,
        safeMultiplier > 1
          ? `Yandan alınan ${value} çift açılışında kullanıldı (x${safeMultiplier})`
          : `Yandan alınan ${value} kullanıldı`
      )
    }
  }

  function markPickedDiscardUsed(
    player,
    usedTiles,
    options = {}
  ) {
    if (!player.pickedDiscardId) {
      return
    }

    const usedTile = usedTiles.find(
      tile => tile.id === player.pickedDiscardId
    )

    if (!usedTile) {
      return
    }

    // Yandan alınan taşın sayı x10 cezası yalnızca bu taşla İLK KEZ
    // açılırken taşı atan oyuncuya yazılır. Oyuncu zaten açmışsa aynı kişiden
    // sonraki turlarda alınan taşla yeni per/işleme yapılması ikinci kez kaynak
    // cezası doğurmaz. Taşın zorunlu kullanım durumu yine temizlenir.
    if (options.applySourcePenalty) {
      applyPickedDiscardSourcePenalty(
        player,
        usedTile,
        options.sourcePenaltyMultiplier
      )
    }

    clearPickedDiscardState(player)
  }

  // =====================================================
  // NORMAL 101 AÇILIŞ
  // =====================================================

  function attemptOpenMelds(player, meldIdGroups) {
    const turnError = requirePostDrawAction(player)

    if (turnError) {
      return turnError
    }

    const acquireError = requireAcquiredTileForInitialOpening(player)
    if (acquireError) return acquireError

    if (player.openType === 'pairs') {
      return {
        ok: false,
        message: 'Çifte açtıktan sonra yeni normal per açılamaz.',
      }
    }

    if (!Array.isArray(meldIdGroups) || meldIdGroups.length === 0) {
      return {
        ok: false,
        message: 'Açılacak per yok.',
      }
    }

    const initialOpen = !player.opened
    const allIds = meldIdGroups.flat()

    if (new Set(allIds).size !== allIds.length) {
      return {
        ok: false,
        message: 'Aynı taş iki kez kullanılamaz.',
      }
    }

    // Her tur mutlaka son bir taş atılarak tamamlanır.
    if (allIds.length >= player.hand.length) {
      return {
        ok: false,
        message: 'Bütün taşları yere indiremezsin; turu bitirmek için bir taş atmalısın.',
      }
    }

    if (
      player.pickedDiscardRequiresOpening &&
      player.pickedDiscardId &&
      !allIds.includes(player.pickedDiscardId)
    ) {
      return {
        ok: false,
        message: 'Yandan aldığın taşı bu açılışta kullanmalısın veya geri koymalısın.',
      }
    }

    const melds = []
    const usedTiles = []
    let totalScore = 0

    for (const idGroup of meldIdGroups) {
      const tiles = handTilesFromIds(player, idGroup)

      if (!tiles) {
        return {
          ok: false,
          message: 'Taşlardan biri elde bulunamadı.',
        }
      }

      const validation = validateMeld(tiles, game.joker)

      if (!validation) {
        if (initialOpen) {
          addPenalty(
            player,
            101,
            'Geçersiz per ile açma denemesi'
          )
        }

        return {
          ok: false,
          penalty: initialOpen ? 101 : 0,
          message: initialOpen
            ? 'Geçersiz per ile açma denemesi. +101 ceza.'
            : 'Geçersiz per.',
        }
      }

      totalScore += validation.score
      usedTiles.push(...tiles)
      melds.push({ tiles, validation })
    }

    const noOtherPlayerHadOpened = initialOpen &&
      [...players.values()].every(
        other => other.id === player.id || !other.opened
      )

    // 22 taşlık elde tek hamlede 21 taşın tamamını geçerli perler halinde
    // yere koyabiliyorsa, özel "elden açma" kuralıyla 101 altı da kabul edilir.
    const openingAll21AtOnce = (
      initialOpen &&
      player.hand.length === 22 &&
      allIds.length === 21 &&
      allIds.length === player.hand.length - 1
    )

    if (
      initialOpen &&
      totalScore < 101 &&
      !openingAll21AtOnce
    ) {
      addPenalty(
        player,
        101,
        '101 tutmadan açma denemesi'
      )

      return {
        ok: false,
        penalty: 101,
        message: 'İlk açılış en az 101 olmalıdır. +101 ceza.',
      }
    }

    markPickedDiscardUsed(player, usedTiles, {
      applySourcePenalty: initialOpen,
    })
    removeTilesFromHand(player, allIds)

    if (initialOpen) {
      player.opened = true
      player.openType = 'normal'
      player.openedAllAtOnceTurn = openingAll21AtOnce
        ? game.turnCounter
        : null
      player.openedAllAtOnceNoOtherOpen = Boolean(
        openingAll21AtOnce && noOtherPlayerHadOpened
      )
    }

    for (const meld of melds) {
      game.tableMelds.push(
        createTableMeld(player, meld.tiles, meld.validation)
      )
    }

    player.turnTableActions++

    return {
      ok: true,
      totalScore,
      openingAll21AtOnce,
    }
  }

  // =====================================================
  // ÇİFT AÇILIŞI
  // =====================================================

  function attemptOpenPairs(player, pairIdGroups) {
    const turnError = requirePostDrawAction(player)

    if (turnError) {
      return turnError
    }

    const acquireError = requireAcquiredTileForInitialOpening(player)
    if (acquireError) return acquireError

    if (player.openType === 'normal') {
      return {
        ok: false,
        message: 'Normal açtıktan sonra çifte dönülemez.',
      }
    }

    if (!Array.isArray(pairIdGroups) || pairIdGroups.length === 0) {
      return {
        ok: false,
        message: 'Açılacak çift yok.',
      }
    }

    const initialOpen = !player.opened
    const minimumPairCount = initialOpen ? 5 : 1

    if (pairIdGroups.length < minimumPairCount) {
      if (initialOpen) {
        addPenalty(
          player,
          101,
          '5 çift olmadan çift açma denemesi'
        )
      }

      return {
        ok: false,
        penalty: initialOpen ? 101 : 0,
        message: initialOpen
          ? 'İlk çift açılışında en az 5 çift gerekir. +101 ceza.'
          : 'En az bir çift gerekir.',
      }
    }

    const flatIds = pairIdGroups.flat().map(String)

    if (new Set(flatIds).size !== flatIds.length) {
      return {
        ok: false,
        message: 'Bir taş birden fazla çiftte kullanılamaz.',
      }
    }

    const handIds = flatIds

    if (handIds.length >= player.hand.length) {
      return {
        ok: false,
        message: 'Bütün taşları yere indiremezsin; turu bitirmek için bir taş atmalısın.',
      }
    }

    if (
      player.pickedDiscardRequiresOpening &&
      player.pickedDiscardId &&
      !handIds.includes(player.pickedDiscardId)
    ) {
      return {
        ok: false,
        message: 'Yandan aldığın taşı çift açılışında kullanmalısın veya geri koymalısın.',
      }
    }

    const pairs = []
    const usedTiles = []
    let indicatorUsedHere = false

    for (const ids of pairIdGroups) {
      const stringIds = ids.map(String)
      const pair = handTilesFromIds(player, stringIds)

      if (!pair || pair.length !== 2) {
        return {
          ok: false,
          message: 'Geçersiz çift.',
        }
      }

      const validation = validateOpeningPair(pair, player, initialOpen)

      if (!validation) {
        if (initialOpen) {
          addPenalty(
            player,
            101,
            'Geçersiz çift ile açma denemesi'
          )
        }

        return {
          ok: false,
          penalty: initialOpen ? 101 : 0,
          message: initialOpen
            ? 'Çiftlerden biri geçersiz. +101 ceza.'
            : 'Çiftlerden biri geçersiz.',
        }
      }

      if (validation.indicatorWildcard) {
        if (indicatorUsedHere) {
          return {
            ok: false,
            message: 'Gösterge-eşi taş yalnız bir çiftte kullanılabilir.',
          }
        }
        indicatorUsedHere = true
      }

      pairs.push(pair)
      usedTiles.push(...pair)
    }

    markPickedDiscardUsed(player, usedTiles, {
      applySourcePenalty: initialOpen,
      // Yandan alınan taşla ilk kez çift açılırsa taşı atan oyuncunun
      // sayı x10 kaynak cezası iki kat uygulanır (örn. 6 => 120).
      sourcePenaltyMultiplier: initialOpen ? 2 : 1,
    })
    removeTilesFromHand(player, handIds)

    if (indicatorUsedHere) {
      game.indicatorPairUsed = true
      game.indicatorPairOwnerId = player.id
    }

    if (initialOpen) {
      player.opened = true
      player.openType = 'pairs'
    }

    game.pairOpens.push({
      ownerId: player.id,
      ownerSeat: player.seat,
      pairs: pairs.map(pair => clonePlain(pair)),
    })

    player.turnTableActions++

    return {
      ok: true,
      pairCount: pairs.length,
      indicatorUsed: indicatorUsedHere,
    }
  }

  // =====================================================
  // MASADAKİ PERE TAŞ İŞLE
  // =====================================================

  function attemptLayoff(player, tileId, meldIndex, preferredSide = null) {
    const turnError = requirePostDrawAction(player)

    if (turnError) {
      return turnError
    }

    if (!canPlayerProcessTable(player)) {
      return {
        ok: false,
        message: 'Önce geçerli 101/5 çift açılışını masaya koymalısın.',
      }
    }

    if (isTileReservedInReadyOpeningDraft(player, tileId)) {
      return { ok: false, message: 'Açılış taslağındaki taşı işleme için tekrar kullanamazsın.' }
    }

    if (
      player.pickedDiscardRequiresOpening &&
      player.pickedDiscardId &&
      tileId !== player.pickedDiscardId &&
      !openingDraftUsesPickedDiscard(player)
    ) {
      return {
        ok: false,
        message: 'Yandan aldığın taşı önce masaya kullanmalısın veya geri koymalısın.',
      }
    }

    if (getAvailableHandCountAfterReadyDraft(player) <= 1) {
      return {
        ok: false,
        message: 'Son discard taşını masaya işleyemezsin; oyunu bir taş atarak bitirmelisin.',
      }
    }

    const tile = player.hand.find(item => item.id === tileId)

    if (!tile) {
      return {
        ok: false,
        message: 'Taş elde değil.',
      }
    }

    const meld = game.tableMelds[meldIndex]

    if (!meld) {
      return {
        ok: false,
        message: 'Per bulunamadı.',
      }
    }

    const preview = previewLayoff(meld, tile, preferredSide)

    if (!preview) {
      return {
        ok: false,
        message: 'Taş bu pere eklenemez.',
      }
    }

    player.turnLayoffHistory.push({
      tile: clonePlain(tile),
      meldIndex,
      previousMeld: clonePlain(meld),
      pickedDiscardState: {
        pickedDiscardId: player.pickedDiscardId,
        pickedDiscardSourceId: player.pickedDiscardSourceId,
        pickedDiscardRequiresOpening: player.pickedDiscardRequiresOpening,
      },
    })

    meld.tiles = preview.tiles
    meld.meta = preview.meta

    markPickedDiscardUsed(player, [tile])
    removeTilesFromHand(player, [tileId])
    player.turnTableActions++
    lockReadyOpeningDraft(player)

    return {
      ok: true,
    }
  }

  // =====================================================
  // GEÇERLİ AÇILIŞ / YENİ PER TASLAĞINDA KENDİ PERİNE TAŞ İŞLE
  // =====================================================
  // Taslak henüz discard ile commit edilmemişken taşlar authoritative olarak
  // oyuncunun elindedir. İlk açılışta 101/5 çift şartı; daha önce açılmış oyuncuda
  // ise legal yeni per şartı sağlanıyorsa kendi taslak perini aynı tur büyütebilir.
  function attemptLayoffOpeningDraft(player, tileId, stageId, preferredSide = null) {
    const turnError = requirePostDrawAction(player)
    if (turnError) return turnError

    if (!getOpeningDraftStatus(player).ready) {
      return {
        ok: false,
        message: player.opened
          ? 'Kendi yeni perine işlemek için önce geçerli bir per taslağı oluşturmalısın.'
          : 'Kendi açılış perine işlemek için önce geçerli 101/5 çift açılışını tamamlamalısın.',
      }
    }

    if (!tileId || !stageId) {
      return { ok: false, message: 'İşlenecek taş veya açılış peri bulunamadı.' }
    }

    if (isTileReservedInReadyOpeningDraft(player, tileId)) {
      return { ok: false, message: 'Bu taş zaten açılış taslağında kullanılıyor.' }
    }

    if (getAvailableHandCountAfterReadyDraft(player) <= 1) {
      return {
        ok: false,
        message: 'Son discard taşını masaya işleyemezsin; turu bir taş atarak bitirmelisin.',
      }
    }

    const tile = player.hand.find(item => item.id === tileId)
    if (!tile) return { ok: false, message: 'Taş elde değil.' }

    const draftIndex = (player.openingDraft || []).findIndex(
      group => String(group?.stageId || '') === String(stageId)
    )
    const draftGroup = player.openingDraft?.[draftIndex]

    if (draftIndex < 0 || !draftGroup || draftGroup.kind !== 'meld') {
      return { ok: false, message: 'Hedef kendi açılışındaki normal bir per değil.' }
    }

    const nextDraft = clonePlain(player.openingDraft)
    const nextGroup = nextDraft[draftIndex]
    const currentTiles = handTilesFromIds(player, nextGroup.tileIds)

    if (!currentTiles) {
      return { ok: false, message: 'Açılış perindeki taşlardan biri elde bulunamadı.' }
    }

    const currentValidation = validateMeld(currentTiles, game.joker)
    if (!currentValidation) {
      return { ok: false, message: 'Açılış peri artık geçerli değil.' }
    }

    const draftMeld = {
      tiles: currentTiles,
      type: nextGroup.meldType || currentValidation.type,
      meta: nextGroup.meldMeta || meldMetaFromValidation(currentValidation),
    }

    const preview = previewLayoff(draftMeld, tile, preferredSide)
    if (!preview) {
      return { ok: false, message: 'Bu taş kendi açılış perine işlenemez.' }
    }

    nextGroup.tileIds = preview.tiles.map(item => String(item.id))
    nextGroup.meldType = draftMeld.type
    nextGroup.meldMeta = preview.meta

    const nextStatus = getOpeningDraftStatus(player, nextDraft)
    if (!nextStatus.ready) {
      return { ok: false, message: 'İşlemden sonra açılış geçerliliğini kaybediyor.' }
    }

    player.openingDraft = nextDraft
    // Aynı turda işleme hakkını kullandıktan sonra bu geçerli çekirdeğin hiçbir
    // parçası geri çekilemesin. Sonraki legal tek-taş işleme ile çekirdek büyür.
    player.openingDraftLockedCore = clonePlain(nextDraft)
    player.turnTableActions++

    return {
      ok: true,
      stageId: String(stageId),
    }
  }


  // =====================================================
  // ÇİFT AÇMIŞ OYUNCUNUN ALANINA ÇİFT İŞLE
  // =====================================================
  //
  // 101'in Türkiye'de yaygın oynanan varyantında, elini açmış bir oyuncu
  // masada çift açmış biri varsa elindeki geçerli çifti o oyuncunun çift
  // alanına işleyebilir. Bu, normal "open-pairs" değildir:
  // - işleyecek oyuncu önce kendi elini açmış olmalıdır,
  // - hedef oyuncu gerçekten çiftten açmış olmalıdır,
  // - işlenen iki taş geçerli bir çift olmalıdır,
  // - tur sonunda yine elde bir discard taşı kalmalıdır.
  function attemptLayoffPair(
    player,
    pairIds,
    targetSeat
  ) {
    const turnError = requirePostDrawAction(player)

    if (turnError) {
      return turnError
    }

    if (!canPlayerProcessTable(player)) {
      return {
        ok: false,
        message: 'Çift işlemek için önce geçerli 101/5 çift açılışını masaya koymalısın.',
      }
    }

    const target = getSeatPlayer(targetSeat)

    if (
      !target ||
      !target.opened ||
      target.openType !== 'pairs'
    ) {
      return {
        ok: false,
        message: 'Bu oyuncu çiftten açmadığı için buraya çift işlenemez.',
      }
    }

    if (
      !Array.isArray(pairIds) ||
      pairIds.length !== 2 ||
      new Set(pairIds).size !== 2
    ) {
      return {
        ok: false,
        message: 'İşlemek için tam bir çift seçmelisin.',
      }
    }

    if (pairIds.some(id => isTileReservedInReadyOpeningDraft(player, id))) {
      return { ok: false, message: 'Açılış taslağındaki taşları çift işleme için tekrar kullanamazsın.' }
    }

    if (getAvailableHandCountAfterReadyDraft(player) <= pairIds.length) {
      return {
        ok: false,
        message: 'Son discard taşını bırakmadan bütün elini işleyemezsin; turu bir taş atarak bitirmelisin.',
      }
    }

    if (
      player.pickedDiscardRequiresOpening &&
      player.pickedDiscardId &&
      !pairIds.includes(player.pickedDiscardId) &&
      !openingDraftUsesPickedDiscard(player)
    ) {
      return {
        ok: false,
        message: 'Yandan aldığın taşı önce kullanmalısın veya geri koymalısın.',
      }
    }

    const pair = handTilesFromIds(player, pairIds)

    if (
      !pair ||
      pair.length !== 2 ||
      !validatePair(pair, game.joker)
    ) {
      return {
        ok: false,
        message: 'Seçilen iki taş geçerli bir çift değil.',
      }
    }

    markPickedDiscardUsed(player, pair)
    removeTilesFromHand(player, pairIds)

    // Görsel olarak çift, hedef çift açan oyuncunun alanına aittir.
    // contributedBy* yalnız izlenebilirlik içindir; el açma türünü değiştirmez.
    game.pairOpens.push({
      ownerId: target.id,
      ownerSeat: target.seat,
      pairs: [clonePlain(pair)],
      contributedById: player.id,
      contributedBySeat: player.seat,
    })

    player.turnTableActions++
    lockReadyOpeningDraft(player)

    return {
      ok: true,
      targetSeat: target.seat,
    }
  }

  // =====================================================
  // MASADAKİ GERÇEK OKEYİ DOĞAL TAŞLA DEĞİŞTİRME
  // =====================================================

  // Bir perde birden fazla gerçek okey bulunabilir. Run metadata'sında her
  // okeyin slotu kesin; dört taşlık sette de atanan renkler kesindir. Doğal
  // karşılığı verilen spesifik okeyi bulur. 3 taşlık setlerde renk yorumu
  // belirsiz kaldığı için mevcut kural gereği okey alma kapalı kalır.
  function findReplaceableJokerInMeld(meld, tile) {
    if (!meld || !tile || !ensureMeldMeta(meld)) return null

    const effective = getEffectiveTile(tile, game.joker)
    if (effective.wildcard) return null

    const jokers = meld.tiles.filter(item => isRealJoker(item, game.joker))
    if (jokers.length === 0) return null

    if (meld.type === 'group') {
      if (meld.tiles.length !== 4) return null
      if (Number(effective.number) !== Number(meld.meta?.number)) return null

      for (const jokerTile of jokers) {
        const assigned = meld.meta?.assignments?.[jokerTile.id]
        if (!assigned || effective.color !== assigned.color) continue

        const replacedTiles = meld.tiles.map(item =>
          item.id === jokerTile.id ? tile : item
        )
        const validation = validateGroup(replacedTiles, game.joker)
        if (validation) return { jokerTile, validation }
      }

      return null
    }

    if (meld.type === 'run') {
      for (const jokerTile of jokers) {
        const assigned = meld.meta?.assignments?.[jokerTile.id]
        if (
          !assigned ||
          effective.color !== assigned.color ||
          Number(effective.number) !== Number(assigned.number)
        ) {
          continue
        }

        const replacedTiles = meld.tiles.map(item =>
          item.id === jokerTile.id ? tile : item
        )
        const validation = validateRun(replacedTiles, game.joker)
        if (validation) return { jokerTile, validation }
      }
    }

    return null
  }

  function attemptReplaceJokerInMeld(player, tileId, meldIndex) {
    const turnError = requirePostDrawAction(player)
    if (turnError) return turnError

    if (!canPlayerProcessTable(player)) {
      return { ok: false, message: 'Okey değiştirmek için önce geçerli 101/5 çift açılışını masaya koymalısın.' }
    }

    if (isTileReservedInReadyOpeningDraft(player, tileId)) {
      return { ok: false, message: 'Açılış taslağındaki taşı okey değiştirmek için tekrar kullanamazsın.' }
    }

    if (player.pickedDiscardRequiresOpening && player.pickedDiscardId && tileId !== player.pickedDiscardId && !openingDraftUsesPickedDiscard(player)) {
      return { ok: false, message: 'Yandan aldığın taşı önce kullanmalısın veya geri koymalısın.' }
    }

    const tile = player.hand.find(item => item.id === tileId)
    const meld = game.tableMelds[meldIndex]

    if (!tile || !meld || !ensureMeldMeta(meld)) {
      return { ok: false, message: 'Taş veya hedef per bulunamadı.' }
    }

    const replacement = findReplaceableJokerInMeld(meld, tile)
    if (!replacement) {
      return { ok: false, message: 'Bu taş masadaki okeylerden hiçbirinin doğal karşılığı değil.' }
    }

    const { jokerTile, validation } = replacement

    markPickedDiscardUsed(player, [tile])
    removeTilesFromHand(player, [tile.id])
    player.hand.push(jokerTile)

    meld.tiles = validation.arrangedTiles
    meld.type = validation.type
    meld.meta = meldMetaFromValidation(validation)
    player.turnTableActions++
    lockReadyOpeningDraft(player)

    return {
      ok: true,
      receivedJokerId: jokerTile.id,
    }
  }

  function attemptReplaceJokerInPair(player, tileId, pairOpenIndex, pairIndex) {
    const turnError = requirePostDrawAction(player)
    if (turnError) return turnError

    if (!canPlayerProcessTable(player)) {
      return { ok: false, message: 'Okey değiştirmek için önce geçerli 101/5 çift açılışını masaya koymalısın.' }
    }

    if (isTileReservedInReadyOpeningDraft(player, tileId)) {
      return { ok: false, message: 'Açılış taslağındaki taşı okey değiştirmek için tekrar kullanamazsın.' }
    }

    if (player.pickedDiscardRequiresOpening && player.pickedDiscardId && tileId !== player.pickedDiscardId && !openingDraftUsesPickedDiscard(player)) {
      return { ok: false, message: 'Yandan aldığın taşı önce kullanmalısın veya geri koymalısın.' }
    }

    const tile = player.hand.find(item => item.id === tileId)
    const pairOpen = game.pairOpens[pairOpenIndex]
    const pair = pairOpen?.pairs?.[pairIndex]

    if (!tile || !Array.isArray(pair) || pair.length !== 2) {
      return { ok: false, message: 'Taş veya hedef çift bulunamadı.' }
    }

    if (!validatePair(pair, game.joker) && pair.some(isIndicatorTwinTile)) {
      return { ok: false, message: 'Gösterge-eşi özel çiftten gerçek okey alınamaz.' }
    }

    const jokers = pair.filter(item => isRealJoker(item, game.joker))
    if (jokers.length !== 1) {
      return { ok: false, message: 'Bu çiftte değiştirilebilir tek bir okey yok.' }
    }

    const jokerTile = jokers[0]
    const mate = pair.find(item => item.id !== jokerTile.id)
    const mateEffective = getEffectiveTile(mate, game.joker)
    const tileEffective = getEffectiveTile(tile, game.joker)

    if (
      mateEffective.wildcard ||
      tileEffective.wildcard ||
      tileEffective.color !== mateEffective.color ||
      Number(tileEffective.number) !== Number(mateEffective.number)
    ) {
      return { ok: false, message: 'Okeyi almak için çiftin doğal eşini koymalısın.' }
    }

    const nextPair = pair.map(item => item.id === jokerTile.id ? tile : item)
    if (!validatePair(nextPair, game.joker)) {
      return { ok: false, message: 'Değişimden sonra çift geçerli kalmıyor.' }
    }

    markPickedDiscardUsed(player, [tile])
    removeTilesFromHand(player, [tile.id])
    player.hand.push(jokerTile)
    pairOpen.pairs[pairIndex] = clonePlain(nextPair)
    player.turnTableActions++
    lockReadyOpeningDraft(player)

    return {
      ok: true,
      receivedJokerId: jokerTile.id,
    }
  }

  // Sadece SON işlenen taş cezasız geri alınabilir. Daha eski bir işleme
  // dokunmaya çalışmak +101 ceza getirir ve masa bozulmadan kalır.
  function attemptUndoLayoff(player, data) {
    const turnError = requirePostDrawAction(player)

    if (turnError) {
      return turnError
    }

    const history = player.turnLayoffHistory

    if (!history.length) {
      return {
        ok: false,
        message: 'Bu tur geri alınabilecek işlenmiş taş yok.',
      }
    }

    const last = history[history.length - 1]

    // Masaya işlenmiş gerçek okey geri alınamaz / başka taşla değiştirilemez.
    if (isRealJoker(last.tile, game.joker)) {
      return {
        ok: false,
        message: 'Masaya işlenmiş okey geri alınamaz.',
      }
    }

    if (
      data?.tileId &&
      data.tileId !== last.tile.id
    ) {
      addPenalty(
        player,
        101,
        'Son işlenen taş dışında işleme geri alma denemesi'
      )

      return {
        ok: false,
        penalty: 101,
        message: 'Sadece son işlediğin taşı cezasız geri alabilirsin. +101 ceza.',
      }
    }

    game.tableMelds[last.meldIndex] = clonePlain(last.previousMeld)
    player.hand.push(clonePlain(last.tile))

    player.pickedDiscardId = last.pickedDiscardState.pickedDiscardId
    player.pickedDiscardSourceId = last.pickedDiscardState.pickedDiscardSourceId
    player.pickedDiscardRequiresOpening =
      last.pickedDiscardState.pickedDiscardRequiresOpening

    history.pop()
    player.turnTableActions = Math.max(0, player.turnTableActions - 1)

    return {
      ok: true,
    }
  }

  function canReplaceJokerInMeldWithTile(meld, tile) {
    return Boolean(findReplaceableJokerInMeld(meld, tile))
  }

  function previewReplaceJokerInMeld(meld, tile) {
    const replacement = findReplaceableJokerInMeld(meld, tile)
    if (!replacement) return null

    return {
      receivedJoker: clonePlain(replacement.jokerTile),
      meld: {
        ...clonePlain(meld),
        tiles: clonePlain(replacement.validation.arrangedTiles),
        type: replacement.validation.type,
        meta: meldMetaFromValidation(replacement.validation),
      },
    }
  }

  function previewReplaceJokerInPair(pair, tile) {
    if (!Array.isArray(pair) || pair.length !== 2 || !tile) return null

    if (!validatePair(pair, game.joker) && pair.some(isIndicatorTwinTile)) {
      return null
    }

    const jokers = pair.filter(item => isRealJoker(item, game.joker))
    if (jokers.length !== 1) return null

    const jokerTile = jokers[0]
    const mate = pair.find(item => item.id !== jokerTile.id)
    const mateEffective = getEffectiveTile(mate, game.joker)
    const tileEffective = getEffectiveTile(tile, game.joker)

    if (
      !mateEffective ||
      mateEffective.wildcard ||
      tileEffective.wildcard ||
      tileEffective.color !== mateEffective.color ||
      Number(tileEffective.number) !== Number(mateEffective.number)
    ) {
      return null
    }

    const nextPair = pair.map(item => item.id === jokerTile.id ? tile : item)
    if (!validatePair(nextPair, game.joker)) return null

    return {
      receivedJoker: clonePlain(jokerTile),
      pair: clonePlain(nextPair),
    }
  }

  function canReplaceJokerInPairWithTile(pair, tile) {
    return Boolean(previewReplaceJokerInPair(pair, tile))
  }

  function canReplaceJokerInAnyPairWithTile(tile) {
    if (!tile) return false

    for (const pairOpen of game.pairOpens || []) {
      for (const pair of pairOpen?.pairs || []) {
        if (canReplaceJokerInPairWithTile(pair, tile)) return true
      }
    }

    return false
  }

  function canAddToAnyMeld(tile) {
    return Boolean(
      game.tableMelds.some(
        meld => Boolean(previewLayoff(meld, tile))
      ) ||
      game.tableMelds.some(
        meld => canReplaceJokerInMeldWithTile(meld, tile)
      ) ||
      canReplaceJokerInAnyPairWithTile(tile)
    )
  }

  // =====================================================
  // SON GÖSTERGE TAŞINI ALMA DENEMESİ
  // =====================================================

  function captureFinalIndicatorSnapshot(player) {
    return {
      player: {
        hand: clonePlain(player.hand),
        opened: player.opened,
        openType: player.openType,
        penalty: player.penalty,
        currentPenaltyEntries:
          clonePlain(player.currentPenaltyEntries || []),
        mustDiscard: player.mustDiscard,
        turnHasAcquiredTile: Boolean(player.turnHasAcquiredTile),
        pickedDiscardId: player.pickedDiscardId,
        pickedDiscardSourceId: player.pickedDiscardSourceId,
        pickedDiscardRequiresOpening: player.pickedDiscardRequiresOpening,
        turnTableActions: player.turnTableActions,
        turnLayoffHistory: clonePlain(player.turnLayoffHistory),
        openedAllAtOnceTurn: player.openedAllAtOnceTurn,
        openedAllAtOnceNoOtherOpen: player.openedAllAtOnceNoOtherOpen,
      },
      tableMelds: clonePlain(game.tableMelds),
      pairOpens: clonePlain(game.pairOpens),
      indicator: clonePlain(game.indicator),
    }
  }

  function restoreFinalIndicatorSnapshot(player) {
    const snapshot = player.finalIndicatorSnapshot

    if (!snapshot) {
      return
    }

    const saved = snapshot.player

    player.hand = clonePlain(saved.hand)
    player.opened = saved.opened
    player.openType = saved.openType
    player.penalty = saved.penalty
    player.currentPenaltyEntries =
      clonePlain(saved.currentPenaltyEntries || [])
    player.mustDiscard = saved.mustDiscard
    player.turnHasAcquiredTile = Boolean(saved.turnHasAcquiredTile)
    player.pickedDiscardId = saved.pickedDiscardId
    player.pickedDiscardSourceId = saved.pickedDiscardSourceId
    player.pickedDiscardRequiresOpening = saved.pickedDiscardRequiresOpening
    player.turnTableActions = saved.turnTableActions
    player.turnLayoffHistory = clonePlain(saved.turnLayoffHistory)
    player.openedAllAtOnceTurn = saved.openedAllAtOnceTurn
    player.openedAllAtOnceNoOtherOpen = saved.openedAllAtOnceNoOtherOpen

    game.tableMelds = clonePlain(snapshot.tableMelds)
    game.pairOpens = clonePlain(snapshot.pairOpens)
    game.indicator = clonePlain(snapshot.indicator)

    player.finalIndicatorId = null
    player.finalIndicatorSnapshot = null
  }

  // =====================================================
  // ROUND SCORE
  // =====================================================

  function calculateRoundScores(
    winner,
    finishTile,
    options = {}
  ) {
    const details = buildRoundScoreDetails(
      winner,
      finishTile,
      options
    )

    return Object.fromEntries(
      Object.entries(details).map(
        ([playerId, detail]) => [
          playerId,
          detail.total,
        ]
      )
    )
  }


  function scheduleNextRound(options = {}) {
    const expectedGame = game
    const token = ++game.transitionToken

    setTimeout(() => {
      if (
        destroyed ||
        !game ||
        game !== expectedGame ||
        game.transitionToken !== token ||
        players.size !== MAX_PLAYERS ||
        game.phase !== 'round-ended'
      ) {
        return
      }

      startRound(options)
    }, ROUND_END_HOLD_MS)
  }

  function finishCancelledPairRound() {
    game.openingCameraLockSeat = null
    game.phase = 'round-ended'
    game.roundWinner = null
    game.roundEndReason = 'all-four-opened-pairs'
    game.roundEndSummary = 'TUR İPTAL · DÖRT OYUNCU ÇİFT AÇTI'
    game.lastRoundScores = Object.fromEntries(
      [...players.values()].map(player => [player.id, 0])
    )
    game.lastRoundTeamScores = getTeamScoresFromPlayerScores(
      game.lastRoundScores
    )

    const cancelledDetails = {}

    for (const player of players.values()) {
      cancelledDetails[player.id] = {
        round: game.round,
        reason: 'all-four-opened-pairs',
        cancelled: true,
        total: 0,
        items: [
          makeScoreItem(
            'Dört oyuncu da çift açtı: tur iptal',
            0
          ),
        ],
      }
    }

    appendScoreLedger(cancelledDetails)

    // Tur iptal: toplam puana ve oynanmış tur sayısına eklenmez.
    broadcastGameState()

    scheduleNextRound({
      countRound: false,
      // İptal edilen elde de yeni dağıtım başladığında başlangıç oyuncusu
      // bir koltuk sağa kayar.
      rotateDealer: true,
    })
  }

  function buildRoundEndSummary(winner, finishTile, options = {}) {
    if (!winner) return 'BALYA BİTTİ'

    const name = String(winner.name || 'OYUNCU').trim().toLocaleUpperCase('tr-TR')
    const jokerFinish = Boolean(finishTile && isRealJoker(finishTile, game.joker))
    const pairFinish = winner.openType === 'pairs'
    const elden = Boolean(options.elden)

    if (elden && jokerFinish) return `${name} ELDEN + OKEYLE BİTTİ`
    if (elden) return `${name} ELDEN BİTTİ`
    if (pairFinish && jokerFinish) return `${name} ÇİFTTEN + OKEYLE BİTTİ`
    if (pairFinish) return `${name} ÇİFTTEN BİTTİ`
    if (jokerFinish) return `${name} OKEYLE BİTTİ`
    return `${name} BİTTİ`
  }

  function finishRound(
    winner = null,
    finishTile = null,
    options = {}
  ) {
    const {
      reason = winner ? 'player-finished' : 'stock-exhausted',
      elden = false,
    } = options

    game.openingCameraLockSeat = null
    game.phase = 'round-ended'
    game.roundWinner = winner ? winner.id : null
    game.roundEndReason = reason
    game.roundEndSummary = buildRoundEndSummary(winner, finishTile, { reason, elden })

    const scoreOptions = {
      stockExhausted: !winner,
      elden,
      reason,
    }

    const scoreDetails = buildRoundScoreDetails(
      winner,
      finishTile,
      scoreOptions
    )

    const scores = Object.fromEntries(
      Object.entries(scoreDetails).map(
        ([playerId, detail]) => [
          playerId,
          detail.total,
        ]
      )
    )

    game.lastRoundScores = scores
    game.lastRoundTeamScores = getTeamScoresFromPlayerScores(scores)
    appendScoreLedger(scoreDetails)

    for (const player of players.values()) {
      const score = scores[player.id]
      player.roundScores.push(score)
      player.totalScore += score
    }

    if (game.round >= game.maxRounds) {
      game.phase = 'match-ended'

      const teams = getPublicTeams()
      // Bundan sonra lobby seat swap veya nick değişikliği olsa bile bitmiş maçın
      // takım üyeleri/puanları değişmesin. Public game-state bu snapshot'ı kullanır.
      game.matchFinalTeams = clonePlain(teams)
      const winningTeams = selectWinningTeams(game.matchFinalTeams)
      const winningPlayerIds = winningTeams.flatMap(
        team => team.playerIds
      )

      game.matchWinnerTeam = winningTeams[0]?.id || null
      game.matchWinnerTeams = winningTeams.map(team => team.id)
      // Eski client alanlarını uyumluluk için tutuyoruz; artık kazananlar
      // bireysel sıralama değil, kazanan takım(lar)ın bütün üyeleridir.
      game.matchWinner = winningPlayerIds[0] || null
      game.matchWinners = winningPlayerIds

      // Yeni maç otomatik başlamasın; aynı kadro yeniden HAZIR vermelidir.
      // Ready bilgisi players-state üzerinden de tutulduğu için yalnız game-state
      // yayınlamak client'ta eski hazır değerlerinin kalmasına yol açabilir.
      resetHumanReadyState()
      io.emit('players-state', getPublicPlayers())
      broadcastGameState()
      return
    }

    broadcastGameState()
    scheduleNextRound({
      countRound: true,
      // Her yeni dağıtımda başlayan oyuncu bir koltuk sağa kayar. Dealer da
      // aynı yönde döndüğü için starterSeat = nextSeat(dealerSeat) ilişkisi
      // korunur; stock-exhausted dahil istisna yoktur.
      rotateDealer: true,
    })
  }

  function advanceTurn() {
    game.openingCameraLockSeat = null
    game.currentSeat = nextSeat(game.currentSeat)
    game.turnCounter++

    const next = getSeatPlayer(game.currentSeat)

    next.mustDiscard = false
    clearPickedDiscardState(next)
    resetTurnState(next)

    scheduleBotTurnIfNeeded()
  }

  // =====================================================
  // BOT V1
  // =====================================================

  function getBotRules(player = null) {
    return {
      colors: COLORS,
      getEffectiveTile: tile => getEffectiveTile(tile, game.joker),
      validateMeld: tiles => validateBotMeld(tiles, game.joker),
      validatePair: pair => (
        player && !player.opened
          ? validateOpeningPair(pair, player, true)
          : validatePair(pair, game.joker)
      ),
      previewLayoff: (meld, tile) => previewLayoff(meld, tile),
      canReplaceJokerInMeldWithTile: (meld, tile) => (
        canReplaceJokerInMeldWithTile(meld, tile)
      ),
      canReplaceJokerInPairWithTile: (pair, tile) => (
        canReplaceJokerInPairWithTile(pair, tile)
      ),
      previewReplaceJokerInMeld: (meld, tile) => (
        previewReplaceJokerInMeld(meld, tile)
      ),
      previewReplaceJokerInPair: (pair, tile) => (
        previewReplaceJokerInPair(pair, tile)
      ),
      isRealJoker: tile => isRealJoker(tile, game.joker),
      tilePenaltyValue: tile => tilePenaltyValue(tile, game.joker),
    }
  }

  function getActiveBotEngine() {
    return BOT_VERSION === 'v1' ? botV1 : botV2
  }

  function getBotKnownVisibleTiles(player) {
    const visible = []
    visible.push(...(player?.hand || []))
    if (game?.indicator) visible.push(game.indicator)
    visible.push(...(game?.discardPile || []))

    for (const meld of game?.tableMelds || []) {
      visible.push(...(meld?.tiles || []))
    }

    for (const pairOpen of game?.pairOpens || []) {
      for (const pair of pairOpen?.pairs || []) {
        visible.push(...(pair || []))
      }
    }

    const byId = new Map()
    for (const tile of visible) {
      if (tile?.id) byId.set(tile.id, tile)
    }
    return [...byId.values()]
  }

  function buildBotContext(player) {
    return {
      player,
      // BOT yalnız public bilgi + kendi elini görür; başka oyuncuların gizli
      // elleri context'e girmez. handCount yalnız masada herkesin görebildiği
      // fiziksel taş sayısıdır ve risk/tempo değerlendirmesinde kullanılabilir.
      players: [...players.values()].map(other => ({
        id: other.id,
        seat: other.seat,
        opened: Boolean(other.opened),
        openType: other.openType || null,
        isBot: Boolean(other.isBot),
        handCount: Array.isArray(other.hand) ? other.hand.length : 0,
      })),
      tableMelds: game.tableMelds,
      pairOpens: game.pairOpens,
      discardPile: game.discardPile,
      indicator: game.indicator,
      stockCount: game.stock.length,
      knownVisibleTiles: getBotKnownVisibleTiles(player),
      rules: getBotRules(player),
    }
  }

  function prepareBotOpeningDecision(player) {
    if (!player || player.opened || !player.mustDiscard) return
    if (player.botOpeningDecisionTurn === game.turnCounter) return

    const base = buildBotContext(player)
    const engine = getActiveBotEngine()
    const decision = typeof engine.evaluateOpeningPolicy === 'function'
      ? engine.evaluateOpeningPolicy(base)
      : { allowOpening: true, legalOpening: true, reason: 'v1-fallback' }

    player.botOpeningDecisionTurn = game.turnCounter
    player.botOpeningAllowedThisTurn = Boolean(decision.allowOpening)
    player.botOpeningDecisionMeta = clonePlain({
      legalOpening: Boolean(decision.legalOpening),
      allowOpening: Boolean(decision.allowOpening),
      reason: decision.reason || null,
      strongDrawChance: Number(decision.strongDrawChance) || 0,
    })
  }

  function getBotContext(player) {
    const context = buildBotContext(player)
    const engine = getActiveBotEngine()

    let allowOpening = true
    if (!player.opened) {
      if (player.botOpeningDecisionTurn !== game.turnCounter) {
        const decision = typeof engine.evaluateOpeningPolicy === 'function'
          ? engine.evaluateOpeningPolicy(context)
          : { allowOpening: true }
        allowOpening = Boolean(decision.allowOpening)
      }
      else {
        allowOpening = Boolean(player.botOpeningAllowedThisTurn)
      }
    }

    context.openingPolicy = {
      mode: BOT_VERSION === 'v2' ? 'adaptive-lookahead' : 'immediate-v1',
      allowOpening,
      waitCount: Number(player.botOpeningWaitCount) || 0,
      decision: player.botOpeningDecisionMeta || null,
    }

    return context
  }

  function botCanTakeDiscard(player) {
    if (
      player.mustDiscard ||
      game.lastDiscardOwnerSeat !== previousSeat(player.seat) ||
      game.lastDiscardOwnerId == null
    ) {
      return false
    }

    const tile = game.discardPile.at(-1)
    if (!tile || game.lastDiscardWasPlayable) return false

    return getActiveBotEngine().canUsePickup(
      getBotContext(player),
      tile
    )
  }

  function botTakeDiscard(player) {
    if (!botCanTakeDiscard(player)) {
      return {
        ok: false,
        message: 'BOT yandan taşı kullanamıyor.',
      }
    }

    const tile = game.discardPile.pop()

    io.emit('discard-taken', {
      tileId: tile.id,
      sourceSeat: game.lastDiscardOwnerSeat,
    })
    emitGameSfx('discard-take', { sourceSeat: player.seat })

    player.hand.push(tile)
    player.mustDiscard = true
    player.turnHasAcquiredTile = true
    player.pickedDiscardId = tile.id
    player.pickedDiscardSourceId = game.lastDiscardOwnerId
    // Yandan alınan taş, oyuncu daha önce açmış olsa bile bu tur masada
    // kullanılmak zorundadır. Kaynak oyuncu cezası ise yalnız ilk açılışta.
    player.pickedDiscardRequiresOpening = true

    player.turnTableActions = 0
    player.turnLayoffHistory = []

    return {
      ok: true,
      tile,
    }
  }

  function botCancelDiscardPick(player) {
    if (!player.pickedDiscardId || player.turnTableActions > 0) {
      return false
    }

    const index = player.hand.findIndex(
      tile => tile.id === player.pickedDiscardId
    )

    if (index < 0) return false

    const [tile] = player.hand.splice(index, 1)
    game.discardPile.push(tile)

    player.mustDiscard = false
    clearPickedDiscardState(player)
    resetTurnState(player)
    return true
  }

  function botDrawStock(player) {
    if (player.mustDiscard || game.stock.length === 0) {
      return {
        ok: false,
      }
    }

    const tile = game.stock.pop()

    player.hand.push(tile)
    player.mustDiscard = true
    clearPickedDiscardState(player)
    resetTurnState(player)
    player.turnHasAcquiredTile = true
    emitGameSfx('stock-draw')

    return {
      ok: true,
      tile,
    }
  }

  function getBotOpeningPreviewGroups(player, action) {
    if (!player || !action || !Array.isArray(action.groups)) return []
    if (action.type !== 'open-melds' && action.type !== 'open-pairs') return []

    const kind = action.type === 'open-pairs' ? 'pair' : 'meld'

    return action.groups.map((group, index) => ({
      stageId: `bot-preview-${game.turnCounter}-${index + 1}`,
      tileIds: [...group].map(String),
      kind,
      placement: null,
    }))
  }

  async function previewBotOpeningAction(player, action) {
    const groups = getBotOpeningPreviewGroups(player, action)
    if (groups.length === 0) return false

    if (!player.opened) {
      game.openingCameraLockSeat = player.seat
    }
    player.openingDraft = []
    broadcastGameState()
    await waitMs(BOT_OPENING_CAMERA_LEAD_MS)

    for (const group of groups) {
      if (
        game?.phase !== 'playing' ||
        game.currentSeat !== player.seat ||
        getSeatPlayer(player.seat)?.id !== player.id
      ) {
        player.openingDraft = []
        return false
      }

      player.openingDraft.push(group)
      emitGameSfx('meld-place', { sourceSeat: player.seat })
      broadcastGameState()
      await waitMs(BOT_OPENING_GROUP_DELAY_MS)
    }

    return true
  }

  function executeBotTableAction(player, action, options = {}) {
    if (!action) {
      return {
        ok: false,
        message: 'BOT aksiyonu yok.',
      }
    }

    if (action.type === 'open-melds') {
      const result = attemptOpenMelds(player, action.groups)

      if (result.ok && !options.suppressSfx) {
        emitGameSfx('meld-place', {
          sourceSeat: player.seat,
          count: Math.max(1, Array.isArray(action.groups) ? action.groups.length : 1),
        })
      }

      return result
    }

    if (action.type === 'open-pairs') {
      const result = attemptOpenPairs(player, action.groups)

      if (result.ok && !options.suppressSfx) {
        emitGameSfx('meld-place', {
          sourceSeat: player.seat,
          count: Math.max(1, Array.isArray(action.groups) ? action.groups.length : 1),
        })
      }

      if (result.ok && allPlayersOpenedPairs()) {
        finishCancelledPairRound()
        return {
          ...result,
          roundEnded: true,
          cancelled: true,
        }
      }

      return result
    }

    if (action.type === 'layoff') {
      const result = attemptLayoff(
        player,
        action.tileId,
        Number(action.meldIndex)
      )

      if (result.ok) {
        emitGameSfx('tile-layoff', { sourceSeat: player.seat })
      }

      return result
    }

    if (action.type === 'layoff-pair') {
      const result = attemptLayoffPair(
        player,
        action.tileIds,
        action.targetSeat
      )

      if (result.ok) {
        emitGameSfx('meld-place', { sourceSeat: player.seat })
      }

      return result
    }

    if (action.type === 'replace-joker-meld') {
      const result = attemptReplaceJokerInMeld(
        player,
        action.tileId,
        Number(action.meldIndex)
      )
      if (result.ok) emitGameSfx('tile-layoff', { sourceSeat: player.seat })
      return result
    }

    if (action.type === 'replace-joker-pair') {
      const result = attemptReplaceJokerInPair(
        player,
        action.tileId,
        Number(action.pairOpenIndex),
        Number(action.pairIndex)
      )
      if (result.ok) emitGameSfx('tile-layoff', { sourceSeat: player.seat })
      return result
    }

    return {
      ok: false,
      message: 'Bilinmeyen BOT aksiyonu.',
    }
  }

  function runBotTableActions(player) {
    let guard = 0

    while (
      game?.phase === 'playing' &&
      game.currentSeat === player.seat &&
      player.mustDiscard &&
      player.hand.length > 1 &&
      guard++ < 64
    ) {
      const action = getActiveBotEngine().chooseNextTableAction(
        getBotContext(player)
      )

      if (!action) break

      const beforeHandLength = player.hand.length
      const result = executeBotTableAction(player, action)

      if (!result.ok || result.roundEnded) {
        return result
      }

      const isJokerReplacement =
        action.type === 'replace-joker-meld' ||
        action.type === 'replace-joker-pair'

      if (
        player.hand.length > beforeHandLength ||
        (!isJokerReplacement && player.hand.length >= beforeHandLength)
      ) {
        return {
          ok: false,
          message: 'BOT masa aksiyonu beklenen ilerlemeyi sağlamadı.',
        }
      }
    }

    return {
      ok: true,
    }
  }

  async function runBotTableActionsAnimated(player) {
    let guard = 0

    while (
      game?.phase === 'playing' &&
      game.currentSeat === player.seat &&
      getSeatPlayer(player.seat)?.id === player.id &&
      player.mustDiscard &&
      player.hand.length > 1 &&
      guard++ < 64
    ) {
      const action = getActiveBotEngine().chooseNextTableAction(
        getBotContext(player)
      )

      if (!action) break

      const beforeHandLength = player.hand.length
      const isOpeningAction = action.type === 'open-melds' || action.type === 'open-pairs'
      const openingAcquireError = isOpeningAction && !player.opened
        ? requireAcquiredTileForInitialOpening(player)
        : null
      const shouldPreviewOpening = isOpeningAction && !openingAcquireError

      // Bot açılışını tek state değişiminde patlatma. Önce kamera kilitlensin,
      // sonra per/çiftler tek tek public taslak olarak görünsün. Authoritative
      // commit ancak bu görsel sıra bittikten sonra yapılır. Başlangıç oyuncusunun
      // 22 taşla çekmeden açması yasak olduğu için o reddedilecek planı önizleme.
      if (shouldPreviewOpening) {
        const previewed = await previewBotOpeningAction(player, action)
        if (!previewed) {
          player.openingDraft = []
          return { ok: false, message: 'BOT açılış önizlemesi kesildi.' }
        }
      }

      player.openingDraft = []
      const result = executeBotTableAction(player, action, {
        suppressSfx: shouldPreviewOpening,
      })

      if (!result.ok || result.roundEnded) {
        player.openingDraft = []
        broadcastGameState()
        return result
      }

      const isJokerReplacement =
        action.type === 'replace-joker-meld' ||
        action.type === 'replace-joker-pair'

      if (
        player.hand.length > beforeHandLength ||
        (!isJokerReplacement && player.hand.length >= beforeHandLength)
      ) {
        return {
          ok: false,
          message: 'BOT masa aksiyonu beklenen ilerlemeyi sağlamadı.',
        }
      }

      broadcastGameState()

      // Açılış grupları zaten tek tek ~1 sn arayla gösterildi. Sonraki layoff
      // veya yeni masa hamlesine geçmeden ayrıca kısa bir düşünme arası bırak.
      await waitMs(BOT_TABLE_ACTION_DELAY_MS)
    }

    return {
      ok: true,
    }
  }

  function botDiscard(player, tileId) {
    if (!player.mustDiscard) {
      return {
        ok: false,
        message: 'BOT önce taş çekmeli.',
      }
    }

    if (player.pickedDiscardRequiresOpening && player.pickedDiscardId) {
      return {
        ok: false,
        message: 'BOT yandan aldığı taşı kullanmadı.',
      }
    }

    const index = player.hand.findIndex(
      tile => tile.id === tileId
    )

    if (index < 0) {
      return {
        ok: false,
        message: 'BOT discard taşı elde değil.',
      }
    }

    const tile = player.hand[index]
    const willFinish = player.hand.length === 1

    if (player.finalIndicatorId) {
      const indicatorStillInHand = player.hand.some(
        item => item.id === player.finalIndicatorId
      )

      if (!willFinish || indicatorStillInHand) {
        restoreFinalIndicatorSnapshot(player)
        finishRound(null, null, {
          reason: 'stock-exhausted',
        })

        return {
          ok: false,
          roundEnded: true,
          message: 'BOT göstergeyle bitme denemesini tamamlayamadı.',
        }
      }
    }

    const isDiscardingRealJoker = isRealJoker(tile, game.joker)
    const discardedRealJoker = !willFinish && isDiscardingRealJoker
    const discardWasPlayable = !willFinish && canAddToAnyMeld(tile)

    // Gerçek okey normal discard edildiğinde tek ceza uygulanır. Okey aynı
    // zamanda açık perlere işlenebilir görünse bile +101'i ikinci kez
    // "işlek taş" cezası olarak yazmayız.
    if (discardWasPlayable && !discardedRealJoker) {
      addPenalty(
        player,
        101,
        `İşlek ${describeTileForScore(tile)} attı`
      )
    }

    if (discardedRealJoker) {
      addPenalty(
        player,
        101,
        'Okey attı'
      )
    }

    player.hand.splice(index, 1)
    game.discardPile.push(tile)
    emitGameSfx(isDiscardingRealJoker ? 'okey-discard' : 'discard', {
      sourceSeat: player.seat,
    })
    game.lastDiscardOwnerId = player.id
    game.lastDiscardOwnerSeat = player.seat
    game.lastDiscardWasPlayable = Boolean(discardWasPlayable)

    player.mustDiscard = false
    clearPickedDiscardState(player)

    if (player.hand.length === 0) {
      const elden = Boolean(
        player.openedAllAtOnceTurn === game.turnCounter &&
        player.openedAllAtOnceNoOtherOpen
      )

      player.finalIndicatorId = null
      player.finalIndicatorSnapshot = null

      finishRound(player, tile, {
        reason: elden ? 'elden-finished' : 'player-finished',
        elden,
      })

      return {
        ok: true,
        finished: true,
        elden,
      }
    }

    player.finalIndicatorId = null
    player.finalIndicatorSnapshot = null

    // Son stok taşını çeken oyuncunun discardı bu elin son hamlesidir.
    // Stock 0 iken sırayı bir sonraki oyuncuya geçirmiyoruz; o oyuncunun
    // artık ne yandan discard alma ne de başka bir hamle yapma hakkı vardır.
    if (game.stock.length === 0) {
      finishRound(null, null, {
        reason: 'stock-exhausted',
      })

      return {
        ok: true,
        roundEnded: true,
        stockExhausted: true,
      }
    }

    advanceTurn()

    return {
      ok: true,
    }
  }

  async function runBotTurn(player) {
    if (
      !player?.isBot ||
      !game ||
      game.phase !== 'playing' ||
      game.currentSeat !== player.seat
    ) {
      return
    }


    // Botun çektiği/alacağı taşı ve ardından ne yapacağını görebilmek için
    // her turu küçük, deterministik beklemelere böl. Discard SONRASI bekleme yok;
    // taş atıldığı anda currentSeat normal şekilde bir sonraki oyuncuya geçer.
    if (!player.mustDiscard) {
      if (botCanTakeDiscard(player)) {
        botTakeDiscard(player)
      }
      else if (game.stock.length > 0) {
        botDrawStock(player)
      }
      else {
        finishRound(null, null, {
          reason: 'stock-exhausted',
        })
        return
      }

      broadcastGameState()
      await waitMs(BOT_DECISION_DELAY_MS)
    }

    prepareBotOpeningDecision(player)

    const tableResult = await runBotTableActionsAnimated(player)
    if (tableResult?.roundEnded || game.phase !== 'playing') {
      return
    }

    // Planner bir yandan taşı kullanılabilir sanıp authoritative validation
    // reddederse, bot başka bir masaya hamle yapmadan taşı geri bırakır ve
    // normal stock yoluna döner. Böylece zorunlu kullanım kuralı delinmez.
    if (player.pickedDiscardRequiresOpening && player.pickedDiscardId) {
      const cancelled = botCancelDiscardPick(player)

      if (!cancelled) {
        console.warn(
          `[BOT] ${player.name}: yandan alınan taş güvenli şekilde geri konamadı.`
        )
        return
      }

      if (game.stock.length > 0) {
        botDrawStock(player)
        broadcastGameState()
        await waitMs(BOT_DECISION_DELAY_MS)
        await runBotTableActionsAnimated(player)
      }
      else {
        finishRound(null, null, {
          reason: 'stock-exhausted',
        })
        return
      }
    }

    if (
      game.phase !== 'playing' ||
      game.currentSeat !== player.seat ||
      !player.mustDiscard
    ) {
      return
    }

    if (
      !player.opened &&
      player.botOpeningDecisionTurn === game.turnCounter &&
      player.botOpeningDecisionMeta?.legalOpening &&
      !player.botOpeningAllowedThisTurn
    ) {
      player.botOpeningWaitCount = Math.min(
        2,
        (Number(player.botOpeningWaitCount) || 0) + 1
      )
    }

    await waitMs(BOT_BEFORE_DISCARD_DELAY_MS)

    if (
      game.phase !== 'playing' ||
      game.currentSeat !== player.seat ||
      !player.mustDiscard
    ) {
      return
    }

    const discard = getActiveBotEngine().chooseDiscard(
      getBotContext(player)
    )

    if (!discard) {
      console.warn(`[BOT] ${player.name}: discard seçilemedi.`)
      return
    }

    const result = botDiscard(player, discard.id)

    if (!result.ok && !result.roundEnded) {
      console.warn(
        `[BOT] ${player.name}: discard reddedildi: ${result.message || 'bilinmeyen hata'}`
      )
    }

    // botDiscard başarılı normal turda advanceTurn() çağırmıştır. Public state'i
    // hemen yayınla: "bot attı ama sıra hâlâ botta" görüntüsü artık oluşmaz.
    if (game) {
      broadcastGameState()
    }
  }

  function scheduleBotTurnIfNeeded() {
    if (!game || game.phase !== 'playing') {
      return
    }

    const player = getSeatPlayer(game.currentSeat)
    if (!player?.isBot) {
      return
    }

    const expectedGame = game
    const expectedSeat = game.currentSeat
    const expectedTurn = game.turnCounter

    setTimeout(() => {
      if (
        destroyed ||
        !game ||
        game !== expectedGame ||
        game.phase !== 'playing' ||
        game.currentSeat !== expectedSeat ||
        game.turnCounter !== expectedTurn
      ) {
        return
      }

      void runBotTurn(player).catch(error => {
        console.error('[BOT] Tur hatası:', error)
      })
    }, BOT_TURN_DELAY_MS)
  }


  function attachSocket(socket) {
    if (destroyed) {
      socket.emit('table-unavailable', { message: 'Masa artık mevcut değil.' })
      return false
    }

      const rawName = socket.handshake.auth?.name
      const name = sanitizePlayerName(rawName) || 'Oyuncu'

      const seat = getFreeSeat()

      if (!seat) {
        socket.emit('table-full', {
          message: 'Masa dolu.',
        })

        setTimeout(() => socket.disconnect(true), 400)
        return
      }

      const player = createPlayerState(
        socket.id,
        name,
        seat,
        false
      )

      players.set(socket.id, player)
      ensureConfiguredBots()

      // Lobby kadrosu değiştiğinde eski hazır onayları yeni kişiye otomatik
      // taşınmasın. Her gerçek oyuncu güncel kadroyu gördükten sonra yeniden HAZIR verir.
      if (!game || game.phase === 'waiting' || game.phase === 'match-ended') {
        broadcastLobbyReadyReset('player-joined')
      }

      socket.emit('you-joined', { ...player, tableId: String(tableId) })
      socket.emit('kick-vote-state', getPublicKickVoteState())
      io.emit('players-state', getPublicPlayers())

      if (players.size === MAX_PLAYERS) {
        // Masa dolu olsa bile hazirlik eksikse waiting snapshot'ini yeni
        // oyuncu kadrosuyla herkese yenile. Baslangic yalniz tum insanlar
        // hazirsa startOrResumeWhenTableIsFull() icinden gerceklesir.
        if (!startOrResumeWhenTableIsFull()) {
          broadcastGameState()
        }
      }

      // ===================================================
      // LOBI: HAZIR / NICK
      // ===================================================

      socket.on('return-to-lobby', callback => {
        const current = players.get(socket.id)

        if (!current || current.isBot) {
          callback?.({ ok: false, message: 'Lobiye dönülemedi.' })
          return
        }

        // Başka bir oyuncu DEVAM ET'e milisaniyeler önce bastıysa bu istek
        // stale bir hata gibi görünmesin. Fresh round-0 waiting state zaten
        // hedeflediğimiz lobby olduğundan event idempotent biçimde başarılıdır.
        if (game?.phase === 'waiting' && game.round === 0 && !game.rosterResumeOptions) {
          callback?.({
            ok: true,
            alreadyReturned: true,
            message: 'Lobiye dönüldü. Yeni maç için yeniden hazır verin.',
          })
          return
        }

        if (!game || game.phase !== 'match-ended') {
          callback?.({ ok: false, message: 'Maç sonucu artık aktif değil.' })
          return
        }

        const returned = returnCompletedMatchToLobby()
        callback?.({
          ok: returned,
          message: returned
            ? 'Lobiye dönüldü. Yeni maç için yeniden hazır verin.'
            : 'Lobiye dönülemedi.',
        })
      })

      socket.on('set-ready', (value, callback) => {
        const current = players.get(socket.id)

        if (!current || current.isBot) {
          callback?.({ ok: false, message: 'Hazirlik yalniz gercek oyuncular icindir.' })
          return
        }

        if (!isLobbyEditable()) {
          callback?.({ ok: false, message: 'Mac basladiktan sonra hazirlik degistirilemez.' })
          return
        }

        // Kadro degisimiyle ayni anda gelen gecikmis bir HAZIR tiklamasi eski
        // onayi geri getirmesin. Hazirlik ancak masa yeniden 4 kisi oldugunda verilir.
        if (players.size !== MAX_PLAYERS) {
          current.ready = false
          io.emit('players-state', getPublicPlayers())
          callback?.({ ok: false, ready: false, message: 'Hazir vermek icin masanin 4 oyuncu olmasi gerekiyor.' })
          return
        }

        current.ready = Boolean(value)
        if (current.ready) {
          cancelOutgoingSeatSwapRequestsForPlayer(current.id, 'requester-ready')
        }
        io.emit('players-state', getPublicPlayers())
        broadcastGameState()

        const started = startOrResumeWhenTableIsFull()
        callback?.({ ok: true, ready: current.ready, started })
      })

      socket.on('rename-player', (value, callback) => {
        const current = players.get(socket.id)

        if (!current || current.isBot) {
          callback?.({ ok: false, message: 'Nick degistirilemedi.' })
          return
        }

        if (!isLobbyEditable()) {
          callback?.({ ok: false, message: 'Mac basladiktan sonra nick degistirilemez.' })
          return
        }

        if (current.ready) {
          callback?.({ ok: false, message: 'Nick degistirmek icin once hazirligini iptal et.' })
          return
        }

        const nextName = sanitizePlayerName(value)
        if (!nextName) {
          callback?.({ ok: false, message: 'Nick bos olamaz.' })
          return
        }

        current.name = nextName
        io.emit('players-state', getPublicPlayers())
        broadcastGameState()
        callback?.({ ok: true, name: current.name })
      })

      // ===================================================
      // LOBI: KOLTUK YER DEĞİŞTİRME
      // ===================================================

      socket.on('seat-swap-request', (targetId, callback) => {
        const source = players.get(socket.id)
        const target = players.get(String(targetId || ''))

        if (!source || source.isBot) {
          callback?.({ ok: false, message: 'Yer değiştirme isteği gönderilemedi.' })
          return
        }

        if (!isLobbyEditable()) {
          callback?.({ ok: false, message: 'Oyun başladıktan sonra koltuk değiştirilemez.' })
          return
        }

        if (source.ready) {
          callback?.({ ok: false, message: 'Yer değiştirmek için önce hazır olmamalısın.' })
          return
        }

        if (!target || target.id === source.id) {
          callback?.({ ok: false, message: 'Geçerli bir oyuncu seç.' })
          return
        }

        if (getPendingSeatSwapForPlayer(source.id)) {
          callback?.({ ok: false, message: 'Önce mevcut yer değiştirme isteğinin sonuçlanmasını bekle.' })
          return
        }

        if (getPendingSeatSwapForPlayer(target.id)) {
          callback?.({ ok: false, message: `${target.name} şu anda başka bir yer değiştirme isteğiyle meşgul.` })
          return
        }

        if (target.isBot) {
          const result = performSeatSwap(source, target)
          callback?.({
            ...result,
            autoAccepted: Boolean(result.ok),
          })
          return
        }

        const request = createSeatSwapRequest(source, target)

        io.to(target.id).emit('seat-swap-offer', {
          requestId: request.id,
          sourcePlayerId: source.id,
          sourceName: source.name,
          sourceSeat: source.seat,
          targetSeat: target.seat,
          expiresAt: request.expiresAt,
        })

        callback?.({
          ok: true,
          pending: true,
          requestId: request.id,
          targetName: target.name,
          expiresAt: request.expiresAt,
        })
      })

      socket.on('seat-swap-response', (value, callback) => {
        const target = players.get(socket.id)
        const requestId = String(value?.requestId || '')
        const accept = Boolean(value?.accept)
        const request = pendingSeatSwapRequests.get(requestId)

        if (!target || target.isBot || !request || request.targetId !== target.id) {
          callback?.({ ok: false, message: 'Yer değiştirme isteği artık geçerli değil.' })
          return
        }

        if (Date.now() > request.expiresAt) {
          cancelSeatSwapRequest(request.id, 'expired', true)
          callback?.({ ok: false, message: 'Yer değiştirme isteğinin süresi doldu.' })
          return
        }

        if (!accept) {
          cancelSeatSwapRequest(request.id, 'declined', true)
          callback?.({ ok: true, accepted: false })
          return
        }

        const source = players.get(request.sourceId)
        if (!source || source.isBot || source.ready || !isLobbyEditable()) {
          cancelSeatSwapRequest(request.id, 'invalidated', true)
          callback?.({ ok: false, message: 'Yer değiştirme isteği artık geçerli değil.' })
          return
        }

        // Request'i önce kapat; swap yayını sırasında stale yanıtların ikinci kez
        // aynı koltukları takas etmesine izin verme.
        cancelSeatSwapRequest(request.id, 'accepted', false)
        const result = performSeatSwap(source, target)

        if (!result.ok) {
          emitSeatSwapCancelled(request, 'invalidated')
          callback?.(result)
          return
        }

        callback?.({ ok: true, accepted: true })
      })

      // ===================================================
      // CHAT / EMOJI / DURTME
      // ===================================================

      socket.on('chat-message', (value, callback) => {
        const current = players.get(socket.id)
        if (!current || current.isBot) {
          callback?.({ ok: false, message: 'Mesaj gönderilemedi.' })
          return
        }

        const text = sanitizeChatMessage(value)
        if (!text) {
          callback?.({ ok: false, message: 'Mesaj boş olamaz.' })
          return
        }

        if (!passesSocialRateLimit(lastChatAtByPlayerId, current.id, CHAT_RATE_LIMIT_MS)) {
          callback?.({ ok: false, message: 'Çok hızlı mesaj gönderiyorsun.' })
          return
        }

        io.emit('chat-message', {
          playerId: current.id,
          name: current.name,
          seat: current.seat,
          text,
          sentAt: Date.now(),
        })

        callback?.({ ok: true })
      })

      socket.on('player-emoji', (value, callback) => {
        const current = players.get(socket.id)
        const emoji = String(value || '').trim()

        if (!current || current.isBot || !SOCIAL_EMOJIS.has(emoji)) {
          callback?.({ ok: false, message: 'Emoji gönderilemedi.' })
          return
        }

        if (!passesSocialRateLimit(lastEmojiAtByPlayerId, current.id, EMOJI_RATE_LIMIT_MS)) {
          callback?.({ ok: false, message: 'Biraz bekleyip tekrar emoji gönder.' })
          return
        }

        io.emit('player-emoji', {
          playerId: current.id,
          seat: current.seat,
          emoji,
          durationMs: 2600,
        })

        callback?.({ ok: true })
      })

      socket.on('poke-current-player', callback => {
        const source = players.get(socket.id)
        if (!source || source.isBot || !game || game.phase !== 'playing') {
          callback?.({ ok: false, message: 'Şu anda dürtülecek oyuncu yok.' })
          return
        }

        const target = getSeatPlayer(game.currentSeat)
        if (!target || target.isBot || target.id === source.id) {
          callback?.({ ok: false, message: 'Yalnız sırası olan başka bir gerçek oyuncuyu dürtebilirsin.' })
          return
        }

        const now = Date.now()
        const previous = Number(lastPokeAtByTargetId.get(target.id)) || 0
        if (now - previous < POKE_COOLDOWN_MS) {
          const waitSeconds = Math.max(1, Math.ceil((POKE_COOLDOWN_MS - (now - previous)) / 1000))
          callback?.({ ok: false, message: `${target.name} için ${waitSeconds} sn bekle.` })
          return
        }

        lastPokeAtByTargetId.set(target.id, now)

        io.emit('player-poked', {
          sourcePlayerId: source.id,
          sourceName: source.name,
          sourceSeat: source.seat,
          targetPlayerId: target.id,
          targetName: target.name,
          targetSeat: target.seat,
          sentAt: now,
        })

        callback?.({ ok: true, targetName: target.name })
      })

      // ===================================================
      // CAY ICME / YENI CAY
      // ===================================================

      socket.on('drink-tea', callback => {
        const current = players.get(socket.id)

        if (!current || current.isBot) {
          callback?.({ ok: false, message: 'Cay bulunamadi.' })
          return
        }

        if (!game || game.phase !== 'playing') {
          callback?.({ ok: false, message: 'Oyun baslamadan cay icilemez.' })
          return
        }

        const now = Date.now()
        if (Number(current.teaBusyUntil) > now) {
          callback?.({ ok: false, message: 'Bardak su anda hareket ediyor.' })
          return
        }

        const beforeLevel = getPublicTeaLevel(current)

        if (beforeLevel <= 0) {
          current.teaLevel = 1
          current.teaBusyUntil = now + TEA_REFILL_ACTION_MS

          io.emit('tea-action', {
            playerId: current.id,
            sourceSeat: current.seat,
            type: 'refill',
            fromLevel: 0,
            toLevel: 1,
            durationMs: TEA_REFILL_ACTION_MS,
          })

          emitGameSfx('tea-refill', { sourceSeat: current.seat })
          callback?.({ ok: true, type: 'refill', teaLevel: 1 })
          return
        }

        const requestedSipFraction = getRandomTeaSipFraction()
        const actualSipFraction = Math.min(beforeLevel, requestedSipFraction)
        current.teaLevel = Math.max(0, beforeLevel - actualSipFraction)
        current.teaBusyUntil = now + TEA_DRINK_ACTION_MS
        const afterLevel = getPublicTeaLevel(current)

        io.emit('tea-action', {
          playerId: current.id,
          sourceSeat: current.seat,
          type: 'drink',
          fromLevel: beforeLevel,
          toLevel: afterLevel,
          durationMs: TEA_DRINK_ACTION_MS,
        })

        emitGameSfx('tea-sip', { sourceSeat: current.seat })
        callback?.({
          ok: true,
          type: 'drink',
          teaLevel: afterLevel,
          sipFraction: actualSipFraction,
        })
      })

      // ===================================================
      // MASADAN BOT EKLE / ÇIKAR
      // ===================================================

      socket.on('add-bot', callback => {
        if (players.size >= MAX_PLAYERS) {
          callback?.({ ok: false, message: 'Masada boş koltuk yok.' })
          return
        }

        const bot = addBotPlayer()
        if (!bot) {
          callback?.({ ok: false, message: 'Bot için boş koltuk bulunamadı.' })
          return
        }

        if (isLobbyEditable()) {
          broadcastLobbyReadyReset('bot-added')
        }
        io.emit('players-state', getPublicPlayers())

        if (players.size === MAX_PLAYERS) {
          if (!startOrResumeWhenTableIsFull()) {
            broadcastGameState()
          }
        }
        else {
          broadcastGameState()
        }

        callback?.({
          ok: true,
          bot: { id: bot.id, name: bot.name, seat: bot.seat },
          players: getPublicPlayers(),
        })
      })

      socket.on('remove-bot', callback => {
        const bots = [...players.values()]
          .filter(player => player.isBot)
          .sort((a, b) => b.name.localeCompare(a.name, undefined, { numeric: true }))

        const bot = bots[0]
        if (!bot) {
          callback?.({ ok: false, message: 'Masada çıkarılacak bot yok.' })
          return
        }

        // Aktif/bitmiş elde oyuncu sayısını 3'e düşürmek turn akışını kırar.
        // Botu hemen kaldır ama eli güvenli biçimde waiting'e al; boş koltuk tekrar
        // dolduğunda skorları koruyarak uygun round yeniden dağıtılır.
        pauseForRosterChange()
        players.delete(bot.id)
        broadcastLobbyReadyReset('bot-removed')

        io.emit('players-state', getPublicPlayers())
        broadcastGameState()

        callback?.({
          ok: true,
          removedId: bot.id,
          paused: Boolean(game?.phase === 'waiting'),
          players: getPublicPlayers(),
        })
      })

      // ===================================================
      // İNSAN OYUNCU KICK OYLAMASI
      // ===================================================

      socket.on('start-kick-vote', (targetId, callback) => {
        const requester = players.get(socket.id)
        const result = startKickVote(requester, String(targetId || ''))
        callback?.(result)
      })

      socket.on('kick-vote', (data, callback) => {
        const voter = players.get(socket.id)
        const result = castKickVote(voter, Boolean(data?.yes))
        callback?.(result)
      })

      // ===================================================
      // CANLI AÇILIŞ TASLAĞI
      // ===================================================

      socket.on('opening-draft', (groups, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({ ok: false, message: 'Sıra sende değil.' })
          return
        }

        const beforeStageIds = new Set(
          (current.openingDraft || []).map(group => String(group.stageId || ''))
        )

        const result = setOpeningDraft(current, groups)

        if (result.ok) {
          const addedGroupCount = (current.openingDraft || []).filter(
            group => !beforeStageIds.has(String(group.stageId || ''))
          ).length

          if (addedGroupCount > 0) {
            emitGameSfx('meld-place', { sourceSeat: current.seat, count: addedGroupCount })
          }
        }

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // LOOK
      // ===================================================

      socket.on('player-look', data => {
        const current = players.get(socket.id)

        if (!current) {
          return
        }

        current.lookX = Math.max(
          -1,
          Math.min(1, Number(data?.x) || 0)
        )

        current.lookY = Math.max(
          -1,
          Math.min(1, Number(data?.y) || 0)
        )

        socket.to(roomName).emit('player-look', {
          id: socket.id,
          x: current.lookX,
          y: current.lookY,
        })
      })

      // ===================================================
      // DESTEDEN ÇEK
      // ===================================================

      socket.on('draw-stock', callback => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        if (current.mustDiscard) {
          callback?.({
            ok: false,
            message: 'Önce taş atmalısın.',
          })
          return
        }

        // Deste bittiyse önceki oyuncunun attığı son taşı alma hakkı vardır.
        // Oyuncu ortadan çekmeyi deneyerek bu hakkı kullanmamayı seçmiş olur.
        if (game.stock.length === 0) {
          finishRound(null, null, {
            reason: 'stock-exhausted',
          })

          callback?.({
            ok: false,
            roundEnded: true,
            message:
              'Ortada çekilecek taş kalmadı. El, elde kalan taşlara göre puanlandı.',
          })
          return
        }

        const tile = game.stock.pop()

        current.hand.push(tile)
        current.mustDiscard = true
        clearPickedDiscardState(current)
        resetTurnState(current)
        current.turnHasAcquiredTile = true
        emitGameSfx('stock-draw')

        broadcastGameState()

        callback?.({
          ok: true,
          tile,
        })
      })

      // ===================================================
      // DESTE BİTİNCE GÖSTERGEYİ ALARAK BİTME DENEMESİ
      // ===================================================

      socket.on('take-indicator', callback => {
        callback?.({
          ok: false,
          message: 'Ortadaki gösterge sabittir ve hiçbir şekilde alınamaz.',
        })
      })

      // ===================================================
      // YANDAN TAŞ AL
      // ===================================================

      socket.on('take-discard', callback => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        if (current.mustDiscard) {
          callback?.({
            ok: false,
            message: 'Önce taş atmalısın.',
          })
          return
        }

        const expectedSourceSeat = previousSeat(current.seat)

        if (
          game.lastDiscardOwnerSeat !== expectedSourceSeat ||
          game.lastDiscardOwnerId == null
        ) {
          callback?.({
            ok: false,
            message: 'Yalnızca hemen önceki oyuncunun son attığı taşı alabilirsin.',
          })
          return
        }

        const topDiscard = game.discardPile.at(-1)

        if (!topDiscard) {
          callback?.({
            ok: false,
            message: 'Alınacak taş yok.',
          })
          return
        }

        if (game.lastDiscardWasPlayable) {
          callback?.({
            ok: false,
            message: 'İşlek atılan taş yandan alınamaz.',
          })
          return
        }

        const tile = game.discardPile.pop()

        // Bütün clientlar fiziksel atık geçmişini yerelde tuttuğu için yalnız
        // alan oyuncunun ACK'ine güvenemeyiz. Taş pop edildiği anda herkese id'yi
        // bildir; böylece diğer oyuncuların kulelerinde de eski görsel kalmaz.
        io.emit('discard-taken', {
          tileId: tile.id,
          sourceSeat: game.lastDiscardOwnerSeat,
        })
        emitGameSfx('discard-take', { sourceSeat: current.seat })

        current.hand.push(tile)
        current.mustDiscard = true
        current.turnHasAcquiredTile = true
        current.pickedDiscardId = tile.id
        current.pickedDiscardSourceId = game.lastDiscardOwnerId
        // Yandan alınan taş her durumda bu tur legal bir masa hamlesinde
        // kullanılmalıdır. Daha önce açmış olmak yalnız kaynak x10 cezasını kaldırır.
        current.pickedDiscardRequiresOpening = true

        // Zorunlu kullanım açılmış/açılmamış herkeste aynıdır. Kaynak oyuncuya
        // sayı x10 ceza yalnız bu taşla İLK açılış yapılırsa uygulanır; daha önce
        // açılmış oyuncunun sonraki yandan alışlarında kaynak cezası yoktur.
        current.turnTableActions = 0
        current.turnLayoffHistory = []

        broadcastGameState()

        callback?.({
          ok: true,
          tile,
        })
      })

      // ===================================================
      // YANDAN ALDIĞINI GERİ KOY
      // ===================================================

      socket.on('cancel-discard-pick', callback => {
        const current = getCurrentPlayer(socket)

        if (!current || !current.pickedDiscardId) {
          callback?.({
            ok: false,
            message: 'Geri bırakılacak yandan alınmış taş yok.',
          })
          return
        }

        // Yandan taşı aldıktan sonra masada başka bir işlem yaptıysa artık
        // tüm turu geri alamayacağı için bu hak kapanır.
        if (current.turnTableActions > 0) {
          callback?.({
            ok: false,
            message: 'Masada işlem yaptıktan sonra yandan alınan taşı geri koyamazsın.',
          })
          return
        }

        const index = current.hand.findIndex(
          tile => tile.id === current.pickedDiscardId
        )

        if (index < 0) {
          callback?.({
            ok: false,
            message: 'Taş artık elde değil.',
          })
          return
        }

        // Geri bırakılan taş taslak açılışta görünüyorsa taslağın tamamını da
        // iptal et; eksik public grup bırakmayalım.
        clearOpeningDraft(current)

        const [tile] = current.hand.splice(index, 1)
        game.discardPile.push(tile)

        current.mustDiscard = false
        clearPickedDiscardState(current)
        resetTurnState(current)

        broadcastGameState()

        callback?.({
          ok: true,
        })
      })

      // ===================================================
      // NORMAL AÇ
      // ===================================================

      socket.on('open-melds', (meldIdGroups, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        const result = attemptOpenMelds(current, meldIdGroups)

        if (result.ok) {
          emitGameSfx('meld-place', {
            sourceSeat: current.seat,
            count: Math.max(1, Array.isArray(meldIdGroups) ? meldIdGroups.length : 1),
          })
        }

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // ÇİFT AÇ
      // ===================================================

      socket.on('open-pairs', (pairIdGroups, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        const result = attemptOpenPairs(current, pairIdGroups)

        if (result.ok) {
          emitGameSfx('meld-place', {
            sourceSeat: current.seat,
            count: Math.max(1, Array.isArray(pairIdGroups) ? pairIdGroups.length : 1),
          })
        }

        if (result.ok && allPlayersOpenedPairs()) {
          finishCancelledPairRound()

          callback?.({
            ...result,
            roundEnded: true,
            cancelled: true,
            message: 'Dört oyuncu da çift açtı. Tur iptal edildi; kimse puan almadı.',
          })
          return
        }

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // PERE İŞLE
      // ===================================================

      socket.on('layoff', (data, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        const result = attemptLayoff(
          current,
          data?.tileId,
          Number(data?.meldIndex),
          data?.side
        )

        if (result.ok) {
          emitGameSfx('tile-layoff', { sourceSeat: current.seat })
        }

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // GEÇERLİ İLK AÇILIŞ TASLAĞINDA KENDİ PERİNE İŞLE
      // ===================================================

      socket.on('layoff-opening-draft', (data, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({ ok: false, message: 'Sıra sende değil.' })
          return
        }

        const result = attemptLayoffOpeningDraft(
          current,
          data?.tileId,
          data?.stageId,
          data?.side
        )

        if (result.ok) {
          emitGameSfx('tile-layoff', { sourceSeat: current.seat })
        }

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // ÇİFT AÇAN OYUNCUYA ÇİFT İŞLE
      // ===================================================

      socket.on('layoff-pair', (data, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        const result = attemptLayoffPair(
          current,
          data?.tileIds,
          data?.targetSeat
        )

        if (result.ok) {
          emitGameSfx('meld-place', { sourceSeat: current.seat })
        }

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // MASADAKİ OKEYİ DOĞAL TAŞLA DEĞİŞTİR
      // ===================================================

      socket.on('replace-joker', (data, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({ ok: false, message: 'Sıra sende değil.' })
          return
        }

        const result = attemptReplaceJokerInMeld(
          current,
          data?.tileId,
          Number(data?.meldIndex)
        )

        if (result.ok) {
          emitGameSfx('tile-layoff', { sourceSeat: current.seat })
        }

        broadcastGameState()
        callback?.(result)
      })

      socket.on('replace-joker-pair', (data, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({ ok: false, message: 'Sıra sende değil.' })
          return
        }

        const result = attemptReplaceJokerInPair(
          current,
          data?.tileId,
          Number(data?.pairOpenIndex),
          Number(data?.pairIndex)
        )

        if (result.ok) {
          emitGameSfx('tile-layoff', { sourceSeat: current.seat })
        }

        broadcastGameState()
        callback?.(result)
      })

      // Gelecekte client tarafında geri-al UI'si kullanılırsa kural hazır.
      socket.on('undo-layoff', (data, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        const result = attemptUndoLayoff(current, data)

        broadcastGameState()
        callback?.(result)
      })

      // ===================================================
      // TAŞ AT / BİTİR
      // ===================================================

      socket.on('discard', (tileId, callback) => {
        const current = getCurrentPlayer(socket)

        if (!current) {
          callback?.({
            ok: false,
            message: 'Sıra sende değil.',
          })
          return
        }

        if (!current.mustDiscard) {
          callback?.({
            ok: false,
            message: 'Önce taş çekmelisin.',
          })
          return
        }

        // AÇ/GERİ butonu yok: masaya bırakılan taslak gruplar ancak discard
        // denendiğinde authoritative olarak commit edilir. Geçersiz/eksik ilk
        // açılış +101 yer ve taşlar elde kalır; discard normal şekilde devam eder.
        const draftResult = commitOpeningDraft(current)

        if (draftResult?.committed && allPlayersOpenedPairs()) {
          finishCancelledPairRound()
          callback?.({
            ok: true,
            roundEnded: true,
            cancelled: true,
            message: 'Dört oyuncu da çift açtı. Tur iptal edildi.',
          })
          return
        }

        // Yandan alınan taş açılmış/açılmamış fark etmeksizin aynı tur masada
        // kullanılmalıdır. Kullanılmadıysa başka bir discard ile tur kapatılamaz.
        if (current.pickedDiscardRequiresOpening && current.pickedDiscardId) {
          broadcastGameState()
          callback?.({
            ok: false,
            message: 'Yandan aldığın taşı kullanmalısın veya geri koymalısın.',
          })
          return
        }

        const index = current.hand.findIndex(
          tile => tile.id === tileId
        )

        if (index < 0) {
          broadcastGameState()
          callback?.({
            ok: false,
            message: 'Taş elde bulunamadı.',
          })
          return
        }

        const tile = current.hand[index]
        const willFinish = current.hand.length === 1

        // Gösterge ancak bu tur gerçekten bitirilebiliyorsa alınabilir.
        // Başarısız denemede tüm masa/eldeki değişiklikleri çekmeden önceki
        // haline döndürüp eli normal deste-bitti kuralıyla bitiriyoruz.
        if (current.finalIndicatorId) {
          const indicatorStillInHand = current.hand.some(
            item => item.id === current.finalIndicatorId
          )

          if (!willFinish || indicatorStillInHand) {
            restoreFinalIndicatorSnapshot(current)

            finishRound(null, null, {
              reason: 'stock-exhausted',
            })

            callback?.({
              ok: false,
              roundEnded: true,
              message:
                'Gösterge yalnız oyunu bitirebiliyorsan alınabilir. Deneme geri alındı ve el sona erdi.',
            })
            return
          }
        }

        // Atılan taş masadaki bir pere işlenebiliyorsa +101.
        // Bitiş taşı bu cezadan muaftır. Gerçek okey normal discard edildiğinde
        // ise yalnız "okey discard" cezası uygulanır; aynı taş için ayrıca
        // işlek +101 yazılmaz.
        const isDiscardingRealJoker = isRealJoker(tile, game.joker)
        const discardedRealJoker = !willFinish && isDiscardingRealJoker
        const discardWasPlayable = !willFinish && canAddToAnyMeld(tile)

        if (discardWasPlayable && !discardedRealJoker) {
          addPenalty(
            current,
            101,
            `İşlek ${describeTileForScore(tile)} attı`
          )
        }

        // Okeyi normal discard olarak atmak +101 ceza.
        // Okeyle BİTİŞ özel puanlamaya tabidir, burada ayrıca +101 eklenmez.
        if (discardedRealJoker) {
          addPenalty(
            current,
            101,
            'Okey attı'
          )
        }

        current.hand.splice(index, 1)
        game.discardPile.push(tile)
        emitGameSfx(isDiscardingRealJoker ? 'okey-discard' : 'discard', {
          sourceSeat: current.seat,
        })
        game.lastDiscardOwnerId = current.id
        game.lastDiscardOwnerSeat = current.seat
        game.lastDiscardWasPlayable = Boolean(discardWasPlayable)

        current.mustDiscard = false
        clearPickedDiscardState(current)

        if (current.hand.length === 0) {
          const elden = Boolean(
            current.openedAllAtOnceTurn === game.turnCounter &&
            current.openedAllAtOnceNoOtherOpen
          )

          current.finalIndicatorId = null
          current.finalIndicatorSnapshot = null

          finishRound(current, tile, {
            reason: elden ? 'elden-finished' : 'player-finished',
            elden,
          })

          callback?.({
            ok: true,
            finished: true,
            elden,
          })
          return
        }

        current.finalIndicatorId = null
        current.finalIndicatorSnapshot = null

        // Son stok taşını çeken oyuncunun discardı stock-exhaustion elindeki
        // son hamledir. Burada roundu kapatıyoruz; sonraki oyuncuya currentSeat
        // geçmez ve boş stock ile yeni bir tur başlamaz.
        if (game.stock.length === 0) {
          finishRound(null, null, {
            reason: 'stock-exhausted',
          })

          callback?.({
            ok: true,
            roundEnded: true,
            stockExhausted: true,
          })
          return
        }

        advanceTurn()
        broadcastGameState()

        callback?.({
          ok: true,
        })
      })

      // ===================================================
      // DISCONNECT
      // ===================================================

      socket.on('disconnect', () => {
        const leavingId = socket.id
        players.delete(leavingId)
        lastChatAtByPlayerId.delete(leavingId)
        lastEmojiAtByPlayerId.delete(leavingId)
        lastPokeAtByTargetId.delete(leavingId)

        // Kick oylamasının hedefi/voterı ayrıldıysa state'i anında temizle veya
        // kalan insan sayısına göre çoğunluk eşiğini yeniden hesapla.
        if (kickVote) {
          kickVote.yesVoterIds.delete(leavingId)
          kickVote.noVoterIds.delete(leavingId)
          pruneKickVoteAndEvaluate()
        }

        // Gerçek oyuncunun ayrılması hangi fazda olursa olsun eski maç/round/ready
        // state'ini sürdürme. Çok hızlı gir-çık, maç-sonu veya round geçişi dahil
        // kalan kadro her zaman temiz lobby'ye döner; yeni maç yalnız herkes yeniden
        // HAZIR verdikten sonra Round 1'den başlar.
        resetMatchToFreshLobbyAfterHumanLeave()
        broadcastLobbyReadyReset('player-left')

        io.emit('player-left', {
          id: socket.id,
        })

        io.emit('players-state', getPublicPlayers())
        broadcastGameState()
      })
    queueStateChanged()
    return true
  }


  function getSummary() {
    const roster = [...players.values()]
    const humans = roster.filter(player => !player.isBot)
    const bots = roster.filter(player => player.isBot)
    const phase = game?.phase || 'waiting'
    return {
      id: String(tableId),
      name: `Masa ${tableId}`,
      playerCount: roster.length,
      humanCount: humans.length,
      botCount: bots.length,
      phase,
      round: Number(game?.round) || 0,
      maxRounds: MAX_ROUNDS,
      joinable: !destroyed && phase === 'waiting' && roster.length < MAX_PLAYERS,
    }
  }

  function canJoin() {
    const summary = getSummary()
    return summary.joinable
  }

  function hasHumanPlayers() {
    return [...players.values()].some(player => !player.isBot)
  }

  function destroy() {
    if (destroyed) return
    destroyed = true

    if (kickVote?.timeout) {
      clearTimeout(kickVote.timeout)
    }
    kickVote = null

    for (const request of pendingSeatSwapRequests.values()) {
      if (request?.timer) clearTimeout(request.timer)
    }
    pendingSeatSwapRequests.clear()
    lastChatAtByPlayerId.clear()
    lastEmojiAtByPlayerId.clear()
    lastPokeAtByTargetId.clear()
    // Do not mutate an in-flight bot's orphaned game object here. `destroyed`
    // suppresses all room output and scheduled entry points, while references
    // naturally become collectible after any currently awaited bot turn exits.
  }

  return {
    id: String(tableId),
    roomName,
    attachSocket,
    getSummary,
    canJoin,
    hasHumanPlayers,
    destroy,
    isDestroyed: () => destroyed,
    rules: {
      COLORS,
      SEATS,
      TEAM_DEFINITIONS,
      INITIAL_STOCK_COUNT,
      getTeamIdForSeat,
      selectWinningTeams,
      previousSeat,
      createDeck,
      getJokerInfo,
      isRealJoker,
      getEffectiveTile,
      validateGroup,
      validateRun,
      validateMeld,
      validatePair,
      validatePairs,
      isIndicatorTwinForIndicator,
      handValue,
      attemptLayoffPair,
      getKickRequiredVotes,
    },
    __botTest: {
      SEATS,
      players,
      createGame,
      createPlayerState,
      getJokerInfo,
      validateMeld,
      validatePair,
      createTableMeld,
      getBotRules,
      getBotContext,
      runBotTableActions,
      executeBotTableAction,
      botCanTakeDiscard,
      botDiscard,
      attemptLayoff,
      allPlayersOpenedPairs,
      attemptOpenMelds,
      setOpeningDraft,
      commitOpeningDraft,
      buildRoundScoreDetails,
      getHandPenaltyBreakdown,
      botV1,
      botV2,
      setGame(value) { game = value },
      getGame() { return game },
    },
  }
}

function createNullIo() {
  const chain = { emit() {} }
  return {
    to() { return chain },
    sockets: { sockets: new Map() },
  }
}

const testingRuntime = createTableRuntime(createNullIo(), '__testing__')

module.exports = {
  createTableRuntime,
  ...testingRuntime.rules,
}
