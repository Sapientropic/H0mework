import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3DeflateTree

set_option autoImplicit false
namespace FlyCNS.C3Deflate

structure Block where
  symbols : ByteArray
  start : Nat
  stop : Nat
  storedAvailable : Bool
  final : Bool

structure MatchState where
  window : ByteArray
  head : Array Nat
  previous : Array Nat
  position : Nat
  lookahead : Nat
  matchStart : Nat
  matchLength : Nat
  available : Bool
  blockStart : Int
  highWater : Nat
  inputRead : Nat
  inputEnd : Nat
  chunkIndex : Nat
  finish : Bool
  symbols : ByteArray
  blocks : Array Block

def initialMatch : MatchState :=
  ⟨⟨Array.replicate 65536 0⟩,Array.replicate 32768 0,Array.replicate 32768 0,
    0,0,0,2,false,0,0,0,0,0,false,ByteArray.empty,#[]⟩

def slideMatch (s : MatchState) : MatchState := Id.run do
  let mut window := s.window
  for i in [:s.position+s.lookahead-32768] do
    window:=window.set! i (window.get! (i+32768))
  let reduce := fun n => if n≥32768 then n-32768 else 0
  let head := s.head.map reduce
  let previous := s.previous.map reduce
  let oldMatch := (s.matchStart+4294967296-32768)%4294967296
  return { s with window:=window, head:=head, previous:=previous, position:=s.position-32768, matchStart:=oldMatch, blockStart:=s.blockStart-32768 }

/-- Native fill_window order, including sliding before the no-input test
and its guard-byte high-water law. Original chunk boundaries are retained. -/
def fillMatch (input : ByteArray) (before : MatchState) : MatchState := Id.run do
  let mut s := before
  for _ in [:2] do
    if s.position≥65274 then s:=slideMatch s
    if s.inputRead==s.inputEnd then break
    let amount := min (65536-s.position-s.lookahead) (s.inputEnd-s.inputRead)
    let mut window := s.window
    for i in [:amount] do
      window:=window.set! (s.position+s.lookahead+i) (input.get! (s.inputRead+i))
    s:={ s with window:=window, lookahead:=s.lookahead+amount, inputRead:=s.inputRead+amount }
    if s.lookahead≥262 || s.inputRead==s.inputEnd then break
  if s.highWater<65536 then
    let current := s.position+s.lookahead
    let start := if s.highWater<current then current else s.highWater
    let stop := min 65536 (current+258)
    let mut window := s.window
    for i in [start:stop] do window:=window.set! i 0
    s:={ s with window:=window, highWater:=max s.highWater stop }
  return s

def insertMatch (s : MatchState) (position : Nat) : MatchState × Nat :=
  let a := (s.window.get! position).toNat
  let b := (s.window.get! (position+1)).toNat
  let c := (s.window.get! (position+2)).toNat
  let key := ((a*1024) ^^^ (b*32) ^^^ c)%32768
  let old := s.head[key]!
  ({ s with head:=s.head.set! key position, previous:=s.previous.set! (position%32768) old },old)

/-- The original first hash candidate may lie exactly on MAX_DIST; subsequent
chain candidates require strict distance. The chain budget is 128/32 at level6. -/
def longestMatch (s : MatchState) (first previousLength : Nat) : MatchState × Nat := Id.run do
  let mut matchStart := s.matchStart
  let mut best := previousLength
  let mut candidate := first
  let limit := if s.position>32506 then s.position-32506 else 0
  let budget := if previousLength≥8 then 32 else 128
  let nice := min 128 s.lookahead
  for _ in [:budget] do
    let byte := fun position => s.window.get! position
    if byte (candidate+best)==byte (s.position+best) &&
        byte (candidate+best-1)==byte (s.position+best-1) &&
        byte candidate==byte s.position && byte (candidate+1)==byte (s.position+1) then
      let mut length := 3
      for offset in [3:258] do
        if byte (candidate+offset) != byte (s.position+offset) then break
        length:=offset+1
      if length>best then
        matchStart:=candidate
        best:=length
        if length≥nice then break
    candidate:=s.previous[candidate%32768]!
    if candidate≤limit then break
  return ({s with matchStart:=matchStart},min best s.lookahead)

def symbol (s : MatchState) (distance literal : Nat) : MatchState :=
  { s with symbols:=((s.symbols.push (UInt8.ofNat distance)).push (UInt8.ofNat (distance/256))).push (UInt8.ofNat literal) }

def flushMatch (s : MatchState) (final : Bool) : MatchState :=
  let stop := s.inputRead-s.lookahead
  let start := (Int.ofNat stop-Int.ofNat s.position+s.blockStart).toNat
  let block : Block := ⟨s.symbols,start,stop,s.blockStart≥0,final⟩
  { s with blocks:=s.blocks.push block, symbols:=ByteArray.empty, blockStart:=Int.ofNat s.position }

/-- Fixed zlib level6 deflate_slow over the given finite source input chunks.
Every emitted literal/match is computed from its own window and hash chain;
no tokens, dictionary, future output or compressor callback are supplied. -/
def matchBlocks (input : ByteArray) (ends : Array Nat) : Except String (Array Block) := do
  if ends.isEmpty || ends.back! != input.size then throw "source LZ77 input chunks omit bytes"
  let mut previousEnd := 0
  for ending in ends do
    if ending<previousEnd || ending>input.size then throw "source LZ77 chunk order changed"
    previousEnd:=ending
  let mut s := {initialMatch with inputEnd:=ends[0]!,chunkIndex:=1}
  let mut completed := false
  for _ in [:input.size+ends.size+2] do
    if s.lookahead<262 then
      s:=fillMatch input s
      if s.lookahead<262 && !s.finish then
        if s.chunkIndex<ends.size then
          s:={s with inputEnd:=ends[s.chunkIndex]!,chunkIndex:=s.chunkIndex+1}
        else s:={s with finish:=true}
        continue
      if s.lookahead==0 then
        if s.available then s:=symbol s 0 (s.window.get! (s.position-1)).toNat
        s:=flushMatch s true
        completed:=true
        break
    let mut head := 0
    if s.lookahead≥3 then
      let (inserted,old) := insertMatch s s.position
      s:=inserted
      head:=old
    let previousLength := s.matchLength
    let previousMatch := s.matchStart
    s:={s with matchLength:=2}
    if head != 0 && previousLength<16 && s.position-head≤32506 then
      let (searched,length) := longestMatch s head previousLength
      s:={searched with matchLength:=length}
      if length==3 && s.position-s.matchStart>4096 then s:={s with matchLength:=2}
    if previousLength≥3 && s.matchLength≤previousLength then
      let lastInsert := s.position+s.lookahead-3
      s:=symbol s (s.position-1-previousMatch) (previousLength-3)
      s:={s with lookahead:=s.lookahead-(previousLength-1)}
      for _ in [:previousLength-2] do
        s:={s with position:=s.position+1}
        if s.position≤lastInsert then s:=(insertMatch s s.position).1
      s:={s with available:=false,matchLength:=2,position:=s.position+1}
      if s.symbols.size==49149 then s:=flushMatch s false
    else if s.available then
      s:=symbol s 0 (s.window.get! (s.position-1)).toNat
      if s.symbols.size==49149 then s:=flushMatch s false
      s:={s with position:=s.position+1,lookahead:=s.lookahead-1}
    else
      s:={s with available:=true,position:=s.position+1,lookahead:=s.lookahead-1}
  if !completed then throw "source LZ77 execution omitted input"
  return s.blocks

end FlyCNS.C3Deflate
