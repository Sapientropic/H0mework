import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3DeflateLZ

set_option autoImplicit false
namespace FlyCNS.C3Deflate

def lengthExtra : Array Nat := #[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]
def lengthBase : Array Nat := #[0,1,2,3,4,5,6,7,8,10,12,14,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,0]
def distanceExtra : Array Nat := #[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]
def distanceBase : Array Nat := #[0,1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048,3072,4096,6144,8192,12288,16384,24576]
def headerOrder : Array Nat := #[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15]
def lengthCode (length : Nat) : Nat := Id.run do
  if length==255 then return 28
  for i in [:28] do
    if length<lengthBase[i]!+2^lengthExtra[i]! then return i
  return 28
def distanceCode (distance : Nat) : Nat := Id.run do
  for i in [:30] do
    if distance<distanceBase[i]!+2^distanceExtra[i]! then return i
  return 29

structure Bits where
  bytes : ByteArray
  value : Nat
  count : Nat
def emptyBits : Bits := ⟨ByteArray.empty,0,0⟩
def send (before : Bits) (value width : Nat) : Bits := Id.run do
  let mut b := {before with value:=before.value+value*2^before.count,count:=before.count+width}
  for _ in [:2] do
    if b.count<8 then break
    b:={b with bytes:=b.bytes.push (UInt8.ofNat b.value),value:=b.value/256,count:=b.count-8}
  return b
def align (b : Bits) : Bits :=
  if b.count==0 then b else ⟨b.bytes.push (UInt8.ofNat b.value),0,0⟩
def sendCode (bits : Bits) (tree : Tree) (symbol : Nat) : Bits :=
  send bits tree.codes[symbol]! tree.lengths[symbol]!

structure RunCode where
  symbol : Nat
  extra : Nat
  width : Nat

/-- Exact scan_tree/send_tree segmentation is generated independently for
literal and distance alphabets, preserving the initial -1 previous length. -/
def runCodes (tree : Tree) : Array RunCode := Id.run do
  let mut previous : Int := -1
  let mut next := tree.lengths[0]!
  let mut count := 0
  let mut maximum := if next==0 then 138 else 7
  let mut minimum := if next==0 then 3 else 4
  let mut codes := #[]
  for n in [:tree.maxCode+1] do
    let current := next
    next:=if n==tree.maxCode then 65535 else tree.lengths[n+1]!
    count:=count+1
    if count<maximum && current==next then continue
    if count<minimum then
      for _ in [:count] do codes:=codes.push ⟨current,0,0⟩
    else if current != 0 then
      if Int.ofNat current != previous then
        codes:=codes.push ⟨current,0,0⟩
        count:=count-1
      codes:=codes.push ⟨16,count-3,2⟩
    else if count≤10 then codes:=codes.push ⟨17,count-3,3⟩
    else codes:=codes.push ⟨18,count-11,7⟩
    count:=0
    previous:=Int.ofNat current
    if next==0 then
      maximum:=138
      minimum:=3
    else if current==next then
      maximum:=6
      minimum:=3
    else
      maximum:=7
      minimum:=4
  return codes

def staticLiteralLength (symbol : Nat) : Nat :=
  if symbol≤143 then 8 else if symbol≤255 then 9 else if symbol≤279 then 7 else 8
def staticLiteral : Tree :=
  let lengths := (List.range 288).toArray.map staticLiteralLength
  let counts := (List.range 16).toArray.map fun i => lengths.filter (· == i) |>.size
  decorate ⟨#[],#[],#[],lengths,Array.replicate 288 0,#[],0,0,287,counts⟩
def staticDistance : Tree :=
  ⟨#[],#[],#[],Array.replicate 30 5,(List.range 30).toArray.map (fun i => reverseBits i 5),#[],0,0,29,#[]⟩

def frequencies (symbols : ByteArray) : Array Nat × Array Nat := Id.run do
  let mut literals := (Array.replicate 286 0).set! 256 1
  let mut distances := Array.replicate 30 0
  for i in [:symbols.size/3] do
    let distance := (symbols.get! (3*i)).toNat+256*(symbols.get! (3*i+1)).toNat
    let literal := (symbols.get! (3*i+2)).toNat
    if distance==0 then literals:=literals.set! literal (literals[literal]!+1)
    else
      let l := lengthCode literal+257
      let d := distanceCode (distance-1)
      literals:=literals.set! l (literals[l]!+1)
      distances:=distances.set! d (distances[d]!+1)
  return (literals,distances)

def dataCost (lf df : Array Nat) (literal distance : Tree) : Nat := Id.run do
  let mut bits := 0
  for n in [:286] do
    let extra := if n≥257 then lengthExtra[n-257]! else 0
    bits:=bits+lf[n]!*(literal.lengths[n]!+extra)
  for n in [:30] do bits:=bits+df[n]!*(distance.lengths[n]!+distanceExtra[n]!)
  return bits

def sendSymbols (before : Bits) (symbols : ByteArray) (literal distance : Tree) : Bits := Id.run do
  let mut b := before
  for i in [:symbols.size/3] do
    let dist := (symbols.get! (3*i)).toNat+256*(symbols.get! (3*i+1)).toNat
    let lc := (symbols.get! (3*i+2)).toNat
    if dist==0 then b:=sendCode b literal lc
    else
      let l := lengthCode lc
      b:=sendCode b literal (l+257)
      if lengthExtra[l]! != 0 then b:=send b (lc-lengthBase[l]!) lengthExtra[l]!
      let d := distanceCode (dist-1)
      b:=sendCode b distance d
      if distanceExtra[d]! != 0 then b:=send b (dist-1-distanceBase[d]!) distanceExtra[d]!
  return sendCode b literal 256

/-- Source _tr_flush_block: costs from own frequencies/RLE decide stored,
fixed or dynamic; original active-window availability controls stored blocks. -/
def sendBlock (input : ByteArray) (before : Bits) (block : Block) : Except String Bits := do
  let (lf,df) := frequencies block.symbols
  let literal ← build lf 15
  let distance ← build df 15
  let runs := runCodes literal ++ runCodes distance
  let mut hf := Array.replicate 19 0
  for r in runs do hf:=hf.set! r.symbol (hf[r.symbol]!+1)
  let header ← build hf 7
  let mut headerCount := 19
  for _ in [:15] do
    if header.lengths[headerOrder[headerCount-1]!]! != 0 then break
    headerCount:=headerCount-1
  let headerCost := runs.foldl (fun total r => total+header.lengths[r.symbol]!+r.width) 0
  let dynamicCost := dataCost lf df literal distance+headerCost+3*headerCount+14
  let fixedCost := dataCost lf df staticLiteral staticDistance
  let fixedBytes := (fixedCost+10)/8
  let dynamicBytes := (dynamicCost+10)/8
  let final := if block.final then 1 else 0
  let mut b := before
  if block.stop-block.start+4≤min fixedBytes dynamicBytes && block.storedAvailable then
    b:=align (send b final 3)
    let size := block.stop-block.start
    for byte in #[size%256,size/256,(65535-size)%256,(65535-size)/256] do
      b:={b with bytes:=b.bytes.push (UInt8.ofNat byte)}
    b:={b with bytes:=b.bytes++input.extract block.start block.stop}
  else if fixedBytes≤dynamicBytes then
    b:=sendSymbols (send b (2+final) 3) block.symbols staticLiteral staticDistance
  else
    b:=send b (4+final) 3
    b:=send b (literal.maxCode+1-257) 5
    b:=send b (distance.maxCode+1-1) 5
    b:=send b (headerCount-4) 4
    for i in [:headerCount] do b:=send b header.lengths[headerOrder[i]!]! 3
    for r in runs do
      b:=sendCode b header r.symbol
      if r.width != 0 then b:=send b r.extra r.width
    b:=sendSymbols b block.symbols literal distance
  return if block.final then align b else b

def compress (input : ByteArray) (ends : Array Nat) : Except String ByteArray := do
  let blocks ← matchBlocks input ends
  let mut bits := emptyBits
  for block in blocks do bits←sendBlock input bits block
  return bits.bytes

end FlyCNS.C3Deflate
