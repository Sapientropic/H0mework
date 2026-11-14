import Lean

set_option autoImplicit false
namespace FlyCNS.C3Deflate

def heapSize : Nat := 573
structure Tree where
  frequency : Array Nat
  depth : Array Nat
  parent : Array Nat
  lengths : Array Nat
  codes : Array Nat
  heap : Array Nat
  heapLength : Nat
  heapStart : Nat
  maxCode : Nat
  lengthCounts : Array Nat

def smaller (t : Tree) (n m : Nat) : Bool :=
  t.frequency[n]! < t.frequency[m]! ||
    (t.frequency[n]! == t.frequency[m]! && t.depth[n]! ≤ t.depth[m]!)

/-- Exact source heap tie rule: equal depth chooses the right child; equal
frequency/depth keeps the current parent. -/
def downHeap (tree : Tree) (start : Nat) : Tree := Id.run do
  let mut t := tree
  let value := t.heap[start]!
  let mut k := start
  let mut j := 2*k
  for _ in [:heapSize] do
    if j>t.heapLength then break
    if j<t.heapLength && smaller t t.heap[j+1]! t.heap[j]! then j:=j+1
    if smaller t value t.heap[j]! then break
    t:={t with heap:=t.heap.set! k t.heap[j]!}
    k:=j
    j:=2*j
  return {t with heap:=t.heap.set! k value}

def reverseBits (value count : Nat) : Nat := Id.run do
  let mut input := value
  let mut output := 0
  for _ in [:count] do
    output:=2*output+input%2
    input:=input/2
  return output

def decorate (tree : Tree) : Tree := Id.run do
  let mut t := tree
  let mut next := Array.replicate 16 0
  let mut code := 0
  for bits in [1:16] do
    code:=2*(code+t.lengthCounts[bits-1]!)
    next:=next.set! bits code
  for n in [:t.maxCode+1] do
    let bits := t.lengths[n]!
    if bits != 0 then
      t:={t with codes:=t.codes.set! n (reverseBits next[bits]! bits)}
      next:=next.set! bits (next[bits]!+1)
  return t

def bitLengths (tree : Tree) (maximum : Nat) : Tree := Id.run do
  let initialLengths := tree.lengths.set! (tree.heap[tree.heapStart]!) 0
  let mut t := { tree with lengths := initialLengths, lengthCounts := Array.replicate 16 0 }
  let mut overflow := 0
  for h in [t.heapStart+1:heapSize] do
    let n := t.heap[h]!
    let wanted := t.lengths[t.parent[n]!]!+1
    let bits := min wanted maximum
    if wanted>maximum then overflow:=overflow+1
    t:={t with lengths:=t.lengths.set! n bits}
    if n≤t.maxCode then
      t:={t with lengthCounts:=t.lengthCounts.set! bits (t.lengthCounts[bits]!+1)}
  if overflow>0 then
    for _ in [:heapSize] do
      let mut bits := maximum-1
      for _ in [:15] do
        if t.lengthCounts[bits]! != 0 then break
        bits:=bits-1
      let counts := t.lengthCounts.set! bits (t.lengthCounts[bits]!-1)
      let counts := counts.set! (bits+1) (counts[bits+1]!+2)
      let counts := counts.set! maximum (counts[maximum]!-1)
      t:={t with lengthCounts:=counts}
      if overflow≤2 then break
      overflow:=overflow-2
    let mut h := heapSize
    for offset in [:maximum] do
      let bits := maximum-offset
      let mut remaining := t.lengthCounts[bits]!
      for _ in [:heapSize] do
        if remaining==0 then break
        h:=h-1
        let n := t.heap[h]!
        if n≤t.maxCode then
          t:={t with lengths:=t.lengths.set! n bits}
          remaining:=remaining-1
  return t

/-- zlib 1.2.12 build_tree/gen_bitlen/gen_codes, including artificial leaves,
reverse heap order, overflow redistribution and canonical reversed codes.
Only the input symbol frequencies enter; no completed tree is accepted. -/
def build (frequencies : Array Nat) (maximum : Nat) : Except String Tree := do
  let elements := frequencies.size
  if elements != 286 && elements != 30 && elements != 19 then
    throw "source DEFLATE alphabet has another size"
  if maximum != 15 && maximum != 7 then throw "source DEFLATE maximum length changed"
  if frequencies.foldl (· + ·) 0 > 16384 then throw "source DEFLATE block frequency exceeds its symbol buffer"
  let mut t : Tree := ⟨frequencies++Array.replicate (heapSize-elements) 0,
    Array.replicate heapSize 0,Array.replicate heapSize 0,Array.replicate heapSize 0,
    Array.replicate heapSize 0,Array.replicate heapSize 0,0,heapSize,0,Array.replicate 16 0⟩
  let mut found := false
  for n in [:elements] do
    if t.frequency[n]! != 0 then
      t:={t with heapLength:=t.heapLength+1,heap:=t.heap.set! (t.heapLength+1) n,maxCode:=n}
      found:=true
  for _ in [:2] do
    if t.heapLength≥2 then break
    let node := if !found then 0 else if t.maxCode<2 then t.maxCode+1 else 0
    let nextMaximum := if !found || t.maxCode<2 then node else t.maxCode
    let updatedHeap := t.heap.set! (t.heapLength+1) node
    let updatedFrequency := t.frequency.set! node 1
    t := { t with heapLength := t.heapLength+1, heap := updatedHeap, maxCode := nextMaximum, frequency := updatedFrequency }
    found:=true
  for offset in [:t.heapLength/2] do
    t:=downHeap t (t.heapLength/2-offset)
  let mut node := elements
  for _ in [:elements-1] do
    let n := t.heap[1]!
    t:={t with heap:=t.heap.set! 1 t.heap[t.heapLength]!,heapLength:=t.heapLength-1}
    t:=downHeap t 1
    let m := t.heap[1]!
    let heap := (t.heap.set! (t.heapStart-1) n).set! (t.heapStart-2) m
    let frequencies := t.frequency.set! node (t.frequency[n]!+t.frequency[m]!)
    let depths := t.depth.set! node (max t.depth[n]! t.depth[m]!+1)
    let parents := (t.parent.set! n node).set! m node
    t := { t with heap := heap, heapStart := t.heapStart-2, frequency := frequencies, depth := depths, parent := parents }
    t:={t with heap:=t.heap.set! 1 node}
    node:=node+1
    t:=downHeap t 1
    if t.heapLength<2 then break
  t:={t with heapStart:=t.heapStart-1,heap:=t.heap.set! (t.heapStart-1) t.heap[1]!}
  return decorate (bitLengths t maximum)

end FlyCNS.C3Deflate
