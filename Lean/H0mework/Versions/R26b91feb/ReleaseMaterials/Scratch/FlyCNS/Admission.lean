import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceStep
import Init.System.IO

/-! Source-only loading. Complete array bytes are parsed before any root seed
exists. Counts and digests locate the expected source; they never replace its
edge/weight/transmitter material. NPY is the independently checked CSR image
of the three official Feather files, with every original source row retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace Admission

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

def neuronCount : Nat := 165122
def edgeCount : Nat := 25563197
def officialEdgeRows : Nat := 151856684

/-- The bounded byte accessor avoids boxing/copying the whole payload for
each read through `ByteArray.data`. -/
def byteNat (bytes : ByteArray) (index : Nat) : Nat :=
  if within : index < bytes.size then (bytes.get index within).toNat else 0

def littleWord (bytes : ByteArray) (start width : Nat) : Nat :=
  (List.range width).foldl
    (fun total offset => total + byteNat bytes (start + offset) * 256 ^ offset) 0

structure NpyVector (bytes : ByteArray) where
  private mk ::
  dataStart : Nat
  width : Nat
  count : Nat
  size_eq : bytes.size = dataStart + width * count

def NpyVector.word {bytes : ByteArray} (vector : NpyVector bytes) (index : Nat) : Nat :=
  littleWord bytes (vector.dataStart + vector.width * index) vector.width

def compactHeader (header : String) : String :=
  String.ofList (header.toList.filter (fun character => !character.isWhitespace))

def parseHeaderCount (header dtype : String) : Except String Nat := do
  let pieces := (compactHeader header).splitOn "'shape':("
  match pieces with
  | [npyHeaderPrefix, remaining] =>
    if npyHeaderPrefix != "{'descr':'" ++ dtype ++ "','fortran_order':False," then
      throw "unsupported NPY dtype/order/header"
    match remaining.splitOn ",),}" with
    | [dimension, ""] =>
      match dimension.toNat? with
      | some count => return count
      | none => throw "invalid NPY dimension"
    | _ => throw "NPY source must be one-dimensional"
  | _ => throw "NPY source must have exactly one shape"

def parseNpyVector (bytes : ByteArray) (dtype : String) (width : Nat) :
    Except String (NpyVector bytes) := do
  if bytes.size < 10 then throw "truncated NPY prefix"
  if (List.range 6).any (fun index => byteNat bytes index !=
      ([147, 78, 85, 77, 80, 89] : List Nat)[index]?.getD 0) then
    throw "invalid NPY magic"
  let version := byteNat bytes 6
  if byteNat bytes 7 != 0 then throw "unsupported NPY minor version"
  let headerStart ←
    if version = 1 then pure 10
    else if version = 2 ∨ version = 3 then pure 12
    else throw "unsupported NPY major version"
  let headerWidth := if version = 1 then 2 else 4
  if bytes.size < headerStart then throw "truncated NPY version prefix"
  let headerLength := littleWord bytes 8 headerWidth
  let dataStart := headerStart + headerLength
  if dataStart > bytes.size then throw "truncated NPY header"
  let header ← match String.fromUTF8? (bytes.extract headerStart dataStart) with
    | some text => pure text
    | none => throw "invalid NPY header encoding"
  let count ← parseHeaderCount header dtype
  if exactSize : bytes.size = dataStart + width * count then
    return ⟨dataStart, width, count, exactSize⟩
  else throw "NPY payload length differs from its complete declared vector"

structure GraphBytes where
  bodyIds : ByteArray
  indptr : ByteArray
  indices : ByteArray
  counts : ByteArray
  sign : ByteArray
  sourceRow : ByteArray

structure GraphVectors where
  private mk ::
  original : GraphBytes
  bodyIds : NpyVector original.bodyIds
  indptr : NpyVector original.indptr
  indices : NpyVector original.indices
  counts : NpyVector original.counts
  sign : NpyVector original.sign
  sourceRow : NpyVector original.sourceRow

def parseGraphVectors (bytes : GraphBytes) : Except String GraphVectors := do
  let bodyIds ← parseNpyVector bytes.bodyIds "<i8" 8
  let indptr ← parseNpyVector bytes.indptr "<i8" 8
  let indices ← parseNpyVector bytes.indices "<i4" 4
  let counts ← parseNpyVector bytes.counts "<i8" 8
  let sign ← parseNpyVector bytes.sign "|i1" 1
  let sourceRow ← parseNpyVector bytes.sourceRow "<i8" 8
  return ⟨bytes, bodyIds, indptr, indices, counts, sign, sourceRow⟩

def locatePre {bytes : ByteArray} (pointers : NpyVector bytes) (edge : Nat) : Nat → Nat → Nat → Nat
  | 0, low, _high => low
  | fuel + 1, low, high =>
    if low + 1 < high then
      let middle := (low + high) / 2
      if pointers.word middle ≤ edge then locatePre pointers edge fuel middle high
      else locatePre pointers edge fuel low middle
    else low

theorem locatePre_bound {bytes : ByteArray} (pointers : NpyVector bytes) (edge fuel low high limit : Nat)
    (low_lt : low < limit) (low_le : low ≤ high) (high_le : high ≤ limit) :
    locatePre pointers edge fuel low high < limit := by
  induction fuel generalizing low high with
  | zero => exact low_lt
  | succ fuel inductionHypothesis =>
    simp only [locatePre]
    split
    · split
      · apply inductionHypothesis <;> omega
      · apply inductionHypothesis <;> omega
    · exact low_lt

def sourcePre (vectors : GraphVectors) (edge : Nat) : Nat :=
  locatePre vectors.indptr edge 64 0 neuronCount

def CompleteCSRAt (vectors : GraphVectors) : Prop :=
  vectors.bodyIds.count = neuronCount ∧
  vectors.indptr.count = neuronCount + 1 ∧
  vectors.sign.count = neuronCount ∧
  vectors.indices.count = edgeCount ∧
  vectors.counts.count = edgeCount ∧
  vectors.sourceRow.count = edgeCount ∧
  vectors.indptr.word 0 = 0 ∧ vectors.indptr.word neuronCount = edgeCount ∧
  (∀ neuron : Fin neuronCount,
    vectors.bodyIds.word neuron.val < 2 ^ 63 ∧
    vectors.indptr.word neuron.val ≤ vectors.indptr.word (neuron.val + 1) ∧
    vectors.indptr.word (neuron.val + 1) ≤ edgeCount ∧
    (vectors.sign.word neuron.val = 0 ∨ vectors.sign.word neuron.val = 1 ∨
      vectors.sign.word neuron.val = 255)) ∧
  (∀ edge : Fin edgeCount,
    vectors.indices.word edge.val < neuronCount ∧
    0 < vectors.counts.word edge.val ∧ vectors.counts.word edge.val < 2 ^ 63 ∧
    vectors.sourceRow.word edge.val < officialEdgeRows ∧
    vectors.indptr.word (sourcePre vectors edge.val) ≤ edge.val ∧
    edge.val < vectors.indptr.word (sourcePre vectors edge.val + 1))

instance (vectors : GraphVectors) : Decidable (CompleteCSRAt vectors) := by
  unfold CompleteCSRAt
  infer_instance

structure AdmittedGraph where
  private mk ::
  vectors : GraphVectors
  complete : CompleteCSRAt vectors

def admitGraphBytes (bytes : GraphBytes) : Except String AdmittedGraph := do
  let vectors ← parseGraphVectors bytes
  if complete : CompleteCSRAt vectors then return ⟨vectors, complete⟩
  else throw "invalid complete CSR source/domain/edge material"

def AdmittedGraph.rawGraph (admitted : AdmittedGraph) : RawGraph neuronCount edgeCount where
  bodyId := fun neuron => admitted.vectors.bodyIds.word neuron.val
  pre := fun edge => ⟨sourcePre admitted.vectors edge.val,
    locatePre_bound admitted.vectors.indptr edge.val 64 0 neuronCount neuronCount
      (by decide) (Nat.zero_le _) (Nat.le_refl _)⟩
  post := fun edge => ⟨admitted.vectors.indices.word edge.val,
    (admitted.complete.2.2.2.2.2.2.2.2.2 edge).1⟩
  contacts := fun edge => admitted.vectors.counts.word edge.val
  transmitterSign := fun neuron =>
    let value := admitted.vectors.sign.word neuron.val
    if value = 255 then -1 else Int.ofNat value

def AdmittedGraph.originalSourceRow (admitted : AdmittedGraph) (edge : Fin edgeCount) : Nat :=
  admitted.vectors.sourceRow.word edge.val

theorem rawGraph_contacts_are_source_words (admitted : AdmittedGraph) (edge : Fin edgeCount) :
    admitted.rawGraph.contacts edge = admitted.vectors.counts.word edge.val := rfl

theorem rawGraph_post_is_source_word (admitted : AdmittedGraph) (edge : Fin edgeCount) :
    (admitted.rawGraph.post edge).val = admitted.vectors.indices.word edge.val := rfl

theorem rawGraph_pre_uses_actual_CSR_interval (admitted : AdmittedGraph) (edge : Fin edgeCount) :
    admitted.vectors.indptr.word (admitted.rawGraph.pre edge).val ≤ edge.val ∧
      edge.val < admitted.vectors.indptr.word ((admitted.rawGraph.pre edge).val + 1) :=
  ⟨(admitted.complete.2.2.2.2.2.2.2.2.2 edge).2.2.2.2.1,
    (admitted.complete.2.2.2.2.2.2.2.2.2 edge).2.2.2.2.2⟩

def addressedTop53 (seed : UInt64) (tick neuron : Nat) : Nat :=
  let first := seed ^^^ (UInt64.ofNat (tick + 1) * 0x9E3779B97F4A7C15)
  let second := first ^^^ (UInt64.ofNat (neuron + 1) * 0xBF58476D1CE4E5B9)
  let third := (second ^^^ (second >>> 30)) * 0xBF58476D1CE4E5B9
  let fourth := (third ^^^ (third >>> 27)) * 0x94D049BB133111EB
  ((fourth ^^^ (fourth >>> 31)) >>> 11).toNat

def registeredPulse (stimulus : List (Fin neuronCount)) (tick : Nat) : RawPulse neuronCount :=
  fun neuron =>
    if neuron ∈ stimulus ∧ addressedTop53 7 tick neuron.val < 360287970189640 then 68750 else 0

/-- Bounded input programme generated only from registered sensory addresses,
the seed and duration. No spike, choice, memory or successor output is input. -/
def sourceSpec (admitted : AdmittedGraph) (stimulus : List (Fin neuronCount))
    (duration : Nat) : SourceSpec neuronCount edgeCount where
  graph := admitted.rawGraph
  initial := initialState neuronCount edgeCount 7
  pulses := (List.range duration).map (registeredPulse stimulus)

def sourceFacade (admitted : AdmittedGraph) (stimulus : List (Fin neuronCount))
    (duration : Nat) := runtimeFacade (sourceSpec admitted stimulus duration)

def sourceSeed (admitted : AdmittedGraph) (stimulus : List (Fin neuronCount))
    (duration : Nat) := (sourceFacade admitted stimulus duration).seed

theorem sourceSeed_initial_material (admitted : AdmittedGraph)
    (stimulus : List (Fin neuronCount)) (duration : Nat) :
    (sourceSeed admitted stimulus duration).state.current =
      initialState neuronCount edgeCount 7 := rfl

theorem sourceSeed_actual_next (admitted : AdmittedGraph)
    (stimulus : List (Fin neuronCount)) (duration : Nat) :
    (sourceSeed admitted stimulus duration).tick.next.state.current =
      neuralStep (sourceSpec admitted stimulus duration)
        (initialState neuronCount edgeCount 7) := rfl

def sugarIndices : List Nat :=
  [54020, 59017, 65043, 70052, 76505, 90102, 101856, 103233, 114994,
    116883, 118774, 120175, 122180, 122205, 124722, 126787, 133426,
    162830, 163191, 163409, 163578, 163826, 163952]

/-- Source-fixed sensory domain: the 23 `gustatory` / `LB3c` annotations in
the retained MaleCNS domain. This roster is initialization data. -/
def sugarStimulus : List (Fin neuronCount) :=
  sugarIndices.attach.map (fun neuron => ⟨neuron.val, by
    have bounded : ∀ number ∈ sugarIndices, number < neuronCount := by decide
    exact bounded neuron.val neuron.property⟩)

structure MaleCNSAdmission where
  private mk ::
  graph : AdmittedGraph
  annotations : ByteArray
  neurotransmitters : ByteArray
  originalWeights : ByteArray

/-- Hash the exact in-memory bytes which the parser will consume. File paths
are not hashed in a separate read, so replacement between reads cannot bind
one payload while parsing another. This is an empirical source locator. -/
def sha256Bytes (bytes : ByteArray) : IO String := do
  let child ← do
    let (input, child) ← (← IO.Process.spawn
      { cmd := "shasum", args := #["-a", "256"],
        stdin := .piped, stdout := .piped, stderr := .piped }).takeStdin
    input.write bytes
    input.flush
    pure child
  let output ← child.stdout.readToEnd
  let errors ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then throw (IO.userError ("source digest failed: " ++ errors))
  match output.splitOn " " with
  | digest :: _ => return digest
  | [] => throw (IO.userError "source digest missing")

def readFrozenFile (relative expectedSha : String) (expectedSize : Nat) : IO ByteArray := do
  let bytes ← IO.FS.readBinFile (System.FilePath.mk "Biomedical/Connectomics/.local" / relative)
  if bytes.size != expectedSize then throw (IO.userError ("source size changed: " ++ relative))
  if (← sha256Bytes bytes) != expectedSha then throw (IO.userError ("source bytes changed: " ++ relative))
  return bytes

/-- The fixed loader reads complete source bytes and admits only their
decoded graph. It has no run, target state, spike count or verdict argument. -/
def loadMaleCNSFullGraph : IO MaleCNSAdmission := do
  let annotations ← readFrozenFile "data/body-annotations-male-cns-v1.0-minconf-0.5.feather"
    "2177e246113e4cfbf1e7772ec37c6da1955ff22e8063d0b1f833101f99a9a3b2" 14483314
  let neurotransmitters ← readFrozenFile "data/body-neurotransmitters-male-cns-v1.0.feather"
    "95c9289220663abeb3409f3ad9e5a7f8a53f8093f5139d15502cd08da8879621" 43282834
  let originalWeights ← readFrozenFile "data/connectome-weights-male-cns-v1.0-minconf-0.5.feather"
    "e35da783d1c686b2b58b3b87cd6a403ae43bfcfba8bff28e08ef752c1a56afc1" 1051241946
  let bodyIds ← readFrozenFile "graph/body_ids.npy"
    "f3f01542613e06bf6eb000f54a4f0fde005f6471739b40d15fd6a2e2f16f2065" 1321104
  let indptr ← readFrozenFile "graph/indptr.npy"
    "ee4cdd67ca2aaa4e7df58c9f08c41506af3e541161954873e80f71344691fea4" 1321112
  let indices ← readFrozenFile "graph/indices.npy"
    "efd277e9c1ac09c16ca71120352cdb5a353589e6b554aac2ec329ec2ff20e84c" 102252916
  let counts ← readFrozenFile "graph/counts.npy"
    "f6fd34cdef6649d3d4012471ced06df29cb4d065609275a13409057198f1ecec" 204505704
  let sign ← readFrozenFile "graph/sign.npy"
    "82d3f498bad789bf2da3f2dc05585bc7556d03cc83b0982156c596f28f6a7d95" 165250
  let sourceRow ← readFrozenFile "graph/source_row.npy"
    "868fb26b55811c1b045fab737160a1931b48834e243cd299c7764910c91196d5" 204505704
  match admitGraphBytes ⟨bodyIds, indptr, indices, counts, sign, sourceRow⟩ with
  | .ok graph => return ⟨graph, annotations, neurotransmitters, originalWeights⟩
  | .error reason => throw (IO.userError reason)

def maleCNSFullGraphFacade (admitted : MaleCNSAdmission) :=
  sourceFacade admitted.graph sugarStimulus 5000

def maleCNSFullGraphSeed (admitted : MaleCNSAdmission) :=
  (maleCNSFullGraphFacade admitted).seed

def loadMaleCNSFullGraphSeed : IO
    (Σ admitted : MaleCNSAdmission,
      LivingRuntimeState (maleCNSFullGraphFacade admitted).process) := do
  let admitted ← loadMaleCNSFullGraph
  return ⟨admitted, maleCNSFullGraphSeed admitted⟩

set_option linter.defProp false in
def maleCNSFullGraph_seed_factorizes (admitted : MaleCNSAdmission) :=
  (maleCNSFullGraphFacade admitted).readoutAt_factorizes
    (maleCNSFullGraphSeed admitted) .before

end Admission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
