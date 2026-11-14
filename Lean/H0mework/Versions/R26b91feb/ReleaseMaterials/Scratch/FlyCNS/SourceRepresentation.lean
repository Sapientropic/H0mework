import H0mework.Realization.ObservationActions.WordsModel
import H0mework.Versions.R2.Realization.Operations.ObservationNative
import H0mework.Foundation.Relations.ConsumerQuotient
import Mathlib.Data.List.TakeDrop

/-! Subordinate whole-native representation producers. The autonomous letter is
the fixed process successor. Other letters are primitive source operations;
neither a future result nor a candidate's correctness enters that source.
The executable byte codec is separate from the minimum behavioral quotient. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace FlyCNS.WholeRepresentation

open SourceOperationNative
open SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

universe u v

def runMap {I : Type u} {C : Type v} (actions : I → C → C) : List I → C → C
  | [], state => state
  | letter :: rest, state => runMap actions rest (actions letter state)

variable {N : WorldRelationNetwork.{u}} (process : SourceNativeLivingRootProcess N)
variable {Intervention : Type u} (intervention : Intervention → process.State → process.State)
variable (system : IndependentConsumerSystem.{u, u} process.State)

abbrev Letter := PUnit.{u + 1} ⊕ Intervention

def autonomous : Letter (Intervention := Intervention) := .inl PUnit.unit

def step : Letter (Intervention := Intervention) → process.State → process.State
  | .inl _ => process.successor
  | .inr operation => intervention operation

abbrev execute := runMap (step process intervention)

noncomputable section

def linearAction (letter : Letter (Intervention := Intervention)) : Carrier process →ₗ[ℤ] Carrier process :=
  Finsupp.lmapDomain ℤ ℤ (step process intervention letter)

def consumerRead (state : process.State) : (consumer : system.Consumer) → system.Output consumer →₀ ℤ :=
  fun consumer => Finsupp.single (system.read consumer state) 1

def consumerObserver : Carrier process →ₗ[ℤ] ((consumer : system.Consumer) → system.Output consumer →₀ ℤ) :=
  observer process (consumerRead process system)

abbrev Model := SourceGeneratedActionWords.Model (linearAction process intervention)
  (consumerObserver process system) (autonomous (Intervention := Intervention))

def modelPoint (state : process.State) : Model process intervention system :=
  SourceGeneratedActionWords.projection (linearAction process intervention)
    (consumerObserver process system) autonomous (statePoint process state)

def modelAdvance (letter : Letter (Intervention := Intervention)) :
    Model process intervention system →ₗ[ℤ] Model process intervention system :=
  SourceGeneratedActionWords.advance (linearAction process intervention)
    (consumerObserver process system) autonomous letter

theorem linearAction_point (letter : Letter (Intervention := Intervention)) (state : process.State) :
    linearAction process intervention letter (statePoint process state) =
      statePoint process (step process intervention letter state) := by
  simp only [linearAction, statePoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem linearRun_point (word : List (Letter (Intervention := Intervention))) (state : process.State) :
    SourceGeneratedActionWords.run (linearAction process intervention) word (statePoint process state) =
      statePoint process (execute process intervention word state) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter rest previous =>
      change SourceGeneratedActionWords.run (linearAction process intervention) rest
        (linearAction process intervention letter (statePoint process state)) = _
      rw [linearAction_point, previous]
      rfl

theorem modelAdvance_point (letter : Letter (Intervention := Intervention)) (state : process.State) :
    modelAdvance process intervention system letter (modelPoint process intervention system state) =
      modelPoint process intervention system (step process intervention letter state) := by
  change SourceGeneratedActionWords.advance (linearAction process intervention)
    (consumerObserver process system) autonomous letter
    (SourceGeneratedActionWords.projection (linearAction process intervention)
      (consumerObserver process system) autonomous (statePoint process state)) = _
  rw [SourceGeneratedActionWords.advance_source, linearAction_point]
  rfl

/-- Exact future kernel, including every autonomous/input/intervention word
and every heterogeneous independently registered consumer. -/
theorem model_future_kernel (left right : process.State) :
    modelPoint process intervention system left = modelPoint process intervention system right ↔
      ∀ word : List (Letter (Intervention := Intervention)), ∀ consumer : system.Consumer,
        system.read consumer (execute process intervention word left) =
          system.read consumer (execute process intervention word right) := by
  rw [modelPoint, modelPoint, SourceGeneratedActionWords.projection_fibre]
  simp only [linearRun_point, consumerObserver, observer_statePoint]
  constructor
  · intro same word consumer
    have equal := congrFun (same word) consumer
    exact Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) equal
  · intro same word
    funext consumer
    change Finsupp.single (system.read consumer (execute process intervention word left)) (1 : ℤ) =
      Finsupp.single (system.read consumer (execute process intervention word right)) (1 : ℤ)
    rw [same word consumer]

def futureConsumers : IndependentConsumerSystem.{u, u} process.State where
  Consumer := List (Letter (Intervention := Intervention)) × system.Consumer
  Output index := system.Output index.2
  read index state := system.read index.2 (execute process intervention index.1 state)
  positive := by
    rcases system.positive with ⟨consumer⟩
    exact ⟨([], consumer)⟩

theorem model_kernel_exact :
    FaceKernelExactAt (futureConsumers process intervention system) (modelPoint process intervention system) := by
  intro left right
  rw [model_future_kernel]
  constructor
  · intro same index
    exact same index.1 index.2
  · intro same word consumer
    exact same (word, consumer)

theorem every_future_consumer_unique_factorization
    (index : (futureConsumers process intervention system).Consumer) :
    ∃! factor : Set.range (modelPoint process intervention system) →
        (futureConsumers process intervention system).Output index,
      ∀ state, factor ⟨modelPoint process intervention system state, state, rfl⟩ =
        (futureConsumers process intervention system).read index state :=
  (model_kernel_exact process intervention system).everyConsumer_unique_factorization index

theorem autonomous_is_actual (runtime : LivingRuntimeState process) :
    modelAdvance process intervention system autonomous
        (modelPoint process intervention system runtime.state) =
      modelPoint process intervention system runtime.tick.next.state :=
  modelAdvance_point process intervention system autonomous runtime.state

set_option linter.defProp false in
def all_consumer_model_and_root_factorizes (runtime : LivingRuntimeState process) :=
  And.intro (autonomous_is_actual process intervention system runtime)
    ((SourceOperationNative.point_factorizes runtime).2)

/-- A candidate which implements the same primitive operations and current
readers necessarily retains every future distinction. These laws constrain a
candidate, not the primitive source or its target quotient. -/
theorem model_minimal {Candidate : Type u}
    (represent : process.State → Candidate)
    (actions : Letter (Intervention := Intervention) → Candidate → Candidate)
    (reads : (consumer : system.Consumer) → Candidate → system.Output consumer)
    (action_commutes : ∀ letter state,
      actions letter (represent state) = represent (step process intervention letter state))
    (read_commutes : ∀ consumer state, reads consumer (represent state) = system.read consumer state) :
    Function.FactorsThrough (modelPoint process intervention system) represent := by
  have words (word : List (Letter (Intervention := Intervention))) (state : process.State) :
      runMap actions word (represent state) = represent (execute process intervention word state) := by
    induction word generalizing state with
    | nil => rfl
    | cons letter rest previous =>
        change runMap actions rest (actions letter (represent state)) = _
        rw [action_commutes, previous]
        rfl
  intro left right same
  apply (model_future_kernel process intervention system left right).2
  intro word consumer
  calc
    system.read consumer (execute process intervention word left) =
        reads consumer (runMap actions word (represent left)) := by rw [words, read_commutes]
    _ = reads consumer (runMap actions word (represent right)) := by rw [same]
    _ = system.read consumer (execute process intervention word right) := by rw [words, read_commutes]

/-- The revised source face recompiles the full word inventory. It retains
future new-reader differences even when their current values coincide. -/
theorem refined_model_future_kernel
    (newReadout : IndependentReadout.{u, u} process.State) (left right : process.State) :
    modelPoint process intervention (system.adjoin newReadout) left =
        modelPoint process intervention (system.adjoin newReadout) right ↔
      modelPoint process intervention system left = modelPoint process intervention system right ∧
        ∀ word : List (Letter (Intervention := Intervention)),
          newReadout.read (execute process intervention word left) =
            newReadout.read (execute process intervention word right) := by
  rw [model_future_kernel]
  constructor
  · intro same
    refine ⟨(model_future_kernel process intervention system left right).2 ?_, ?_⟩
    · intro word consumer
      exact same word (.inl consumer)
    · intro word
      exact same word (.inr PUnit.unit)
  · rintro ⟨oldSame, newSame⟩ word consumer
    cases consumer with
    | inl consumer => exact (model_future_kernel process intervention system left right).1 oldSame word consumer
    | inr _ => exact newSame word

theorem refined_future_escape_separates
    (newReadout : IndependentReadout.{u, u} process.State)
    (left right : process.State) (word : List (Letter (Intervention := Intervention)))
    (different : newReadout.read (execute process intervention word left) ≠
      newReadout.read (execute process intervention word right)) :
    modelPoint process intervention (system.adjoin newReadout) left ≠
      modelPoint process intervention (system.adjoin newReadout) right := by
  intro merged
  exact different (((refined_model_future_kernel process intervention system newReadout left right).1 merged).2 word)

end

/-! The codec reads opaque literal file bytes. Array interpretation, dtype,
IEEE signs/payloads and source JSON identities never enter a lossy projection. -/

inductive SnapshotFile where
  | neural | body | pendingAndPlastic | source
  deriving DecidableEq

abbrev Byte := Fin 256
abbrev Snapshot := SnapshotFile → List Byte

inductive Block where
  | zeros (length : Nat)
  | literal (bytes : List Byte)
  deriving DecidableEq

def expandBlock : Block → List Byte
  | .zeros length => List.replicate length 0
  | .literal bytes => bytes

def packBlock (bytes : List Byte) : Block :=
  if ∀ byte ∈ bytes, byte = 0 then .zeros bytes.length else .literal bytes

theorem expand_packBlock (bytes : List Byte) : expandBlock (packBlock bytes) = bytes := by
  unfold packBlock
  split_ifs with allZero
  · change List.replicate bytes.length 0 = bytes
    induction bytes with
    | nil => rfl
    | cons byte rest previous =>
        have head : byte = 0 := allZero byte (by simp)
        have tail : ∀ value ∈ rest, value = 0 := fun value member => allZero value (by simp [member])
        simp only [List.length_cons, List.replicate_succ, head, previous tail]
  · rfl

def unpack (blocks : List Block) : List Byte := (blocks.map expandBlock).flatten

def packAux : Nat → List Byte → List Block
  | 0, bytes => [.literal bytes]
  | _ + 1, [] => []
  | fuel + 1, byte :: rest =>
      packBlock ((byte :: rest).take 64) :: packAux fuel ((byte :: rest).drop 64)

theorem unpack_packAux (fuel : Nat) (bytes : List Byte) : unpack (packAux fuel bytes) = bytes := by
  induction fuel generalizing bytes with
  | zero => simp [packAux, unpack, expandBlock]
  | succ fuel previous =>
      cases bytes with
      | nil => rfl
      | cons byte rest =>
          change expandBlock (packBlock ((byte :: rest).take 64)) ++
            unpack (packAux fuel ((byte :: rest).drop 64)) = byte :: rest
          rw [expand_packBlock, previous, List.take_append_drop]

def encode (snapshot : Snapshot) : SnapshotFile → List Block :=
  fun file => packAux (snapshot file).length (snapshot file)

def decode (compressed : SnapshotFile → List Block) : Snapshot :=
  fun file => unpack (compressed file)

theorem decode_encode (snapshot : Snapshot) : decode (encode snapshot) = snapshot := by
  funext file
  exact unpack_packAux (snapshot file).length (snapshot file)

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

/-- The complete autonomous update is conjugated through exact decoding;
it is not replaced by an externally supplied list of selected actions. -/
def compressedNext (sourceNext : Snapshot → Snapshot) (compressed : SnapshotFile → List Block) :=
  encode (sourceNext (decode compressed))

theorem autonomous_codec_commutes (sourceNext : Snapshot → Snapshot) (snapshot : Snapshot) :
    compressedNext sourceNext (encode snapshot) = encode (sourceNext snapshot) := by
  simp only [compressedNext, decode_encode]

theorem decoded_autonomous_codec_commutes (sourceNext : Snapshot → Snapshot) (snapshot : Snapshot) :
    decode (compressedNext sourceNext (encode snapshot)) = sourceNext snapshot := by
  rw [autonomous_codec_commutes, decode_encode]

theorem all_readers_zero_error {Output : Type u} (reader : Snapshot → Output) (snapshot : Snapshot) :
    reader (decode (encode snapshot)) = reader snapshot := by rw [decode_encode]

theorem source_identity_separates (left right : Snapshot) (different : left ≠ right) :
    encode left ≠ encode right := fun merged => different (encode_injective merged)

end FlyCNS.WholeRepresentation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
