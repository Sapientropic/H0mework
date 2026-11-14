import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceRepresentation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

/-! Executable minimal future models generated from a complete finite raw
source.  Current reads start the partition; source successors refine it.
No quotient, correct partition, future table or normalizer enters the source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace FiniteMinimalModel

structure Source where
  stateCount : Nat
  letterCount : Nat
  readerCount : Nat
  Output : Fin readerCount → Type
  outputEq : (reader : Fin readerCount) → DecidableEq (Output reader)
  initial : Fin stateCount
  autonomous : Fin letterCount
  reader : Fin readerCount
  action : Fin letterCount → Fin stateCount → Fin stateCount
  read : (reader : Fin readerCount) → Fin stateCount → Output reader

abbrev State (source : Source) := Fin source.stateCount
abbrev Letter (source : Source) := Fin source.letterCount
abbrev Pair (source : Source) := State source × State source

instance (source : Source) (reader : Fin source.readerCount) : DecidableEq (source.Output reader) :=
  source.outputEq reader

variable (source : Source)

def sameReads (left right : State source) : Prop :=
  ∀ reader, source.read reader left = source.read reader right

instance (left right : State source) : Decidable (sameReads source left right) := by
  unfold sameReads
  infer_instance

def initialPairs : Finset (Pair source) :=
  Finset.univ.filter fun pair => sameReads source pair.1 pair.2

def refine (pairs : Finset (Pair source)) : Finset (Pair source) :=
  pairs.filter fun pair =>
    ∀ letter, (source.action letter pair.1, source.action letter pair.2) ∈ pairs

theorem mem_initial (left right : State source) :
    (left, right) ∈ initialPairs source ↔ sameReads source left right := by
  simp [initialPairs]

theorem mem_refine (pairs : Finset (Pair source)) (left right : State source) :
    (left, right) ∈ refine source pairs ↔
      (left, right) ∈ pairs ∧
        ∀ letter, (source.action letter left, source.action letter right) ∈ pairs := by
  simp [refine]

theorem refine_subset (pairs : Finset (Pair source)) : refine source pairs ⊆ pairs :=
  Finset.filter_subset _ _

theorem strict_refinement_decreases (pairs : Finset (Pair source))
    (different : refine source pairs ≠ pairs) :
    (refine source pairs).card < pairs.card :=
  Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).2 ⟨refine_subset source pairs, different⟩)

/-- Each nonfixed iteration removes a real raw-state pair.  The supplied
fuel is a generated bound, not a correctness certificate. -/
def settle : Nat → Finset (Pair source) → Finset (Pair source)
  | 0, pairs => pairs
  | fuel + 1, pairs =>
      let next := refine source pairs
      if next = pairs then pairs else settle fuel next

theorem settle_subset (fuel : Nat) (pairs : Finset (Pair source)) :
    settle source fuel pairs ⊆ pairs := by
  induction fuel generalizing pairs with
  | zero => exact Finset.Subset.refl pairs
  | succ fuel previous =>
      simp only [settle]
      split_ifs with fixed
      · exact Finset.Subset.refl pairs
      · exact (previous (refine source pairs)).trans (refine_subset source pairs)

theorem settle_fixed (fuel : Nat) (pairs : Finset (Pair source)) (enough : pairs.card ≤ fuel) :
    refine source (settle source fuel pairs) = settle source fuel pairs := by
  induction fuel generalizing pairs with
  | zero =>
      have empty : pairs = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [settle, empty, refine]
  | succ fuel previous =>
      simp only [settle]
      split_ifs with fixed
      · exact fixed
      · apply previous
        have decrease := strict_refinement_decreases source pairs fixed
        omega

def kernel : Finset (Pair source) :=
  settle source (initialPairs source).card (initialPairs source)

theorem kernel_fixed : refine source (kernel source) = kernel source :=
  settle_fixed source _ _ (Nat.le_refl _)

theorem kernel_reads {left right : State source} (same : (left, right) ∈ kernel source) :
    sameReads source left right :=
  (mem_initial source left right).1 (settle_subset source _ _ same)

theorem kernel_action {left right : State source} (same : (left, right) ∈ kernel source)
    (letter : Letter source) :
    (source.action letter left, source.action letter right) ∈ kernel source := by
  have refined : (left, right) ∈ refine source (kernel source) := by rw [kernel_fixed]; exact same
  exact ((mem_refine source _ left right).1 refined).2 letter

abbrev execute := WholeRepresentation.runMap source.action

def FutureSame (left right : State source) : Prop :=
  ∀ word : List (Letter source), ∀ reader,
    source.read reader (execute source word left) = source.read reader (execute source word right)

theorem future_reads {left right : State source} (same : FutureSame source left right) :
    sameReads source left right := same []

theorem future_action {left right : State source} (same : FutureSame source left right)
    (letter : Letter source) : FutureSame source (source.action letter left) (source.action letter right) :=
  fun word reader => same (letter :: word) reader

theorem settle_retains_future (fuel : Nat) (pairs : Finset (Pair source))
    (retains : ∀ left right, FutureSame source left right → (left, right) ∈ pairs) :
    ∀ left right, FutureSame source left right → (left, right) ∈ settle source fuel pairs := by
  induction fuel generalizing pairs with
  | zero => exact retains
  | succ fuel previous =>
      simp only [settle]
      split_ifs with fixed
      · exact retains
      · apply previous
        intro left right same
        apply (mem_refine source pairs left right).2
        exact ⟨retains left right same, fun letter => retains _ _ (future_action source same letter)⟩

theorem kernel_future_exact (left right : State source) :
    (left, right) ∈ kernel source ↔ FutureSame source left right := by
  constructor
  · intro same word
    induction word generalizing left right with
    | nil => exact kernel_reads source same
    | cons letter word previous =>
        exact previous _ _ (kernel_action source same letter)
  · exact settle_retains_future source _ _
      (fun left right same => (mem_initial source left right).2 (future_reads source same)) left right

theorem kernel_refl (state : State source) : (state, state) ∈ kernel source :=
  (kernel_future_exact source state state).2 (fun _ _ => rfl)

theorem kernel_symm {left right : State source} (same : (left, right) ∈ kernel source) :
    (right, left) ∈ kernel source :=
  (kernel_future_exact source right left).2
    (fun word reader => ((kernel_future_exact source left right).1 same word reader).symm)

theorem kernel_trans {left middle right : State source}
    (first : (left, middle) ∈ kernel source) (second : (middle, right) ∈ kernel source) :
    (left, right) ∈ kernel source :=
  (kernel_future_exact source left right).2 (fun word reader =>
    ((kernel_future_exact source left middle).1 first word reader).trans
      ((kernel_future_exact source middle right).1 second word reader))

def members (state : State source) : Finset (State source) :=
  Finset.univ.filter fun candidate => (state, candidate) ∈ kernel source

theorem members_nonempty (state : State source) : (members source state).Nonempty :=
  ⟨state, by simp [members, kernel_refl]⟩

/-- Least raw address in the generated class.  It is computed from the
partition and cannot be supplied by a caller as a target normalizer. -/
def code (state : State source) : State source :=
  (members source state).min' (members_nonempty source state)

theorem code_related (state : State source) : (state, code source state) ∈ kernel source := by
  have member := Finset.min'_mem (members source state) (members_nonempty source state)
  exact (Finset.mem_filter.mp member).2

theorem members_eq {left right : State source} (same : (left, right) ∈ kernel source) :
    members source left = members source right := by
  ext candidate
  simp only [members, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun leftSame => kernel_trans source (kernel_symm source same) leftSame
  · exact fun rightSame => kernel_trans source same rightSame

theorem code_kernel (left right : State source) :
    code source left = code source right ↔ (left, right) ∈ kernel source := by
  constructor
  · intro equal
    have first := code_related source left
    rw [equal] at first
    exact kernel_trans source first (kernel_symm source (code_related source right))
  · intro same
    have classes := members_eq source same
    unfold code
    congr 1

theorem code_idempotent (state : State source) : code source (code source state) = code source state :=
  (code_kernel source _ _).2 (kernel_symm source (code_related source state))

abbrev Model := {state : State source // code source state = state}

def encode (state : State source) : Model source := ⟨code source state, code_idempotent source state⟩

def next (letter : Letter source) (state : Model source) : Model source :=
  encode source (source.action letter state.val)

def read (reader : Fin source.readerCount) (state : Model source) : source.Output reader :=
  source.read reader state.val

theorem encode_kernel (left right : State source) :
    encode source left = encode source right ↔ FutureSame source left right := by
  rw [← kernel_future_exact, ← code_kernel]
  exact Subtype.mk_eq_mk

theorem encode_surjective : Function.Surjective (encode source) := by
  intro point
  refine ⟨point.val, ?_⟩
  apply Subtype.ext
  exact point.property

theorem next_commutes (letter : Letter source) (state : State source) :
    next source letter (encode source state) = encode source (source.action letter state) := by
  apply (encode_kernel source _ _).2
  apply (kernel_future_exact source _ _).1
  exact kernel_action source (kernel_symm source (code_related source state)) letter

theorem read_commutes (reader : Fin source.readerCount) (state : State source) :
    read source reader (encode source state) = source.read reader state :=
  (kernel_reads source (kernel_symm source (code_related source state))) reader

def run := WholeRepresentation.runMap (next source)

theorem all_words_commute (word : List (Letter source)) (state : State source) :
    run source word (encode source state) = encode source (execute source word state) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter word previous =>
      change run source word (next source letter (encode source state)) = _
      rw [next_commutes, previous]
      rfl

theorem every_future_reader_commutes (word : List (Letter source))
    (reader : Fin source.readerCount) (state : State source) :
    read source reader (run source word (encode source state)) = source.read reader (execute source word state) := by
  rw [all_words_commute, read_commutes]

/-- Every other autonomous/read-faithful implementation retains this
computed distinction.  Candidate laws constrain the candidate, not source. -/
theorem minimal {Candidate : Type} (represent : State source → Candidate)
    (actions : Letter source → Candidate → Candidate)
    (reads : (reader : Fin source.readerCount) → Candidate → source.Output reader)
    (action_commutes : ∀ letter state, actions letter (represent state) = represent (source.action letter state))
    (read_commutes : ∀ reader state, reads reader (represent state) = source.read reader state) :
    Function.FactorsThrough (encode source) represent := by
  have words (word : List (Letter source)) (state : State source) :
      WholeRepresentation.runMap actions word (represent state) = represent (execute source word state) := by
    induction word generalizing state with
    | nil => rfl
    | cons letter word previous =>
        change WholeRepresentation.runMap actions word (actions letter (represent state)) = _
        rw [action_commutes, previous]
        rfl
  intro left right same
  apply (encode_kernel source left right).2
  intro word reader
  calc
    source.read reader (execute source word left) = reads reader (WholeRepresentation.runMap actions word (represent left)) := by rw [words, read_commutes]
    _ = reads reader (WholeRepresentation.runMap actions word (represent right)) := by rw [same]
    _ = source.read reader (execute source word right) := by rw [words, read_commutes]

theorem every_future_reader_unique_factorization (word : List (Letter source))
    (reader : Fin source.readerCount) :
    ∃! factor : Model source → source.Output reader,
      ∀ state, factor (encode source state) = source.read reader (execute source word state) := by
  refine ⟨fun point => read source reader (run source word point), every_future_reader_commutes source word reader, ?_⟩
  intro candidate commutes
  funext point
  rcases encode_surjective source point with ⟨state, rfl⟩
  rw [commutes, every_future_reader_commutes]

structure AdditionalReadout where
  Output : Type
  outputEq : DecidableEq Output
  read : State source → Output

instance (additional : AdditionalReadout source) : DecidableEq additional.Output := additional.outputEq

/-- New independent source reading is admitted before rebuilding the model.
The raw state/action inventory and autonomous letter remain the same. -/
abbrev adjoin (additional : AdditionalReadout source) : Source where
  stateCount := source.stateCount
  letterCount := source.letterCount
  readerCount := source.readerCount + 1
  Output := Fin.cases additional.Output source.Output
  outputEq := Fin.cases additional.outputEq source.outputEq
  initial := source.initial
  autonomous := source.autonomous
  reader := 0
  action := source.action
  read := Fin.cases additional.read source.read

theorem adjoin_future_kernel (additional : AdditionalReadout source) (left right : State source) :
    FutureSame (adjoin source additional) left right ↔
      FutureSame source left right ∧
        ∀ word : List (Letter source), additional.read (execute source word left) =
          additional.read (execute source word right) := by
  constructor
  · intro same
    refine ⟨fun word reader => same word reader.succ, fun word => same word 0⟩
  · rintro ⟨oldSame, newSame⟩ word reader
    refine Fin.cases ?_ (fun reader => ?_) reader
    · exact newSame word
    · exact oldSame word reader

def refinementInitial (additional : AdditionalReadout source) : Finset (Pair source) :=
  (kernel source).filter fun pair => additional.read pair.1 = additional.read pair.2

/-- The old generated partition is refined incrementally by the new current
signature and all original successors, not just by the new current value. -/
def refinedKernel (additional : AdditionalReadout source) : Finset (Pair source) :=
  settle (adjoin source additional) (refinementInitial source additional).card
    (refinementInitial source additional)

theorem refined_kernel_future_exact (additional : AdditionalReadout source) (left right : State source) :
    (left, right) ∈ refinedKernel source additional ↔
      FutureSame (adjoin source additional) left right := by
  constructor
  · intro same word
    have fixed : refine (adjoin source additional) (refinedKernel source additional) =
        refinedKernel source additional := settle_fixed (adjoin source additional) _
      (refinementInitial source additional) (Nat.le_refl _)
    have currentReads {left right : State source}
        (member : (left, right) ∈ refinedKernel source additional) :
        sameReads (adjoin source additional) left right := by
      have original := settle_subset (adjoin source additional) _ _ member
      rcases Finset.mem_filter.mp original with ⟨oldSame, newSame⟩
      intro reader
      refine Fin.cases ?_ (fun reader => ?_) reader
      · exact newSame
      · exact kernel_reads source oldSame reader
    induction word generalizing left right with
    | nil => exact currentReads same
    | cons letter word previous =>
        have inRefined : (left, right) ∈ refine (adjoin source additional) (refinedKernel source additional) := by
          rw [fixed]
          exact same
        exact previous _ _ (((mem_refine (adjoin source additional) _ left right).1 inRefined).2 letter)
  · apply settle_retains_future (adjoin source additional) _ _
    intro left right same
    have complete := (adjoin_future_kernel source additional left right).1 same
    apply Finset.mem_filter.mpr
    exact ⟨(kernel_future_exact source left right).2 complete.1, complete.2 []⟩

theorem incremental_matches_recomputed_minimum (additional : AdditionalReadout source) :
    refinedKernel source additional = kernel (adjoin source additional) := by
  ext pair
  exact (refined_kernel_future_exact source additional pair.1 pair.2).trans
    (kernel_future_exact (adjoin source additional) pair.1 pair.2).symm

theorem refined_model_future_exact (additional : AdditionalReadout source) (left right : State source) :
    encode (adjoin source additional) left = encode (adjoin source additional) right ↔
      encode source left = encode source right ∧
        ∀ word : List (Letter source), additional.read (execute source word left) =
          additional.read (execute source word right) := by
  rw [encode_kernel (adjoin source additional), adjoin_future_kernel source additional,
    encode_kernel source]

theorem actual_future_escape_separates (additional : AdditionalReadout source)
    (left right : State source) (word : List (Letter source))
    (different : additional.read (execute source word left) ≠ additional.read (execute source word right)) :
    encode (adjoin source additional) left ≠ encode (adjoin source additional) right := by
  intro merged
  exact different (((refined_model_future_exact source additional left right).1 merged).2 word)

/-! Complete raw inventory can be presented directly from the already fixed
process and its operation/read inventories.  These are source presentations,
not a supplied behavioral quotient or an observed-history approximation. -/

open SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

variable {N : WorldRelationNetwork} (process : SourceNativeLivingRootProcess N)
variable {Intervention : Type} (intervention : Intervention → process.State → process.State)
variable (system : IndependentConsumerSystem process.State)
variable {states letters readers : Nat}
variable (stateInventory : ConstructivePresentation (Fin states) process.State)
variable (letterInventory : ConstructivePresentation (Fin letters) (WholeRepresentation.Letter (Intervention := Intervention)))
variable (readerInventory : ConstructivePresentation (Fin readers) system.Consumer)
variable (reader : Fin readers)
variable (readerEq : (consumer : system.Consumer) → DecidableEq (system.Output consumer))

abbrev fromProcess : Source where
  stateCount := states
  letterCount := letters
  readerCount := readers
  Output := fun index => system.Output (readerInventory.forward index)
  outputEq := fun index => readerEq (readerInventory.forward index)
  initial := stateInventory.backward process.initial
  autonomous := letterInventory.backward WholeRepresentation.autonomous
  reader := reader
  action := fun letter state => stateInventory.backward
    (WholeRepresentation.step process intervention (letterInventory.forward letter) (stateInventory.forward state))
  read := fun index state => system.read (readerInventory.forward index) (stateInventory.forward state)

include reader readerEq in
theorem fromProcess_decoded_word (word : List (Fin letters)) (state : Fin states) :
    stateInventory.forward
        (execute (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq) word state) =
      WholeRepresentation.execute process intervention (word.map letterInventory.forward) (stateInventory.forward state) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter word previous =>
      change stateInventory.forward (execute
        (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq) word
        (stateInventory.backward (WholeRepresentation.step process intervention (letterInventory.forward letter)
          (stateInventory.forward state)))) = _
      rw [previous, stateInventory.forward_backward]
      rfl

include reader readerEq in
theorem computed_matches_source_future_model (left right : process.State) :
    encode (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
        (stateInventory.backward left) =
      encode (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
        (stateInventory.backward right) ↔
      WholeRepresentation.modelPoint process intervention system left =
        WholeRepresentation.modelPoint process intervention system right := by
  rw [encode_kernel, WholeRepresentation.model_future_kernel]
  constructor
  · intro same word consumer
    have generated := same (word.map letterInventory.backward) (readerInventory.backward consumer)
    change system.read (readerInventory.forward (readerInventory.backward consumer))
        (stateInventory.forward (execute
          (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
          (word.map letterInventory.backward) (stateInventory.backward left))) =
      system.read (readerInventory.forward (readerInventory.backward consumer))
        (stateInventory.forward (execute
          (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
          (word.map letterInventory.backward) (stateInventory.backward right))) at generated
    rw [fromProcess_decoded_word, fromProcess_decoded_word, stateInventory.forward_backward,
      stateInventory.forward_backward, readerInventory.forward_backward] at generated
    have words : (word.map letterInventory.backward).map letterInventory.forward = word := by
      simp only [List.map_map, Function.comp_def, letterInventory.forward_backward]
      exact List.map_id word
    rw [words] at generated
    exact generated
  · intro same word index
    change system.read (readerInventory.forward index)
        (stateInventory.forward (execute
          (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
          word (stateInventory.backward left))) =
      system.read (readerInventory.forward index)
        (stateInventory.forward (execute
          (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
          word (stateInventory.backward right)))
    rw [fromProcess_decoded_word, fromProcess_decoded_word, stateInventory.forward_backward,
      stateInventory.forward_backward]
    exact same _ _

include reader readerEq in
theorem computed_autonomous_next_is_actual (runtime : LivingRuntimeState process) :
    next (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
        (letterInventory.backward WholeRepresentation.autonomous)
        (encode (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
          (stateInventory.backward runtime.state)) =
      encode (fromProcess process intervention system stateInventory letterInventory readerInventory reader readerEq)
        (stateInventory.backward runtime.tick.next.state) := by
  rw [next_commutes]
  simp only [fromProcess, letterInventory.forward_backward, stateInventory.forward_backward,
    WholeRepresentation.step]
  rfl

set_option linter.defProp false in
def computed_model_and_actual_root_factorizes (runtime : LivingRuntimeState process) :=
  And.intro
    (computed_autonomous_next_is_actual process intervention system stateInventory letterInventory readerInventory reader readerEq runtime)
    (SourceOperationNative.point_factorizes runtime).2

end FiniteMinimalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
