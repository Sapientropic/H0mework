import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Measure.FiniteObserverMeasure

/-!
# Normalized finite observer-kernel fold

This is the occurrence-polymorphic mathematical core of normalized observer
conditioning.  It accepts one neutral finite measure, one existing authority
observer, and one event predicate.  Fibre inventories and both masses are
derived from that exact measure; probability, support, normalization, and
authority reconstruction are never constructor fields.

Source-owned specializations remain responsible for producing the indexed
measure.  In particular, this neutral core does not turn an arbitrary measure
into source authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Probability
namespace Kernel

open Observer Measure

universe uOccurrence uVisible uAuthorityResidual

variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {AuthorityResidual : Type uAuthorityResidual}

noncomputable section

/-! ## Finite-mass helpers -/

private theorem eventFold_mono
    (weightedOccurrences : List (Occurrence × ℚ≥0))
    (left right : Occurrence → Prop)
    [DecidablePred left]
    [DecidablePred right]
    (subset : ∀ occurrence, left occurrence → right occurrence) :
    weightedOccurrences.foldr
        (fun weighted accumulated =>
          if left weighted.1 then weighted.2 + accumulated else accumulated)
        0 ≤
      weightedOccurrences.foldr
        (fun weighted accumulated =>
          if right weighted.1 then weighted.2 + accumulated else accumulated)
        0 := by
  induction weightedOccurrences with
  | nil => rfl
  | cons weighted rest inductionHypothesis =>
      by_cases leftObserved : left weighted.1
      · have rightObserved : right weighted.1 :=
          subset weighted.1 leftObserved
        simp only [List.foldr_cons, leftObserved, rightObserved, if_pos]
        exact add_le_add_right inductionHypothesis weighted.2
      · by_cases rightObserved : right weighted.1
        · simp only [List.foldr_cons, leftObserved, rightObserved,
            if_false, if_pos]
          exact inductionHypothesis.trans (le_add_of_nonneg_left bot_le)
        · simp only [List.foldr_cons, leftObserved, rightObserved, if_false]
          exact inductionHypothesis

private theorem finiteEventMass_mono
    (measure : FiniteObserverMeasure Occurrence)
    (left right : Occurrence → Prop)
    [DecidablePred left]
    [DecidablePred right]
    (subset : ∀ occurrence, left occurrence → right occurrence) :
    measure.eventMass left ≤ measure.eventMass right := by
  unfold FiniteObserverMeasure.eventMass
  exact eventFold_mono measure.weightedOccurrences left right subset

private theorem eventFold_eq_zero_of_weight_zero
    (weightedOccurrences : List (Occurrence × ℚ≥0))
    (event : Occurrence → Prop)
    [DecidablePred event]
    (weightZero : ∀ weighted, weighted ∈ weightedOccurrences →
      event weighted.1 → weighted.2 = 0) :
    weightedOccurrences.foldr
        (fun weighted accumulated =>
          if event weighted.1 then weighted.2 + accumulated else accumulated)
        0 = 0 := by
  induction weightedOccurrences with
  | nil => rfl
  | cons weighted rest inductionHypothesis =>
      have restWeightZero : ∀ next, next ∈ rest →
          event next.1 → next.2 = 0 := by
        intro next membership observed
        exact weightZero next (by simp [membership]) observed
      by_cases observed : event weighted.1
      · simp only [List.foldr_cons, observed, if_pos,
          weightZero weighted (by simp) observed, zero_add]
        exact inductionHypothesis restWeightZero
      · simp only [List.foldr_cons, observed, if_false]
        exact inductionHypothesis restWeightZero

private theorem finiteEventMass_eq_zero_of_filteredTrace_eq_nil
    (measure : FiniteObserverMeasure Occurrence)
    (event : Occurrence → Prop)
    [DecidablePred event]
    (empty : measure.occurrenceTrace.filter event = []) :
    measure.eventMass event = 0 := by
  unfold FiniteObserverMeasure.eventMass
  apply eventFold_eq_zero_of_weight_zero
  intro weighted membership observed
  have occurrenceMembership : weighted.1 ∈ measure.occurrenceTrace :=
    measure.occurrence_mem_of_weighted_mem membership
  have filteredMembership :
      weighted.1 ∈ measure.occurrenceTrace.filter event := by
    simp [occurrenceMembership, observed]
  rw [empty] at filteredMembership
  simp at filteredMembership

/-! ## Zero-choice neutral fold -/

/-- Zero-field normalized fold over one exact finite occurrence measure, one
observer, and one event.  It stores no mass, support, probability,
normalizer, classification, authority verdict, root, or future. -/
inductive NormalizedFiniteObserverKernelFoldAt
    (measure : FiniteObserverMeasure Occurrence)
    (observer : AuthorityObserver Occurrence Visible AuthorityResidual)
    (event : Occurrence → Prop) : Type where
  | private generated

namespace NormalizedFiniteObserverKernelFoldAt

/-- Sole neutral fold constructor.  Source authority, when present, must come
from the producer of the indexed measure rather than from this seal. -/
def generate
    (measure : FiniteObserverMeasure Occurrence)
    (observer : AuthorityObserver Occurrence Visible AuthorityResidual)
    (event : Occurrence → Prop) :
    NormalizedFiniteObserverKernelFoldAt measure observer event :=
  .generated

variable {measure : FiniteObserverMeasure Occurrence}
variable {observer : AuthorityObserver Occurrence Visible AuthorityResidual}
variable {event : Occurrence → Prop}
variable (fold : NormalizedFiniteObserverKernelFoldAt measure observer event)

theorem eq_generate : fold = generate measure observer event := by
  cases fold
  rfl

section ComputableReadouts

variable [DecidableEq Visible]
variable [DecidablePred event]

/-- Exact retained occurrences in one observer fibre. -/
def fibre
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event)
    (visible : Visible) : List Occurrence :=
  measure.occurrenceTrace.filter fun occurrence =>
    observer.forget occurrence = visible

/-- Exact retained event occurrences in the same observer fibre. -/
def eventFibre
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event)
    (visible : Visible) : List Occurrence :=
  measure.occurrenceTrace.filter fun occurrence =>
    observer.forget occurrence = visible ∧ event occurrence

omit [DecidablePred event] in
theorem fibre_sublist_occurrenceTrace (visible : Visible) :
    List.Sublist (fold.fibre visible) measure.occurrenceTrace :=
  List.filter_sublist

theorem eventFibre_sublist_occurrenceTrace (visible : Visible) :
    List.Sublist (fold.eventFibre visible) measure.occurrenceTrace :=
  List.filter_sublist

/-- Conditioning mass is the exact finite event fold for the observer fibre. -/
def fibreMass
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event)
    (visible : Visible) : ℚ≥0 :=
  measure.eventMass fun occurrence => observer.forget occurrence = visible

/-- Event mass is the same fold intersected with the indexed event. -/
def eventMass
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event)
    (visible : Visible) : ℚ≥0 :=
  measure.eventMass fun occurrence =>
    observer.forget occurrence = visible ∧ event occurrence

theorem eventMass_le_fibreMass (visible : Visible) :
    fold.eventMass visible ≤ fold.fibreMass visible := by
  apply finiteEventMass_mono measure
  intro occurrence observed
  exact observed.1

/-- A zero-mass fibre is undefined; otherwise normalization is the unique
event/fibre mass ratio. -/
def readVisible
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event)
    (visible : Visible) : Option ℚ≥0 :=
  if _fold.fibreMass visible = 0 then none
  else some (_fold.eventMass visible / _fold.fibreMass visible)

theorem readVisible_eq_none_iff (visible : Visible) :
    fold.readVisible visible = none ↔ fold.fibreMass visible = 0 := by
  by_cases zeroMass : fold.fibreMass visible = 0 <;>
    simp [readVisible, zeroMass]

theorem readVisible_eq_some_ratio
    {visible : Visible}
    (positive : 0 < fold.fibreMass visible) :
    fold.readVisible visible =
      some (fold.eventMass visible / fold.fibreMass visible) := by
  simp [readVisible, ne_of_gt positive]

theorem positive_event_readVisible_some_positive
    {visible : Visible}
    (positiveEvent : 0 < fold.eventMass visible) :
    ∃ probability : ℚ≥0,
      fold.readVisible visible = some probability ∧ 0 < probability := by
  have positiveFibre : 0 < fold.fibreMass visible :=
    lt_of_lt_of_le positiveEvent (fold.eventMass_le_fibreMass visible)
  refine ⟨fold.eventMass visible / fold.fibreMass visible,
    fold.readVisible_eq_some_ratio positiveFibre, ?_⟩
  exact div_pos positiveEvent positiveFibre

theorem readVisible_probability_le_one
    {visible : Visible}
    {probability : ℚ≥0}
    (readout : fold.readVisible visible = some probability) :
    probability ≤ 1 := by
  unfold readVisible at readout
  split at readout
  · simp at readout
  · rename_i nonzero
    cases readout
    exact (div_le_one₀ (pos_of_ne_zero nonzero)).2
      (fold.eventMass_le_fibreMass visible)

/-- Empty retained occurrence fibres have zero mass and no normalized value. -/
theorem empty_fibre_readVisible_none
    {visible : Visible}
    (empty : fold.fibre visible = []) :
    fold.readVisible visible = none := by
  apply (fold.readVisible_eq_none_iff visible).2
  change measure.eventMass
      (fun occurrence => observer.forget occurrence = visible) = 0
  apply finiteEventMass_eq_zero_of_filteredTrace_eq_nil
  change measure.occurrenceTrace.filter
      (fun occurrence => observer.forget occurrence = visible) = []
  exact empty

omit [DecidablePred event] in
/-- If every weighted entry retained by a fibre has coefficient zero, the
fibre has zero mass.  Occurrences remain in the inventory. -/
theorem fibreMass_eq_zero_of_all_weights_zero
    {visible : Visible}
    (allZero : ∀ weighted, weighted ∈ measure.weightedOccurrences →
      observer.forget weighted.1 = visible → weighted.2 = 0) :
    fold.fibreMass visible = 0 := by
  change measure.eventMass
      (fun occurrence => observer.forget occurrence = visible) = 0
  unfold FiniteObserverMeasure.eventMass
  exact eventFold_eq_zero_of_weight_zero measure.weightedOccurrences
    (fun occurrence => observer.forget occurrence = visible) allZero

/-- A visibly nonempty all-zero fibre remains present but has no probability
readout. -/
theorem nonempty_allZero_fibre_readVisible_none
    {visible : Visible}
    (nonempty : fold.fibre visible ≠ [])
    (allZero : ∀ weighted, weighted ∈ measure.weightedOccurrences →
      observer.forget weighted.1 = visible → weighted.2 = 0) :
    fold.readVisible visible = none ∧ fold.fibre visible ≠ [] :=
  ⟨(fold.readVisible_eq_none_iff visible).2
      (fold.fibreMass_eq_zero_of_all_weights_zero allZero),
    nonempty⟩

/-- Positive conditioning mass and an empty event fibre generate `some 0`. -/
theorem positive_fibre_empty_event_readVisible_some_zero
    {visible : Visible}
    (positiveFibre : 0 < fold.fibreMass visible)
    (emptyEvent : fold.eventFibre visible = []) :
    fold.readVisible visible = some 0 := by
  have eventZero : fold.eventMass visible = 0 := by
    change measure.eventMass
        (fun occurrence => observer.forget occurrence = visible ∧
          event occurrence) = 0
    apply finiteEventMass_eq_zero_of_filteredTrace_eq_nil
    change measure.occurrenceTrace.filter
        (fun occurrence => observer.forget occurrence = visible ∧
          event occurrence) = []
    exact emptyEvent
  rw [fold.readVisible_eq_some_ratio positiveFibre, eventZero]
  simp

/-! ## Visible factorization and hidden-authority no-go -/

def probabilityReadout
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event) :
    OccurrenceReadout Occurrence (Option ℚ≥0) :=
  OccurrenceReadout.ofVisible observer _fold.readVisible

@[simp] theorem probabilityReadout_read (occurrence : Occurrence) :
    fold.probabilityReadout.read occurrence =
      fold.readVisible (observer.forget occurrence) :=
  rfl

def probabilityReadoutFactorization
    (_fold : NormalizedFiniteObserverKernelFoldAt measure observer event) :
    ReadoutFactorization observer _fold.probabilityReadout :=
  ReadoutFactorization.ofVisible observer _fold.readVisible

theorem kernelPair_equivalence
    (pair : AuthorityKernelPair observer) :
    fold.probabilityReadout.read pair.left =
      fold.probabilityReadout.read pair.right := by
  exact congrArg fold.readVisible pair.visible_eq

theorem noAuthorityCompleteProbability
    (pair : AuthorityKernelPair observer) :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt observer fold.probabilityReadout) := by
  rintro ⟨complete⟩
  exact pair.noAuthorityFactorization
    ⟨fold.probabilityReadoutFactorization.toAuthorityFactorization complete⟩

end ComputableReadouts

end NormalizedFiniteObserverKernelFoldAt

end
end Kernel
end Probability
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.Probability.Kernel.NormalizedFiniteObserverKernelFoldAt.readVisible_probability_le_one
#print axioms SaturationMonoid.ProcessGame.Society.Probability.Kernel.NormalizedFiniteObserverKernelFoldAt.empty_fibre_readVisible_none
#print axioms SaturationMonoid.ProcessGame.Society.Probability.Kernel.NormalizedFiniteObserverKernelFoldAt.noAuthorityCompleteProbability
