import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Kernel.ObserverGeometryRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.SourceWitnessRefinement
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Consumer.ObserverConditionedPrediction

/-!
# Source-generated M12 aesthetic observer context

This fixed interface exposes the two M12 observer contexts as source-generated
readout occurrences.  The refined context is not a second caller label: it is
the projection of an honest publication of the exact crossing state.  The
object, observer-kernel, context, alignment, and kernel-lineage readouts below
are computed from the same monthly crossing measure.

No beauty carrier, consumer system, factorization, root, ledger, or successor
is defined here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Beauty
namespace M12

open ProcessGame Society
open ProcessGame.Society.Capacity ProcessGame.Society.Space
open ProcessGame.Society.Observer
open ProcessGame.Society.Probability
open ProcessGame.Society.Probability.Measure
open ProcessGame.Society.Probability.Kernel
open ProcessGame.Society.Probability.Consumer
open ProcessGame.Society.M10OccurrenceCapacityProcessFixture
open ProcessGame.Society.M11GeneratedSocialSpaceCrossingFixture
open ProcessGame.Society.M12GeneratedFlowObserverFixture
open ProcessGame.Society.M12GeneratedFlowMeasureFixture
open ProcessGame.Society.M12ObserverGeometryRegression

noncomputable section

abbrev ExactCrossing :=
  ProcessGame.Society.M12GeneratedFlowObserverFixture.ExactCrossing

abbrev Visible :=
  ProcessGame.Society.M12GeneratedFlowObserverFixture.Visible

/-! ## Fixed source contexts and honest state publication -/

/-- The two fixed observation occurrences already present in M12. -/
inductive SourceGeneratedM12AestheticContextOccurrence where
  | coarse
  | refined
  deriving DecidableEq, Repr

/-- An exact crossing publishes a refinement witness precisely when its
source state is `true`. -/
def AestheticStateWitnessAt (crossing : ExactCrossing) : Type :=
  PLift (crossing.state = true)

/-- Honest publication of the existing source state.  It contains no
probability, classification, occurrence decoder, or authority decoder. -/
def aestheticStatePublication :
    SourceWitnessPublicationAt AestheticStateWitnessAt where
  publicationTag := fun crossing => crossing.state
  publicationTag_eq_true_iff := by
    intro crossing
    constructor
    · intro stateTrue
      exact ⟨⟨stateTrue⟩⟩
    · rintro ⟨⟨stateTrue⟩⟩
      exact stateTrue

/-- The coarse fibre collision removed by publishing the middle crossing's
source state. -/
def coarseMiddleKernelPair : AuthorityKernelPair coarseObserver where
  left := middleCrossing
  right := firstCrossing
  occurrence_ne :=
    SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
      (Ne.symm first_middle_positions_are_distinct)
  visible_eq := rfl
  authority_ne := by decide

theorem middleStateWitness :
    Nonempty (AestheticStateWitnessAt middleCrossing) :=
  ⟨⟨rfl⟩⟩

theorem firstStateWitness_isEmpty :
    IsEmpty (AestheticStateWitnessAt firstCrossing) :=
  ⟨fun witness => by
    have firstStateFalse : firstCrossing.state = false := rfl
    exact (by decide : false ≠ true)
      (firstStateFalse.symm.trans witness.down)⟩

/-- Exact source-witness refinement of the middle/first coarse collision. -/
theorem coarseMiddleKernelRefinement :
    SourceWitnessKernelRefinementAt aestheticStatePublication
      coarseMiddleKernelPair :=
  sourceWitnessKernelRefinement aestheticStatePublication
    coarseMiddleKernelPair middleStateWitness firstStateWitness_isEmpty

abbrev sourceRefinedObserver :
    AuthorityObserver ExactCrossing (SourceWitnessRefinedVisible Visible) Nat :=
  sourceWitnessRefinedObserver coarseObserver aestheticStatePublication

/-- Collapse the redundant coarse coordinate of this fixed source refinement
back to the existing two-valued M12 visible type. -/
def refinedVisibleProjection
    (visible : SourceWitnessRefinedVisible Visible) : Visible :=
  match visible.witnessPublished with
  | false => visible.coarse
  | true => .outside

/-- The published source-state refinement projects pointwise to the existing
M12 fine observer. -/
theorem refinedPublicationProjection_forget_exact
    (crossing : ExactCrossing) :
    refinedVisibleProjection (sourceRefinedObserver.forget crossing) =
      fineObserver.forget crossing := by
  cases state_eq : crossing.state <;>
    simp [refinedVisibleProjection, sourceRefinedObserver,
      sourceWitnessRefinedObserver, aestheticStatePublication,
      coarseObserver, fineObserver, state_eq]

theorem refinedPublicationProjection_authority_exact
    (crossing : ExactCrossing) :
    sourceRefinedObserver.authorityK crossing =
      fineObserver.authorityK crossing :=
  rfl

theorem refinedPublication_separates_middle_first :
    sourceRefinedObserver.forget middleCrossing ≠
      sourceRefinedObserver.forget firstCrossing :=
  coarseMiddleKernelRefinement.refinedVisible_ne

/-! ## Shared context-indexed runtime -/

def observerAt : SourceGeneratedM12AestheticContextOccurrence →
    AuthorityObserver ExactCrossing Visible Nat
  | .coarse => coarseObserver
  | .refined => fineObserver

def foldAt (context : SourceGeneratedM12AestheticContextOccurrence) :
    SourceGeneratedObserverKernelFoldAt monthlyMeasure
      (observerAt context) firstOccurrenceEvent :=
  match context with
  | .coarse => coarseMonthlyFold
  | .refined => fineMonthlyFold

/-- The first/recurrent hidden authority pair survives both contexts. -/
def persistentHiddenKernelPairAt
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    AuthorityKernelPair (observerAt context) :=
  match context with
  | .coarse => coarseKernelPair
  | .refined => fineKernelPair

@[simp] theorem persistentHiddenKernelPairAt_left
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    (persistentHiddenKernelPairAt context).left = firstCrossing := by
  cases context <;> rfl

@[simp] theorem persistentHiddenKernelPairAt_right
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    (persistentHiddenKernelPairAt context).right = recurrentCrossing := by
  cases context <;> rfl

theorem persistentHiddenKernelPair_probability_equal
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    (foldAt context).probabilityReadout.read
        (persistentHiddenKernelPairAt context).left =
      (foldAt context).probabilityReadout.read
        (persistentHiddenKernelPairAt context).right :=
  (foldAt context).kernelPair_equivalence
    (persistentHiddenKernelPairAt context)

/-! ## Five independent source readout coordinates -/

structure M12AestheticObjectReadout : Type where
  weightedTrace : List (ExactCrossing × ℚ≥0)
  eventFibre : List ExactCrossing
  eventMass : ℚ≥0

structure M12AestheticObserverKernelReadout : Type where
  fibre : List ExactCrossing
  fibreMass : ℚ≥0

structure M12AestheticContextReadout : Type where
  stateVisibleTrace : List (Bool × Visible)

structure M12AestheticAlignmentReadout : Type where
  probability : Option ℚ≥0
  phase : Option ObserverConditionedPredictionClass

structure M12AestheticKernelLineageReadout : Type where
  occurrenceVisibleTrace : List (ExactCrossing × Visible)

def sourceObjectRead
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    M12AestheticObjectReadout where
  weightedTrace := monthlyMeasure.measure.weightedOccurrences
  eventFibre := (foldAt context).eventFibre .conditioned
  eventMass := (foldAt context).eventMass .conditioned

def sourceObserverKernelRead
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    M12AestheticObserverKernelReadout where
  fibre := (foldAt context).fibre .conditioned
  fibreMass := (foldAt context).fibreMass .conditioned

def sourceContextRead
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    M12AestheticContextReadout where
  stateVisibleTrace := monthlyMeasure.measure.occurrenceTrace.map
    (fun crossing => (crossing.state, (observerAt context).forget crossing))

def sourceAlignmentRead
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    M12AestheticAlignmentReadout where
  probability := (foldAt context).readVisible .conditioned
  phase := ObserverConditionedPredictionClass.ofReadout
    ((foldAt context).readVisible .conditioned)

def sourceKernelLineageRead
    (context : SourceGeneratedM12AestheticContextOccurrence) :
    M12AestheticKernelLineageReadout where
  occurrenceVisibleTrace := monthlyMeasure.measure.occurrenceTrace.map
    (fun crossing => (crossing, (observerAt context).forget crossing))

/-! ## Exact fixed-source readouts -/

@[simp] theorem sourceObjectRead_coarse_eventFibre :
    (sourceObjectRead .coarse).eventFibre = [firstCrossing] :=
  coarse_event_fibre

@[simp] theorem sourceObjectRead_refined_eventFibre :
    (sourceObjectRead .refined).eventFibre = [firstCrossing] :=
  fine_event_fibre

@[simp] theorem sourceObjectRead_coarse_eventMass :
    (sourceObjectRead .coarse).eventMass = 8754 :=
  coarse_eventMass

@[simp] theorem sourceObjectRead_refined_eventMass :
    (sourceObjectRead .refined).eventMass = 8754 :=
  fine_eventMass

theorem sourceObjectRead_event_preserved :
    (sourceObjectRead .coarse).eventFibre =
        (sourceObjectRead .refined).eventFibre ∧
      (sourceObjectRead .coarse).eventMass =
        (sourceObjectRead .refined).eventMass ∧
      (sourceObjectRead .coarse).eventMass = 8754 :=
  ⟨by rw [sourceObjectRead_coarse_eventFibre,
      sourceObjectRead_refined_eventFibre],
    by rw [sourceObjectRead_coarse_eventMass,
      sourceObjectRead_refined_eventMass],
    sourceObjectRead_coarse_eventMass⟩

@[simp] theorem sourceObserverKernelRead_coarse_fibre :
    (sourceObserverKernelRead .coarse).fibre =
      [firstCrossing, middleCrossing, recurrentCrossing] :=
  coarse_conditioned_fibre

@[simp] theorem sourceObserverKernelRead_refined_fibre :
    (sourceObserverKernelRead .refined).fibre =
      [firstCrossing, recurrentCrossing] :=
  fine_conditioned_fibre

@[simp] theorem sourceObserverKernelRead_coarse_mass :
    (sourceObserverKernelRead .coarse).fibreMass = 20581 :=
  coarse_fibreMass

@[simp] theorem sourceObserverKernelRead_refined_mass :
    (sourceObserverKernelRead .refined).fibreMass = 11511 :=
  fine_fibreMass

/-- Refinement removes exactly the middle non-event occurrence and its source
mass `9070`, while retaining the event occurrence and recurrent tail. -/
theorem refinement_removes_middle_mass_exact :
    (sourceObserverKernelRead .coarse).fibre =
        [firstCrossing, middleCrossing, recurrentCrossing] ∧
      (sourceObserverKernelRead .refined).fibre =
        [firstCrossing, recurrentCrossing] ∧
      monthlyMeasure.coefficient middleCrossing = 9070 ∧
      (sourceObserverKernelRead .coarse).fibreMass =
        (sourceObserverKernelRead .refined).fibreMass + 9070 := by
  refine ⟨sourceObserverKernelRead_coarse_fibre,
    sourceObserverKernelRead_refined_fibre, monthly_middle_weight, ?_⟩
  rw [sourceObserverKernelRead_coarse_mass,
    sourceObserverKernelRead_refined_mass]
  norm_num

@[simp] theorem sourceContextRead_coarse_exact :
    (sourceContextRead .coarse).stateVisibleTrace =
      [(false, .conditioned), (true, .conditioned),
        (false, .conditioned)] := by
  rfl

@[simp] theorem sourceContextRead_refined_exact :
    (sourceContextRead .refined).stateVisibleTrace =
      [(false, .conditioned), (true, .outside),
        (false, .conditioned)] := by
  rfl

@[simp] theorem sourceKernelLineageRead_coarse_exact :
    (sourceKernelLineageRead .coarse).occurrenceVisibleTrace =
      [(firstCrossing, .conditioned),
        (middleCrossing, .conditioned),
        (recurrentCrossing, .conditioned)] := by
  rfl

@[simp] theorem sourceKernelLineageRead_refined_exact :
    (sourceKernelLineageRead .refined).occurrenceVisibleTrace =
      [(firstCrossing, .conditioned),
        (middleCrossing, .outside),
        (recurrentCrossing, .conditioned)] := by
  rfl

@[simp] theorem sourceAlignmentRead_coarse_probability :
    (sourceAlignmentRead .coarse).probability =
      some ((8754 : ℚ≥0) / 20581) :=
  coarse_readVisible_exact

@[simp] theorem sourceAlignmentRead_refined_probability :
    (sourceAlignmentRead .refined).probability =
      some ((8754 : ℚ≥0) / 11511) :=
  fine_readVisible_exact

@[simp] theorem sourceAlignmentRead_coarse_phase :
    (sourceAlignmentRead .coarse).phase =
      some ObserverConditionedPredictionClass.belowHalf := by
  apply (ObserverConditionedPredictionClass.ofReadout_eq_some_belowHalf_iff
    ((foldAt .coarse).readVisible .conditioned)).2
  exact ⟨(8754 : ℚ≥0) / 20581, coarse_readVisible_exact,
    by simpa [ObserverConditionedPredictionClass.half] using
      coarse_probability_below_half⟩

@[simp] theorem sourceAlignmentRead_refined_phase :
    (sourceAlignmentRead .refined).phase =
      some ObserverConditionedPredictionClass.aboveHalf := by
  apply (ObserverConditionedPredictionClass.ofReadout_eq_some_aboveHalf_iff
    ((foldAt .refined).readVisible .conditioned)).2
  exact ⟨(8754 : ℚ≥0) / 11511, fine_readVisible_exact,
    by simpa [ObserverConditionedPredictionClass.half] using
      fine_probability_above_half⟩

/-- Same object event and source measure, opposite alignment phases, generated
solely by the source-state observer refinement. -/
theorem sourceAlignment_phaseFlip :
    (sourceObjectRead .coarse).eventMass =
        (sourceObjectRead .refined).eventMass ∧
      (sourceAlignmentRead .coarse).phase =
        some ObserverConditionedPredictionClass.belowHalf ∧
      (sourceAlignmentRead .refined).phase =
        some ObserverConditionedPredictionClass.aboveHalf :=
  ⟨sourceObjectRead_event_preserved.2.1,
    sourceAlignmentRead_coarse_phase,
    sourceAlignmentRead_refined_phase⟩

end
end M12
end Beauty
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.coarseMiddleKernelRefinement
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.refinedPublicationProjection_forget_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.refinement_removes_middle_mass_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.sourceAlignment_phaseFlip
