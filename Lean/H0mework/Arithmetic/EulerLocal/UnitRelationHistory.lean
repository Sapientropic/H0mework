import H0mework.Arithmetic.EulerLocal.FiniteEnvelope
import H0mework.Realization.Completion.UnitPrimeClosure
import H0mework.Realization.Completion.HistorySettlement
import H0mework.Realization.GlobalSections.KernelIncidenceRigidity

/-!
# Source-generated unit-normalized arithmetic relation history

Every actual quotient history is generated from the same unit occurrence.
Its additive fold is therefore its cardinality multiple of one shared
`quotientUnit` generator; it is not a fresh generator indexed by `(p,k)`.

This file builds the cofinal relation history directly on that fixed finite
generator carrier.  It does not first construct the provisional completion
with independent quotient roots and then collapse it.  Each row is still
rooted in its exact runtime factorization occurrence, while the generic
history engine owns iteration, accumulated relations and the completion.

The resulting completion is finitely generated because the source generator
type is finite.  Canonical quotient evaluation and frozen prime-power
rigidity then eliminate the shared anti-invariant component.  No FG premise,
completed relation table, division-root family, fixedness or determinant is
accepted from a caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticUnitNormalizedRelationHistory

open CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure

noncomputable section

abbrev EnvelopeGenerator :=
  CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.Generator

/-- `none` is a fixed bookkeeping generator used only to carry the source
cursor through the unfolding frontier.  Arithmetic generators are `some`.
The generator type remains finite. -/
abbrev Generator := Option EnvelopeGenerator
abbrev Lattice := Generator →₀ ℤ
abbrev Event := PresentedRelationEventAt Generator

def liftEnvelope :
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.Lattice →ₗ[ℤ]
      Lattice :=
  Finsupp.lmapDomain ℤ ℤ some

@[simp] theorem liftEnvelope_apply_some
    (value : CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.Lattice)
    (generator : EnvelopeGenerator) :
    liftEnvelope value (some generator) = value generator := by
  rw [liftEnvelope, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_apply (Option.some_injective EnvelopeGenerator)]

@[simp] theorem liftEnvelope_apply_none
    (value : CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.Lattice) :
    liftEnvelope value none = 0 := by
  rw [liftEnvelope, Finsupp.lmapDomain_apply]
  apply Finsupp.mapDomain_of_notMem_range
  simp

@[simp] theorem liftEnvelope_basis
    (role : EnvelopeRole) (dualIndex : Fin 2) :
    liftEnvelope (basis role dualIndex) =
      Finsupp.single (some (role, dualIndex)) 1 := by
  rw [liftEnvelope, Finsupp.lmapDomain_apply,
    basis, Finsupp.mapDomain_single]

def localRelation (cursor : Nat) : Lattice :=
  liftEnvelope (relation (scheduledFactor cursor))

def relationRowEvent (cursor : Nat) : Event :=
  .relation (localRelation cursor)

def clockMarker (cursor : Nat) : Lattice :=
  Finsupp.single none (cursor + 1 : ℤ)

def clockMarkerEvent (cursor : Nat) : Event :=
  .relation (clockMarker cursor)

/-- The actual unit-normalized row retains both the exact factorization
authority and its generated relation event before either projection. -/
def certifiedRelationRowOccurrence (cursor : Nat) :
    RootedAccountedUnfolding
      (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.FactorizationRoot ×
        Event) :=
  (relationOccurrence (scheduledFactor cursor)).map fun payload =>
    (payload.1,
      PresentedRelationEventAt.relation (liftEnvelope payload.2))

def relationRowOccurrence (cursor : Nat) :
    RootedAccountedUnfolding Event :=
  (certifiedRelationRowOccurrence cursor).map Prod.snd

theorem certifiedRelationRowOccurrence_projects_to_factorization
    (cursor : Nat) :
    (certifiedRelationRowOccurrence cursor).map Prod.fst =
      CanonicalUnitArithmeticFactorizationOccurrence.factorizationOccurrence
        (scheduledFactor cursor).stage := by
  rw [certifiedRelationRowOccurrence,
    RootedAccountedUnfolding.map_map]
  exact relationOccurrence_projects_to_factorization
    (scheduledFactor cursor)

theorem certifiedRelationRowOccurrence_projects_to_event
    (cursor : Nat) :
    (certifiedRelationRowOccurrence cursor).map Prod.snd =
      relationRowOccurrence cursor :=
  rfl

theorem relationRowOccurrence_root (cursor : Nat) :
    (relationRowOccurrence cursor).root = relationRowEvent cursor :=
  rfl

def rowPatch (cursor : Nat) : RootedAccountedUnfolding Event :=
  (relationRowOccurrence cursor).advance fun _event =>
    RootedAccountedUnfolding.zero (clockMarkerEvent cursor)

@[simp] theorem relationRowOccurrence_frontier (cursor : Nat) :
    (relationRowOccurrence cursor).frontier = [relationRowEvent cursor] :=
  rfl

@[simp] theorem rowPatch_frontier (cursor : Nat) :
    (rowPatch cursor).frontier = [clockMarkerEvent cursor] := by
  rw [rowPatch, RootedAccountedUnfolding.frontier_advance,
    relationRowOccurrence_frontier]
  rfl

@[simp] theorem rowPatch_root (cursor : Nat) :
    (rowPatch cursor).root = relationRowEvent cursor := by
  rw [rowPatch]
  exact relationRowOccurrence_root cursor

def decodedCursor : Event → Nat
  | .generator _ => 0
  | .relation value => (value none).natAbs - 1

@[simp] theorem decodedCursor_clockMarkerEvent (cursor : Nat) :
    decodedCursor (clockMarkerEvent cursor) = cursor := by
  simp only [clockMarkerEvent, decodedCursor, clockMarker,
    Finsupp.single_eq_same]
  rw [show (cursor : ℤ) + 1 = (cursor + 1 : Nat) by omega]
  rw [Int.natAbs_natCast]
  omega

def nextPatch (event : Event) : RootedAccountedUnfolding Event :=
  rowPatch (decodedCursor event + 1)

@[simp] theorem nextPatch_clockMarkerEvent (cursor : Nat) :
    nextPatch (clockMarkerEvent cursor) = rowPatch (cursor + 1) := by
  rw [nextPatch, decodedCursor_clockMarkerEvent]

abbrev FactorizationRoot :=
  RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure.FactorizationRoot

def rootOccurrence : RootedAccountedUnfolding FactorizationRoot :=
  CanonicalUnitArithmeticFactorizationOccurrence.factorizationOccurrence 0

def seedEventOccurrence : RootedAccountedUnfolding Event :=
  rowPatch 0

def continuationOccurrence : RootedAccountedUnfolding
    (Event → RootedAccountedUnfolding Event) :=
  rootOccurrence.map fun _root => nextPatch

def history : RootGeneratedCofinalHistoryAt rootOccurrence
    seedEventOccurrence continuationOccurrence :=
  RootGeneratedCofinalHistoryAt.generate

/-- The framework-generated observation carries exactly one current clock
leaf; no completed `Nat → Event` table enters the source. -/
theorem observation_frontier (stage : Nat) :
    (history.observation stage).frontier = [clockMarkerEvent stage] := by
  induction stage with
  | zero => exact rowPatch_frontier 0
  | succ stage inductionHypothesis =>
      rw [history.observation_succ,
        RootedAccountedUnfolding.frontier_advance,
        inductionHypothesis]
      change (nextPatch (clockMarkerEvent stage)).frontier =
        [clockMarkerEvent (stage + 1)]
      rw [nextPatch_clockMarkerEvent, rowPatch_frontier]

private theorem next_trace_mem_trace_advance
    (next : Event → RootedAccountedUnfolding Event)
    (occurrence : RootedAccountedUnfolding Event) :
    ∀ leaf, leaf ∈ occurrence.frontier →
      ∀ event, event ∈ (next leaf).trace →
        event ∈ (occurrence.advance next).trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ leaf, leaf ∈ current.frontier →
        ∀ event, event ∈ (next leaf).trace →
          event ∈ (current.advance next).trace)
    (motive_2 := fun branches =>
      ∀ leaf,
        leaf ∈ RootedAccountedUnfolding.frontierBranches branches →
        ∀ event, event ∈ (next leaf).trace →
          event ∈ RootedAccountedUnfolding.traceBranches
            (RootedAccountedUnfolding.advanceBranches next branches))
    (fun root branches branchResult leaf leaf_mem event event_mem => by
      cases branches with
      | nil =>
          change leaf ∈ [root] at leaf_mem
          have leaf_eq : leaf = root := by simpa using leaf_mem
          subst leaf
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.nil : AccountedBranches Event)).advance next =
                RootedAccountedUnfolding.occur root
                  (AccountedBranches.singleton (next root)) from rfl]
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.singleton (next root))).trace =
                root :: (next root).trace by
            simp [RootedAccountedUnfolding.trace,
              AccountedBranches.singleton]]
          exact List.mem_cons_of_mem root event_mem
      | cons head tail =>
          exact List.mem_cons_of_mem root
            (branchResult leaf leaf_mem event event_mem))
    (fun leaf leaf_mem event event_mem => by
      change leaf ∈ ([] : List Event) at leaf_mem
      exact False.elim (List.not_mem_nil leaf_mem))
    (fun head tail headResult tailResult leaf leaf_mem event event_mem => by
      change leaf ∈ head.frontier ++
        RootedAccountedUnfolding.frontierBranches tail at leaf_mem
      change event ∈ (head.advance next).trace ++
        RootedAccountedUnfolding.traceBranches
          (RootedAccountedUnfolding.advanceBranches next tail)
      rw [List.mem_append] at leaf_mem ⊢
      cases leaf_mem with
      | inl inHead => exact Or.inl (headResult leaf inHead event event_mem)
      | inr inTail => exact Or.inr (tailResult leaf inTail event event_mem))
    occurrence

theorem relationRowEvent_mem_observation_trace (cursor : Nat) :
    relationRowEvent cursor ∈ (history.observation cursor).trace := by
  induction cursor with
  | zero =>
      have rootMem := RootedAccountedUnfolding.root_mem_trace
        (history.observation 0)
      rw [show (history.observation 0).root = relationRowEvent 0 from rfl]
        at rootMem
      exact rootMem
  | succ cursor inductionHypothesis =>
      rw [history.observation_succ]
      apply next_trace_mem_trace_advance
        (next := history.actualContinuation)
        (leaf := clockMarkerEvent cursor)
      · rw [observation_frontier]
        simp
      · change relationRowEvent (cursor + 1) ∈
          (nextPatch (clockMarkerEvent cursor)).trace
        rw [nextPatch_clockMarkerEvent]
        have rootMem := RootedAccountedUnfolding.root_mem_trace
          (rowPatch (cursor + 1))
        simpa [rowPatch_root] using rootMem

theorem relationRowEvent_mem_observedEvents (cursor : Nat) :
    relationRowEvent cursor ∈ history.observedEvents cursor := by
  rw [RootGeneratedCofinalHistoryAt.observedEvents, List.mem_flatMap]
  exact ⟨cursor, by simp, relationRowEvent_mem_observation_trace cursor⟩

@[simp] theorem rowPatch_trace (cursor : Nat) :
    (rowPatch cursor).trace =
      [relationRowEvent cursor, clockMarkerEvent cursor] :=
  rfl

theorem clockMarkerEvent_mem_observedEvents_zero :
    clockMarkerEvent 0 ∈ history.observedEvents 0 := by
  rw [RootGeneratedCofinalHistoryAt.observedEvents]
  simp only [List.range_succ, List.range_zero, Nat.reduceAdd]
  change clockMarkerEvent 0 ∈ (rowPatch 0).trace
  rw [rowPatch_trace]
  simp

theorem localRelation_mem_relationStage (cursor : Nat) :
    localRelation cursor ∈ history.relationStage cursor := by
  apply Submodule.subset_span
  exact relationRowEvent_mem_observedEvents cursor

theorem localRelation_mem_relationClosure (cursor : Nat) :
    localRelation cursor ∈ history.relationClosure :=
  history.relationStage_le_closure cursor
    (localRelation_mem_relationStage cursor)

theorem event_support_subset_generatorSupport
    {stage : Nat} {event : Event}
    (event_mem : event ∈ history.observedEvents stage) :
    (event.support : Set Generator) ⊆ history.generatorSupport stage := by
  classical
  intro generator generator_mem
  rw [RootGeneratedCofinalHistoryAt.generatorSupport]
  have inFinset : generator ∈
      ((history.observedEvents stage).flatMap
        (fun current => current.support.toList)).toFinset := by
    rw [List.mem_toFinset, List.mem_flatMap]
    exact ⟨event, event_mem, by simpa using generator_mem⟩
  simpa using inFinset

theorem clock_mem_generatorSupport_zero :
    (none : Generator) ∈ history.generatorSupport 0 := by
  apply event_support_subset_generatorSupport
    clockMarkerEvent_mem_observedEvents_zero
  change none ∈ (clockMarker 0).support
  rw [Finsupp.mem_support_iff]
  simp [clockMarker]

theorem wholeUnitCoefficient_positive
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : CanonicalUnitArithmeticFactorizationOccurrence.RuntimePrimePowerFactorAt
      requestedPrime requestedExponent) :
    0 < wholeUnitCoefficient factor := by
  unfold wholeUnitCoefficient
  rw [CanonicalUnitArithmeticFactorizationOccurrence.factorialHistory_cardinalShadow]
  exact Nat.factorial_pos _

theorem envelopeGenerator_mem_generatorSupport
    (cursor : Nat) (role : EnvelopeRole) (dualIndex : Fin 2) :
    some (role, dualIndex) ∈ history.generatorSupport cursor := by
  apply event_support_subset_generatorSupport
    (relationRowEvent_mem_observedEvents cursor)
  change some (role, dualIndex) ∈ (localRelation cursor).support
  rw [Finsupp.mem_support_iff]
  unfold localRelation
  rw [liftEnvelope_apply_some]
  rw [relation_eq_wholeCoefficient_normalForm]
  have coefficientNe :
      wholeUnitCoefficient (scheduledFactor cursor) ≠ 0 :=
    Nat.ne_of_gt (wholeUnitCoefficient_positive (scheduledFactor cursor))
  cases role <;> fin_cases dualIndex <;>
    simp [
      CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference,
      CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference,
      basis, coefficientNe]

theorem everyGenerator_mem_generatorSupport_zero (generator : Generator) :
    generator ∈ history.generatorSupport 0 := by
  cases generator with
  | none => exact clock_mem_generatorSupport_zero
  | some generator =>
      rcases generator with ⟨role, dualIndex⟩
      exact envelopeGenerator_mem_generatorSupport 0 role dualIndex

theorem generatorSupport_zero_eq_univ :
    history.generatorSupport 0 = Finset.univ := by
  apply Finset.eq_univ_of_forall
  exact everyGenerator_mem_generatorSupport_zero

theorem generatorStage_zero_eq_top :
    history.generatorStage 0 = ⊤ := by
  unfold RootGeneratedCofinalHistoryAt.generatorStage
  rw [generatorSupport_zero_eq_univ]
  ext value
  simp

theorem generatorClosure_eq_top : history.generatorClosure = ⊤ := by
  apply top_unique
  rw [← generatorStage_zero_eq_top]
  exact history.generatorStage_le_closure 0

theorem stageGeneratorToCompletion_zero_surjective :
    Function.Surjective (history.stageGeneratorToCompletion 0) := by
  intro value
  obtain ⟨representative, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      history.relationInGeneratorClosure value
  let stageRepresentative : history.generatorStage 0 :=
    ⟨representative.1, by
      rw [generatorStage_zero_eq_top]
      exact Submodule.mem_top⟩
  exact ⟨stageRepresentative, rfl⟩

theorem compactAt_zero : history.CompactAt 0 := by
  rw [history.compactAt_iff_presentedEpi,
    ← history.stageGeneratorToCompletion_surjective_iff_presentedEpi]
  exact stageGeneratorToCompletion_zero_surjective

noncomputable def compactPerfectPackage :
    Σ trace : GeneratedHistoricalCompactnessAt history,
      GeneratedCompactPerfectReadoutAt history trace :=
  Classical.choice <| history.compactPerfectReadout_exists
    ⟨0, compactAt_zero⟩

noncomputable def compactTrace :
    GeneratedHistoricalCompactnessAt history :=
  compactPerfectPackage.1

noncomputable def compactPerfectReadout :
    GeneratedCompactPerfectReadoutAt history compactTrace :=
  compactPerfectPackage.2

def perfectComplex := compactPerfectReadout.perfectComplex

def determinantProjection := compactPerfectReadout.determinantProjection

theorem perfectCalculation :
    PerfectComplexDeterminantProjection.RootGeneratedFourTermPerfectCalculationAt
      determinantProjection :=
  compactPerfectReadout.perfectCalculation

def determinantState := compactPerfectReadout.determinantState

abbrev IntegralLine := determinantState.integralLine

noncomputable def unitTorsor := determinantState.unitTorsor

theorem cofinalHistory_generates_perfect_determinant_unit :
    Nonempty
        ((history.generatorStage compactTrace.index ⧸
          LinearMap.ker
            (history.stageGeneratorToCompletion compactTrace.index)) ≃ₗ[ℤ]
          history.CompletionCarrier) ∧
      Nonempty
        (GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
          IntegralLine) :=
  ⟨⟨compactPerfectReadout.degreeOneHomologyEquiv⟩,
    ⟨unitTorsor⟩⟩

def embeddedComponentDifference : Lattice :=
  liftEnvelope
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference

def embeddedQuotientUnitDifference : Lattice :=
  liftEnvelope
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference

def componentDifferenceStage (cursor : Nat) :
    history.generatorStage cursor := by
  refine ⟨embeddedComponentDifference, ?_⟩
  unfold embeddedComponentDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference
  rw [map_sub, liftEnvelope_basis, liftEnvelope_basis]
  apply Submodule.sub_mem
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (envelopeGenerator_mem_generatorSupport cursor .component 0)
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (envelopeGenerator_mem_generatorSupport cursor .component 1)

def quotientUnitDifferenceStage (cursor : Nat) :
    history.generatorStage cursor := by
  refine ⟨embeddedQuotientUnitDifference, ?_⟩
  unfold embeddedQuotientUnitDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference
  rw [map_sub, liftEnvelope_basis, liftEnvelope_basis]
  apply Submodule.sub_mem
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (envelopeGenerator_mem_generatorSupport cursor .quotientUnit 0)
  · exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
      (envelopeGenerator_mem_generatorSupport cursor .quotientUnit 1)

def componentAt (cursor : Nat) : history.CompletionCarrier :=
  history.stageGeneratorToCompletion cursor (componentDifferenceStage cursor)

def globalComponent : history.CompletionCarrier :=
  componentAt 0

theorem componentAt_eq_global (cursor : Nat) :
    componentAt cursor = globalComponent := by
  unfold componentAt globalComponent
    RootGeneratedCofinalHistoryAt.stageGeneratorToCompletion
    RootGeneratedCofinalHistoryAt.completionProjection
    RootGeneratedCofinalHistoryAt.stageGeneratorToClosure
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rfl

def quotientUnitRootAt (cursor : Nat) : history.CompletionCarrier :=
  quotientUnitCoefficient (scheduledFactor cursor) •
    history.stageGeneratorToCompletion cursor
      (quotientUnitDifferenceStage cursor)

def localRelationInGeneratorStage (cursor : Nat) :
    history.relationInGeneratorStage cursor :=
  ⟨⟨localRelation cursor,
      history.relationStage_le_generatorStage cursor
        (localRelation_mem_relationStage cursor)⟩,
    localRelation_mem_relationStage cursor⟩

theorem localRelation_mapsToZero (cursor : Nat) :
    history.stageGeneratorToCompletion cursor
        (localRelationInGeneratorStage cursor).1 = 0 :=
  LinearMap.mem_ker.mp
    (history.stageRelationInGenerator_le_kernel cursor
      (localRelationInGeneratorStage cursor).2)

theorem localRelation_normalForm (cursor : Nat) :
    localRelation cursor = embeddedComponentDifference -
      ((scheduledPrime cursor : Nat) ^ scheduledExponent cursor) •
        (quotientUnitCoefficient (scheduledFactor cursor) •
          embeddedQuotientUnitDifference) := by
  unfold localRelation embeddedComponentDifference
    embeddedQuotientUnitDifference
  change liftEnvelope
      (CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference -
        (((scheduledPrime cursor : Nat) ^ scheduledExponent cursor) *
          quotientUnitCoefficient (scheduledFactor cursor)) •
            CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference) = _
  rw [map_sub, map_nsmul]
  module

theorem localRelationStage_normalForm (cursor : Nat) :
    (localRelationInGeneratorStage cursor).1 =
      componentDifferenceStage cursor -
        ((scheduledPrime cursor : Nat) ^ scheduledExponent cursor) •
          (quotientUnitCoefficient (scheduledFactor cursor) •
            quotientUnitDifferenceStage cursor) := by
  apply Subtype.ext
  exact localRelation_normalForm cursor

theorem scheduled_primePower_landing (cursor : Nat) :
    (scheduledPrime cursor : Nat) ^ scheduledExponent cursor •
        quotientUnitRootAt cursor = globalComponent := by
  have relationZero := localRelation_mapsToZero cursor
  rw [localRelationStage_normalForm, map_sub, map_nsmul,
    map_nsmul] at relationZero
  change componentAt cursor -
    ((scheduledPrime cursor : Nat) ^ scheduledExponent cursor) •
      quotientUnitRootAt cursor = 0 at relationZero
  rw [sub_eq_zero, componentAt_eq_global] at relationZero
  exact relationZero.symm

def requestedRoot (prime : Nat.Primes) (exponent : Nat) :
    history.CompletionCarrier :=
  quotientUnitRootAt (scheduleIndex prime exponent)

theorem requested_primePower_landing
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (prime : Nat) ^ exponent • requestedRoot prime exponent =
      globalComponent := by
  unfold requestedRoot
  have landing := scheduled_primePower_landing
    (scheduleIndex prime exponent)
  simpa only [scheduledPrime_scheduleIndex,
    scheduledExponent_scheduleIndex prime exponent positive] using landing

/-- FG is generated from the fixed finite source generator presentation;
it is not a global caller premise. -/
theorem completionFiniteGenerated :
    AddGroup.FG history.CompletionCarrier := by
  letI : Module.Finite ℤ (Generator →₀ ℤ) := inferInstance
  letI : Module.Finite ℤ history.generatorClosure :=
    Module.Finite.of_fg
      (Submodule.FG.of_le Module.Finite.fg_top le_top)
  letI : Module.Finite ℤ history.CompletionCarrier :=
    Module.Finite.quotient ℤ history.relationInGeneratorClosure
  exact Module.Finite.iff_addGroup_fg.mp inferInstance

def quotientFace : RootGeneratedPrimePowerQuotientEvaluationAt
    history.CompletionCarrier history.root completionFiniteGenerated :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate
    history.CompletionCarrier

def quotientEvaluator : history.CompletionCarrier →
    PrimePowerQuotientEvaluation.State history.CompletionCarrier :=
  quotientFace.accountedEvaluator

theorem globalComponent_quotientZero
    (prime : Nat.Primes) (exponent : Nat) :
    quotientEvaluator globalComponent prime exponent = 0 := by
  unfold quotientEvaluator
  rw [quotientFace.accountedEvaluator_eq_canonical]
  apply (QuotientAddGroup.eq_zero_iff globalComponent).2
  cases exponent with
  | zero => exact ⟨globalComponent, by simp⟩
  | succ exponent =>
      exact ⟨requestedRoot prime (exponent + 1),
        requested_primePower_landing prime (exponent + 1) (by omega)⟩

theorem globalComponent_evaluatorZero :
    quotientEvaluator globalComponent = 0 := by
  funext prime exponent
  exact globalComponent_quotientZero prime exponent

def rigidityFace : RootGeneratedPrimePowerKernelIncidenceRigidityAt
    quotientFace.dependentOccurrence :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem globalComponent_eq_zero : globalComponent = 0 := by
  apply rigidityFace.evaluator_eq_zero_implies_element_zero globalComponent
  change quotientEvaluator globalComponent = 0
  exact globalComponent_evaluatorZero

def componentClass (dualIndex : Fin 2) : history.CompletionCarrier :=
  history.stageGeneratorToCompletion 0 ⟨
    liftEnvelope (basis .component dualIndex), by
      rw [liftEnvelope_basis]
      exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
        (envelopeGenerator_mem_generatorSupport 0 .component dualIndex)⟩

def quotientUnitClassAt (cursor : Nat) (dualIndex : Fin 2) :
    history.CompletionCarrier :=
  history.stageGeneratorToCompletion cursor ⟨
    liftEnvelope (basis .quotientUnit dualIndex), by
      rw [liftEnvelope_basis]
      exact Finsupp.single_mem_supported (R := ℤ) (1 : ℤ)
        (envelopeGenerator_mem_generatorSupport cursor .quotientUnit dualIndex)⟩

def normalizedComponentAt (cursor : Nat) (dualIndex : Fin 2) :
    history.CompletionCarrier :=
  wholeUnitCoefficient (scheduledFactor cursor) •
    quotientUnitClassAt cursor dualIndex

theorem quotientUnitClassAt_sub (cursor : Nat) :
    quotientUnitClassAt cursor 0 - quotientUnitClassAt cursor 1 =
      history.stageGeneratorToCompletion cursor
        (quotientUnitDifferenceStage cursor) := by
  unfold quotientUnitClassAt
  rw [← map_sub]
  apply congrArg (history.stageGeneratorToCompletion cursor)
  apply Subtype.ext
  change liftEnvelope (basis .quotientUnit 0) -
      liftEnvelope (basis .quotientUnit 1) =
    embeddedQuotientUnitDifference
  unfold embeddedQuotientUnitDifference
    CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.quotientUnitDifference
  rw [map_sub]

theorem normalizedComponent_difference_eq_global (cursor : Nat) :
    normalizedComponentAt cursor 0 - normalizedComponentAt cursor 1 =
      globalComponent := by
  unfold normalizedComponentAt
  rw [← smul_sub, quotientUnitClassAt_sub]
  have wholeCoefficient :=
    wholeUnitCoefficient_eq_primePower_mul_quotient
      (scheduledFactor cursor)
  rw [wholeCoefficient, mul_smul]
  change (scheduledPrime cursor : Nat) ^ scheduledExponent cursor •
      quotientUnitRootAt cursor = globalComponent
  exact scheduled_primePower_landing cursor

theorem normalizedComponent_fixed (cursor : Nat) :
    normalizedComponentAt cursor 0 = normalizedComponentAt cursor 1 := by
  apply sub_eq_zero.mp
  rw [normalizedComponent_difference_eq_global, globalComponent_eq_zero]

theorem globalComponent_eq_component_sub :
    globalComponent = componentClass 0 - componentClass 1 := by
  unfold globalComponent componentAt componentClass
  rw [← map_sub]
  apply congrArg (history.stageGeneratorToCompletion 0)
  apply Subtype.ext
  change liftEnvelope
      CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference =
    liftEnvelope (basis .component 0) -
      liftEnvelope (basis .component 1)
  rw [CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope.componentDifference,
    map_sub]

theorem generatedFixedComponent : componentClass 0 = componentClass 1 := by
  apply sub_eq_zero.mp
  rw [← globalComponent_eq_component_sub]
  exact globalComponent_eq_zero

theorem sourceKernelResidualZero :
    AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt.GeneratedSourceKernelResidualZeroAt
      rigidityFace.faithfulFace rigidityFace.additiveCalculation :=
  rigidityFace.sourceKernelResidualZero

noncomputable def canonicalSourceComponentEquiv :=
  rigidityFace.canonicalSourceComponentEquiv

theorem preserves_exact_root_history_and_rigidity :
    history.root = rootOccurrence ∧
      history.seed = seedEventOccurrence ∧
      history.actualContinuation = nextPatch ∧
      quotientFace.dependentOccurrence.map Prod.fst = history.root := by
  exact ⟨rfl, rfl, rfl,
    quotientFace.dependentOccurrence_projects_to_root⟩

end

end CanonicalUnitArithmeticUnitNormalizedRelationHistory
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
