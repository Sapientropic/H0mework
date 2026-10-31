import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Trace.FiniteActualRepairFailureTrace
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Measure.FiniteObserverMeasure

/-!
# M14 actual repair-failure counting measure

The already generated paired actual-failure trace receives its canonical
occurrence-counting measure.  The only public producer input is the requested
finite horizon.  Every coefficient is definitionally one; no caller supplies
weights, support, total mass, a normalizer, or a probability.

This is a neutral finite-measure producer over the existing dependent
occurrence carrier.  It does not retype M14 occurrences as M11 crossings and
does not create a second occurrence, trace, registry, root, or ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ActualRepairFailureCountingMeasure

noncomputable section

open Probability Measure
open UBI Policy
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14ActualRepairFailureOccurrence
open M14FiniteActualRepairFailureTrace

/-- The sole weighted inventory: the existing paired trace mapped with the
source-fixed counting coefficient one. -/
def actualRepairFailureWeightedTrace (horizon : Nat) :
    List (AnyActualRepairFailure × ℚ≥0) :=
  (sourceGeneratedFiniteActualRepairFailureTrace horizon).map
    (fun occurrence => (occurrence, 1))

/-- Canonical unit-count measure over the existing actual trace. -/
def actualRepairFailureCountingMeasure (horizon : Nat) :
    FiniteObserverMeasure AnyActualRepairFailure where
  weightedOccurrences := actualRepairFailureWeightedTrace horizon
  occurrence_nodup := by
    simpa [actualRepairFailureWeightedTrace, List.map_map,
      Function.comp_def] using
      finiteActualRepairFailureTrace_nodup horizon

@[simp] theorem countingMeasure_weightedOccurrences (horizon : Nat) :
    (actualRepairFailureCountingMeasure horizon).weightedOccurrences =
      actualRepairFailureWeightedTrace horizon :=
  rfl

@[simp] theorem countingMeasure_occurrenceTrace (horizon : Nat) :
    (actualRepairFailureCountingMeasure horizon).occurrenceTrace =
      sourceGeneratedFiniteActualRepairFailureTrace horizon := by
  simp [actualRepairFailureCountingMeasure,
    actualRepairFailureWeightedTrace,
    FiniteObserverMeasure.occurrenceTrace, List.map_map,
    Function.comp_def]

theorem countingMeasure_occurrenceTrace_nodup (horizon : Nat) :
    (actualRepairFailureCountingMeasure horizon).occurrenceTrace.Nodup :=
  (actualRepairFailureCountingMeasure horizon).occurrenceTrace_nodup

@[simp] theorem countingMeasure_occurrenceTrace_length (horizon : Nat) :
    (actualRepairFailureCountingMeasure horizon).occurrenceTrace.length =
      2 * horizon := by
  rw [countingMeasure_occurrenceTrace,
    finiteActualRepairFailureTrace_length]

@[simp] theorem countingMeasure_coefficient_exact
    {horizon : Nat} {weighted : AnyActualRepairFailure × ℚ≥0}
    (membership : weighted ∈
      (actualRepairFailureCountingMeasure horizon).weightedOccurrences) :
    weighted.2 = 1 := by
  rcases List.mem_map.mp membership with
    ⟨occurrence, _occurrenceMem, rfl⟩
  rfl

theorem countingMeasure_weighted_member_provenance
    {horizon : Nat} {weighted : AnyActualRepairFailure × ℚ≥0}
    (membership : weighted ∈
      (actualRepairFailureCountingMeasure horizon).weightedOccurrences) :
    weighted.2 = 1 ∧
      weighted.1 ∈ sourceGeneratedFiniteActualRepairFailureTrace horizon := by
  rcases List.mem_map.mp membership with
    ⟨occurrence, occurrenceMem, rfl⟩
  exact ⟨rfl, occurrenceMem⟩

private theorem foldr_countingMass_eq_length
    {Occurrence : Type*} (occurrences : List Occurrence) :
    occurrences.foldr
        (fun (_ : Occurrence) (accumulated : ℚ≥0) => 1 + accumulated) 0 =
      occurrences.length := by
  induction occurrences with
  | nil => rfl
  | cons _ rest inductionHypothesis =>
      simp only [List.foldr_cons, List.length_cons]
      rw [inductionHypothesis]
      simp [add_comm]

theorem countingMeasure_eventMass_eq_filtered_length
    (horizon : Nat) (event : AnyActualRepairFailure → Prop)
    [DecidablePred event] :
    (actualRepairFailureCountingMeasure horizon).eventMass event =
      ((actualRepairFailureCountingMeasure horizon).occurrenceTrace
        |>.filter event).length := by
  rw [countingMeasure_occurrenceTrace]
  unfold FiniteObserverMeasure.eventMass
    actualRepairFailureCountingMeasure
    actualRepairFailureWeightedTrace
  rw [List.foldr_map]
  simp only
  induction sourceGeneratedFiniteActualRepairFailureTrace horizon with
  | nil => rfl
  | cons occurrence rest inductionHypothesis =>
      by_cases observed : event occurrence
      · rw [List.foldr_cons, if_pos observed]
        have filtered :
            (occurrence :: rest).filter event =
              occurrence :: rest.filter event := by
          simp [observed]
        rw [filtered, List.length_cons, Nat.cast_succ,
          inductionHypothesis]
        exact add_comm _ _
      · rw [List.foldr_cons, if_neg observed]
        have filtered :
            (occurrence :: rest).filter event = rest.filter event := by
          simp [observed]
        rw [filtered]
        exact inductionHypothesis

@[simp] theorem countingMeasure_totalMass (horizon : Nat) :
    (actualRepairFailureCountingMeasure horizon).totalMass =
      (2 * horizon : Nat) := by
  unfold FiniteObserverMeasure.totalMass
    actualRepairFailureCountingMeasure
    actualRepairFailureWeightedTrace
  rw [List.foldr_map]
  simp only
  rw [foldr_countingMass_eq_length,
    finiteActualRepairFailureTrace_length]

@[simp] theorem countingMeasure_zero_occurrenceTrace :
    (actualRepairFailureCountingMeasure 0).occurrenceTrace = [] := by
  rw [countingMeasure_occurrenceTrace]
  rfl

@[simp] theorem countingMeasure_zero_totalMass :
    (actualRepairFailureCountingMeasure 0).totalMass = 0 := by
  rw [countingMeasure_totalMass]
  rfl

theorem countingMeasure_tenure_mem_iff
    {horizon depth : Nat} :
    tenureRepairFailureOccurrenceAt depth ∈
        (actualRepairFailureCountingMeasure horizon).occurrenceTrace ↔
      depth < horizon := by
  rw [countingMeasure_occurrenceTrace]
  exact tenureOccurrence_mem_pairedTrace_iff

theorem countingMeasure_route_mem_iff
    {horizon depth : Nat} :
    routeRepairFailureOccurrenceAt depth ∈
        (actualRepairFailureCountingMeasure horizon).occurrenceTrace ↔
      depth < horizon := by
  rw [countingMeasure_occurrenceTrace]
  exact routeOccurrence_mem_pairedTrace_iff

structure CountingMeasureMemberCertificate
    (horizon : Nat) (occurrence : AnyActualRepairFailure) : Prop where
  depthLt : occurrence.depth < horizon
  failureKindExact :
    occurrence.failureKind = ExactExitFailureKind.tenureCapture ∨
      occurrence.failureKind = ExactExitFailureKind.routeBottleneck
  rootOccurrenceExact :
    occurrence.actual.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt occurrence.depth)
  sourceConsumerExact :
    ActualRepairFailureAt.SourceConsumerExactAt occurrence.origin
      occurrence.actual
  installedActionExact :
    ActualRepairFailureAt.InstalledActionExactAt occurrence.origin
      occurrence.actual
  selectedWriteCommutes :
    ActualRepairFailureAt.SelectedWriteCommutesAt occurrence.origin
      occurrence.actual
  rootFactorizes :
    ActualRepairFailureAt.RootFactorizesAt occurrence.origin
      occurrence.actual
  componentOutcomeExact :
    ActualRepairFailureAt.ComponentOutcomeExactAt occurrence.origin
      occurrence.actual
  wholeLedgerExact :
    HEq occurrence.actual.wholeLedgerWriteBack
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt occurrence.depth)).wholeLedgerWriteBack
  generatedNextExact :
    occurrence.actual.generatedNext =
      jointRoot.generatedNextCurrentAt
        (temporalVisitAt occurrence.depth)

theorem countingMeasure_member_exact
    {horizon : Nat} {occurrence : AnyActualRepairFailure}
    (membership : occurrence ∈
      (actualRepairFailureCountingMeasure horizon).occurrenceTrace) :
    CountingMeasureMemberCertificate horizon occurrence := by
  rw [countingMeasure_occurrenceTrace] at membership
  rcases finiteActualRepairFailureTrace_member_exact membership with
    ⟨depthLt, failureKindExact, rootOccurrenceExact,
      sourceConsumerExact, installedActionExact, selectedWriteCommutes,
      rootFactorizes, componentOutcomeExact, wholeLedgerExact,
      generatedNextExact⟩
  exact
    { depthLt := depthLt
      failureKindExact := failureKindExact
      rootOccurrenceExact := rootOccurrenceExact
      sourceConsumerExact := sourceConsumerExact
      installedActionExact := installedActionExact
      selectedWriteCommutes := selectedWriteCommutes
      rootFactorizes := rootFactorizes
      componentOutcomeExact := componentOutcomeExact
      wholeLedgerExact := wholeLedgerExact
      generatedNextExact := generatedNextExact }

theorem countingMeasure_mouth_has_no_submitted_measure_authority
    (horizon : Nat) : True := by
  let measure := actualRepairFailureCountingMeasure horizon
  fail_if_success exact measure.submittedWeights
  fail_if_success exact measure.submittedSupport
  fail_if_success exact measure.submittedTotalMass
  fail_if_success exact measure.normalizer
  fail_if_success exact measure.probability
  fail_if_success exact measure.coverage
  fail_if_success exact measure.occurrenceRegistry
  fail_if_success exact measure.completedFuture
  trivial

end
end M14ActualRepairFailureCountingMeasure
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureCountingMeasure.actualRepairFailureCountingMeasure
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureCountingMeasure.countingMeasure_occurrenceTrace
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureCountingMeasure.countingMeasure_totalMass
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureCountingMeasure.countingMeasure_eventMass_eq_filtered_length
#print axioms SaturationMonoid.ProcessGame.Society.M14ActualRepairFailureCountingMeasure.countingMeasure_member_exact
