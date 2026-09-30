import H0mework.Versions.Y.Arithmetic.RiemannGraph.RuntimeMuntzConductorHistoryRoot
import H0mework.Foundation.Source.TraceAdvance

/-!
# Soundness of the rooted conductor history

Every relation appearing in the generated trace is an actual shifted
prefix-successor relation.  The complete test/scale evaluator kills the
entire relation closure, so soundness is derived from the rooted history
rather than submitted to the faithful settlement engine.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalHistorySettlement
open CofinalHistorySettlementFace
open Material
open RootedAccountedUnfolding

noncomputable section

def directObservation (start : Nat) : Nat →
    RootedAccountedUnfolding
      (PresentedRelationEventAt ConductorHistoryGenerator)
  | 0 => conductorHistorySeedAt start
  | stage + 1 =>
      (directObservation start stage).advance conductorHistoryContinuationAt

@[simp] theorem directObservation_zero (start : Nat) :
    directObservation start 0 = conductorHistorySeedAt start := rfl

@[simp] theorem directObservation_succ (start stage : Nat) :
    directObservation start (stage + 1) =
      (directObservation start stage).advance conductorHistoryContinuationAt :=
  rfl

theorem directObservation_frontier (start stage : Nat) :
    (directObservation start stage).frontier =
      [conductorSuccessorPresentedEvent (start + stage)] := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      rw [directObservation_succ]
      rw [RootedAccountedUnfolding.frontier_advance]
      rw [ih]
      simp [conductorHistoryContinuationAt_successor,
        conductorHistorySeedAt]
      congr 2

theorem directObservation_trace_is_successor
    (start stage : Nat)
    {event : PresentedRelationEventAt ConductorHistoryGenerator}
    (event_mem : event ∈ (directObservation start stage).trace) :
    ∃ cutoff : Nat, event = conductorSuccessorPresentedEvent cutoff := by
  induction stage with
  | zero =>
      refine ⟨start, ?_⟩
      change event ∈ [conductorSuccessorPresentedEvent start] at event_mem
      simpa using event_mem
  | succ stage ih =>
      have cases := (mem_trace_advance_iff conductorHistoryContinuationAt
        (directObservation start stage) event).1 event_mem
      rcases cases with old | generated
      · exact ih old
      · obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
        rw [directObservation_frontier] at leaf_mem
        have leaf_eq : leaf =
            conductorSuccessorPresentedEvent (start + stage) := by
          simpa using leaf_mem
        subst leaf
        refine ⟨start + stage + 1, ?_⟩
        rw [conductorHistoryContinuationAt_successor] at generated_mem
        change event ∈
          [conductorSuccessorPresentedEvent (start + stage + 1)]
            at generated_mem
        simpa using generated_mem

theorem materialHistory_observation_eq_direct
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat) :
    ((runtimeConductorHistoryMaterialLaw observation nontrivial).historyAt
      occurrence).observation stage =
      directObservation 0 stage := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ,
        directObservation_succ, ih]
      rfl

theorem materialHistory_observed_relation_is_successor
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat) (relation : ConductorHistoryGenerator →₀ ℤ)
    (relation_mem : PresentedRelationEventAt.relation relation ∈
      ((runtimeConductorHistoryMaterialLaw observation nontrivial).historyAt
        occurrence).observedEvents stage) :
    ∃ cutoff : Nat, relation = conductorSuccessorRelation cutoff := by
  change PresentedRelationEventAt.relation relation ∈
    (List.map
      (fun index =>
        (((runtimeConductorHistoryMaterialLaw observation nontrivial
          ).historyAt occurrence).observation index).trace)
      (List.range (stage + 1))).flatten at relation_mem
  obtain ⟨events, events_mem, relation_mem⟩ :=
    List.mem_flatten.mp relation_mem
  obtain ⟨index, index_mem, events_eq⟩ := List.mem_map.mp events_mem
  subst events
  rw [materialHistory_observation_eq_direct] at relation_mem
  obtain ⟨cutoff, event_eq⟩ := directObservation_trace_is_successor
    0 index relation_mem
  refine ⟨cutoff, ?_⟩
  injection event_eq

/-- Every relation generated by the rooted conductor history is killed by
the actual full test/scale evaluator. -/
theorem runtimeConductorFaithful_relationsSound
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    ((runtimeConductorFaithfulMaterialLaw observation nontrivial).faithfulAt
      occurrence).RelationsSound := by
  unfold RootGeneratedCofinalFaithfulRealizationAt.RelationsSound
  refine iSup_le fun stage => ?_
  apply Submodule.span_le.mpr
  intro relation relation_mem
  apply (LinearMap.mem_ker).2
  obtain ⟨cutoff, relation_eq⟩ :=
    materialHistory_observed_relation_is_successor
      observation nontrivial occurrence stage relation relation_mem
  subst relation
  change conductorHistoryFreeEvaluation
      (generateRuntimeAllPlaceWeilFace observation nontrivial occurrence)
      (conductorSuccessorRelation cutoff) = 0
  exact conductorSuccessorRelation_evaluates_zero _ _

theorem runtimeConductorHistoryStep_relationsSound
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeConductorHistoryStepAt observation nontrivial depth
      ).faithful.RelationsSound :=
  runtimeConductorFaithful_relationsSound observation nontrivial
    (runtimeConductorHistoryStepAt observation nontrivial depth
      ).sourceOccurrence

/-- Every exact all-place occurrence carries the canonical conductor clock
from zero.  Its history observation index is independent of the q-rich
runtime depth carried by that occurrence. -/
theorem materialHistory_observation_frontier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current)
    (index : Nat) :
    (((runtimeConductorHistoryMaterialLaw observation nontrivial).historyAt
        occurrence).observation index).frontier =
        [conductorSuccessorPresentedEvent index] := by
  rw [materialHistory_observation_eq_direct]
  unfold runtimeConductorHistoryMaterialLaw
  unfold SourceNativeCofinalHistoryMaterialLaw.create
  simpa using directObservation_frontier 0 index

theorem materialHistory_observes_successor
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence :
      (Root.runtimeAllPlaceWeilAuthoritySource observation nontrivial
        ).restructuringSource.source.toRootSource.actual.OccurrenceAt current)
    (index : Nat) :
    conductorSuccessorPresentedEvent index ∈
      (((runtimeConductorHistoryMaterialLaw observation nontrivial).historyAt
        occurrence).observation index).trace := by
  rw [materialHistory_observation_eq_direct]
  unfold runtimeConductorHistoryMaterialLaw
  unfold SourceNativeCofinalHistoryMaterialLaw.create
  apply RootedAccountedUnfolding.frontier_mem_trace
  rw [directObservation_frontier]
  simp

/-- The generic relation classifier is forced into its sound branch by the
actual rooted successor trace. -/
theorem runtimeConductorHistorySoundnessAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    GeneratedRelationSoundnessAt
      (runtimeConductorHistoryStepAt observation nontrivial depth
        ).faithful := by
  let face :=
    (runtimeConductorHistoryStepAt observation nontrivial depth).faithful
  cases h : face.settleRelations with
  | sound soundness => exact soundness
  | unsound obstruction =>
      exact False.elim
        (obstruction.notSound
          (runtimeConductorHistoryStep_relationsSound
            observation nontrivial depth))

end

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History
