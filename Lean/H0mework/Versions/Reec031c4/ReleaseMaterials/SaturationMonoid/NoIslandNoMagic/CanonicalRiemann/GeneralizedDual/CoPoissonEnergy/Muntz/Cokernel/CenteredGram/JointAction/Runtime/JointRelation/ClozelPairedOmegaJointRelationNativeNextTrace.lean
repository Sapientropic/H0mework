import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationShiftTrace
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaFiniteEffectHistory

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt

noncomputable section

abbrev nativeNextJointHistory (depth : Nat) :=
  runtimeJointRawHistoryAt
    (CanonicalUnitArithmeticRoot.emitted
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current)

private theorem nativeNextJoint_frontier (depth stage : Nat) :
    ((nativeNextJointHistory depth).observation stage).frontier =
      [runtimeJointBalancePresentedEvent (depth + stage)] := by
  induction stage with
  | zero =>
      change (runtimeJointRelationSeedAt
        (currentEffectStage (CanonicalUnitArithmeticRoot.finiteVisit depth).current
          )).frontier = _
      rw [currentEffectStage_finiteVisit,
        runtimeJointRelationSeedAt_frontier]
      simp
  | succ stage ih =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ]
      simp only [RootedAccountedUnfolding.frontier_advance]
      rw [ih]
      change (runtimeJointShiftContinuationAt
        (runtimeJointBalancePresentedEvent (depth + stage))).frontier = _
      simpa only [List.flatMap_singleton, Nat.add_succ] using
        runtimeJointShiftContinuationAt_balance_frontier (depth + stage)

private theorem nativeNextJoint_sourceSeed_trace_subset
    (depth stage : Nat) :
    ∀ event ∈ (runtimeJointRelationSeedAt (depth + stage)).trace,
      event ∈ ((nativeNextJointHistory depth).observation stage).trace := by
  intro event event_mem
  have source_mem := rawJointObservation_currentSeed_trace_subset
    (CanonicalUnitArithmeticRoot.emitted
    (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
    stage event
  have source_seed : event ∈
      (runtimeJointRelationSeedAt
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current + stage)).trace := by
    simpa only [currentEffectStage_finiteVisit] using event_mem
  exact source_mem source_seed

private theorem nativeNextJoint_trace_mem_observed
    (depth stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership : event ∈
      ((nativeNextJointHistory depth).observation stage).trace) :
    event ∈ (nativeNextJointHistory depth).observedEvents stage := by
  unfold RootGeneratedCofinalHistoryAt.observedEvents
  exact List.mem_flatMap.mpr ⟨stage, by simp, membership⟩

private theorem nativeNextJoint_targetTrace_in_sourceObserved
    (depth stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership : event ∈
      ((nativeNextJointHistory (depth + 1)).observation stage).trace) :
    event ∈ (nativeNextJointHistory depth).observedEvents (stage + 1) := by
  induction stage with
  | zero =>
      have seed_mem : event ∈
          (runtimeJointRelationSeedAt (depth + 1)).trace := by
        change event ∈
          (runtimeJointRelationSeedAt
            (currentEffectStage
              (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)).trace
          at membership
        rw [currentEffectStage_finiteVisit] at membership
        exact membership
      exact nativeNextJoint_trace_mem_observed depth 1 event
        (nativeNextJoint_sourceSeed_trace_subset depth 1 event seed_mem)
  | succ stage ih =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ] at membership
      cases RootedAccountedUnfolding.trace_advance_cases
          (nativeNextJointHistory (depth + 1)).actualContinuation
          ((nativeNextJointHistory (depth + 1)).observation stage)
          event membership with
      | inl old =>
          exact (nativeNextJointHistory depth).observedEvents_mono
            (Nat.le_succ (stage + 1)) event (ih old)
      | inr generated =>
          obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
          rw [nativeNextJoint_frontier (depth + 1) stage] at leaf_mem
          have leaf_eq : leaf =
              runtimeJointBalancePresentedEvent (depth + 1 + stage) :=
            List.mem_singleton.mp leaf_mem
          subst leaf
          change event ∈ (runtimeJointShiftContinuationAt
            (runtimeJointBalancePresentedEvent (depth + 1 + stage))).trace
            at generated_mem
          rw [runtimeJointShiftContinuationAt_balance] at generated_mem
          have source_seed : event ∈
              (runtimeJointRelationSeedAt (depth + (stage + 2))).trace := by
            have stageEq : depth + 1 + stage + 1 = depth + (stage + 2) := by
              omega
            simpa only [stageEq] using generated_mem
          exact nativeNextJoint_trace_mem_observed depth (stage + 2) event
            (nativeNextJoint_sourceSeed_trace_subset depth (stage + 2)
              event source_seed)

private theorem nativeNextJoint_targetObserved_in_sourceObserved
    (depth stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership : event ∈
      (nativeNextJointHistory (depth + 1)).observedEvents stage) :
    event ∈ (nativeNextJointHistory depth).observedEvents (stage + 1) := by
  unfold RootGeneratedCofinalHistoryAt.observedEvents at membership
  obtain ⟨index, index_mem, event_mem⟩ := List.mem_flatMap.mp membership
  have trace_mem := nativeNextJoint_targetTrace_in_sourceObserved
    depth index event event_mem
  apply (nativeNextJointHistory depth).observedEvents_mono
    (first := index + 1) (later := stage + 1)
  · simp only [List.mem_range] at index_mem
    omega
  · exact trace_mem

private theorem nativeNextJoint_generatorSupport_le
    (depth stage : Nat) :
    ((nativeNextJointHistory (depth + 1)).generatorSupport stage :
      Set RuntimeJointRelationGenerator) ⊆
      (nativeNextJointHistory depth).generatorSupport (stage + 1) := by
  classical
  intro generator generator_mem
  change generator ∈
    (nativeNextJointHistory (depth + 1)).generatorSupport stage at generator_mem
  change generator ∈
    (nativeNextJointHistory depth).generatorSupport (stage + 1)
  simp only [RootGeneratedCofinalHistoryAt.generatorSupport,
    List.mem_toFinset, List.mem_flatMap, Finset.mem_toList]
    at generator_mem ⊢
  obtain ⟨event, event_mem, support_mem⟩ := generator_mem
  exact ⟨event,
    nativeNextJoint_targetObserved_in_sourceObserved
      depth stage event event_mem, support_mem⟩

theorem nativeNextJoint_generatorStage_le
    (depth stage : Nat) :
    (nativeNextJointHistory (depth + 1)).generatorStage stage ≤
      (nativeNextJointHistory depth).generatorStage (stage + 1) := by
  exact Finsupp.supported_mono
    (nativeNextJoint_generatorSupport_le depth stage)

theorem nativeNextJoint_relationStage_le
    (depth stage : Nat) :
    (nativeNextJointHistory (depth + 1)).relationStage stage ≤
      (nativeNextJointHistory depth).relationStage (stage + 1) := by
  apply Submodule.span_mono
  intro relation relation_mem
  exact nativeNextJoint_targetObserved_in_sourceObserved depth stage
    (.relation relation) relation_mem

end
end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
