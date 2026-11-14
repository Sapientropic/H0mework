import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationNativeNextTransition

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

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
open CofinalHistoryTransition

noncomputable section

private theorem runtimeJointAtom_zero_off_stage
    (stage other : Nat)
    (role sourceRole : RuntimeJointRelationRole)
    (ne : other ≠ stage) :
    runtimeJointRelationAtom stage sourceRole (other, role) = 0 := by
  have pair_ne : (other, role) ≠ (stage, sourceRole) := by
    intro equality
    exact ne (congrArg Prod.fst equality)
  simp [runtimeJointRelationAtom, pair_ne]

private theorem runtimeJointSeed_support_at_stage
    (stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (event_mem : event ∈ (runtimeJointRelationSeedAt stage).trace)
    (generator : RuntimeJointRelationGenerator)
    (support_mem : generator ∈ event.support) :
    generator.1 = stage := by
  by_contra ne
  rcases generator with ⟨other, role⟩
  have atom_zero (sourceRole : RuntimeJointRelationRole) :
      runtimeJointRelationAtom stage sourceRole (other, role) = 0 :=
    runtimeJointAtom_zero_off_stage stage other role sourceRole ne
  rw [runtimeJointRelationSeedAt_trace] at event_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at event_mem
  rcases event_mem with h | h | h | h | h | h | h
  all_goals subst event
  all_goals
    simp [runtimeJointIncidencePresentedEvent,
      runtimeJointSourceBoundaryPresentedEvent,
      runtimeJointQuarterIncidencePresentedEvent,
      runtimeJointQuarterSourceBoundaryPresentedEvent,
      runtimeJointQuarterBoundaryEnergyPresentedEvent,
      runtimeJointQuarterBalancePresentedEvent,
      runtimeJointBalancePresentedEvent,
      PresentedRelationEventAt.support, Finsupp.mem_support_iff,
      runtimeJointIncidenceStageRelation,
      runtimeJointSourceBoundaryStageRelation,
      runtimeJointQuarterIncidenceStageRelation,
      runtimeJointQuarterSourceBoundaryStageRelation,
      runtimeJointQuarterBoundaryEnergyStageRelation,
      runtimeJointQuarterBalanceStageRelation,
      runtimeJointBalanceStageRelation,
      Finsupp.sub_apply, atom_zero, sub_zero] at support_mem

private theorem reverseJoint_frontier (depth stage : Nat) :
    ((nativeNextJointHistory depth).observation stage).frontier =
      [runtimeJointBalancePresentedEvent (depth + stage)] := by
  induction stage with
  | zero =>
      change (runtimeJointRelationSeedAt
        (currentEffectStage
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).frontier = _
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

private theorem reverseJoint_trace_origin
    (depth stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership : event ∈
      ((nativeNextJointHistory depth).observation stage).trace) :
    ∃ offset ≤ stage,
      event ∈ (runtimeJointRelationSeedAt (depth + offset)).trace := by
  induction stage with
  | zero =>
      have seed_mem : event ∈
          (runtimeJointRelationSeedAt depth).trace := by
        change event ∈
          (runtimeJointRelationSeedAt
            (currentEffectStage
              (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).trace
          at membership
        rw [currentEffectStage_finiteVisit] at membership
        exact membership
      exact ⟨0, le_refl _, by simpa only [Nat.add_zero] using seed_mem⟩
  | succ stage ih =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ] at membership
      cases RootedAccountedUnfolding.trace_advance_cases
          (nativeNextJointHistory depth).actualContinuation
          ((nativeNextJointHistory depth).observation stage)
          event membership with
      | inl old =>
          obtain ⟨offset, offset_le, seed_mem⟩ := ih old
          exact ⟨offset, Nat.le_succ_of_le offset_le, seed_mem⟩
      | inr generated =>
          obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
          rw [reverseJoint_frontier depth stage] at leaf_mem
          have leaf_eq : leaf =
              runtimeJointBalancePresentedEvent (depth + stage) :=
            List.mem_singleton.mp leaf_mem
          subst leaf
          refine ⟨stage + 1, le_refl _, ?_⟩
          change event ∈ (runtimeJointShiftContinuationAt
            (runtimeJointBalancePresentedEvent (depth + stage))).trace
            at generated_mem
          rw [runtimeJointShiftContinuationAt_balance] at generated_mem
          simpa only [Nat.add_succ] using generated_mem

private theorem reverseJoint_generatorSupport_future
    (depth stage : Nat)
    (generator : RuntimeJointRelationGenerator)
    (membership : generator ∈
      (nativeNextJointHistory depth).generatorSupport stage) :
    depth ≤ generator.1 := by
  classical
  simp only [RootGeneratedCofinalHistoryAt.generatorSupport,
    List.mem_toFinset, List.mem_flatMap, Finset.mem_toList] at membership
  obtain ⟨event, event_mem, support_mem⟩ := membership
  unfold RootGeneratedCofinalHistoryAt.observedEvents at event_mem
  obtain ⟨index, _index_mem, trace_mem⟩ :=
    List.mem_flatMap.mp event_mem
  obtain ⟨offset, _offset_le, seed_mem⟩ :=
    reverseJoint_trace_origin depth index event trace_mem
  have at_stage := runtimeJointSeed_support_at_stage
    (depth + offset) event seed_mem generator support_mem
  omega

theorem reverseJoint_generatorClosure_future (depth : Nat) :
    (nativeNextJointHistory depth).generatorClosure ≤
      Finsupp.supported ℤ ℤ
        {generator : RuntimeJointRelationGenerator | depth ≤ generator.1} := by
  apply iSup_le
  intro stage
  exact Finsupp.supported_mono
    (fun generator membership =>
      reverseJoint_generatorSupport_future depth stage generator membership)

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
