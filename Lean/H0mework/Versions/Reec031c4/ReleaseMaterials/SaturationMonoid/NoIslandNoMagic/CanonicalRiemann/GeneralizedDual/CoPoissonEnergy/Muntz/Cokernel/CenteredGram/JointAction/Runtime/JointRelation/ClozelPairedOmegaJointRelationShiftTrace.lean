import H0mework.Versions.Y.Arithmetic.RiemannRuntime.ClozelPairedOmegaJointRelationRawAction

set_option autoImplicit false
set_option maxHeartbeats 3000000

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

def rawJointShiftLinear :
    (RuntimeJointRelationGenerator →₀ ℤ) →ₗ[ℤ]
      (RuntimeJointRelationGenerator →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ runtimeJointShiftGenerator

@[simp] theorem rawJointShiftLinear_apply
    (relation : RuntimeJointRelationGenerator →₀ ℤ) :
    rawJointShiftLinear relation = runtimeJointShiftRelation relation :=
  rfl

def rawJointShiftEvent :
    PresentedRelationEventAt RuntimeJointRelationGenerator →
      PresentedRelationEventAt RuntimeJointRelationGenerator
  | .generator generator => .generator (runtimeJointShiftGenerator generator)
  | .relation relation => .relation (runtimeJointShiftRelation relation)

private theorem rawJointShiftGenerator_injective :
    Function.Injective runtimeJointShiftGenerator := by
  intro a b eq
  rcases a with ⟨a, ar⟩
  rcases b with ⟨b, br⟩
  have eq' : (a + 1, ar) = (b + 1, br) := eq
  exact Prod.ext (Nat.add_right_cancel (Prod.mk.inj eq').1) (Prod.mk.inj eq').2

theorem rawJointShiftEvent_support
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (generator : RuntimeJointRelationGenerator)
    (membership : generator ∈ event.support) :
    runtimeJointShiftGenerator generator ∈
      (rawJointShiftEvent event).support := by
  cases event with
  | generator value =>
      simpa [PresentedRelationEventAt.support, rawJointShiftEvent] using
        congrArg runtimeJointShiftGenerator
          (Finset.mem_singleton.mp membership)
  | relation relation =>
      change generator ∈ relation.support at membership
      change runtimeJointShiftGenerator generator ∈
        (runtimeJointShiftRelation relation).support
      rw [runtimeJointShiftRelation,
        Finsupp.mapDomain_support_of_injective rawJointShiftGenerator_injective]
      exact Finset.mem_image.mpr ⟨generator, membership, rfl⟩

theorem rawJointShiftEvent_seed_trace
    (stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership : event ∈ (runtimeJointRelationSeedAt stage).trace) :
    rawJointShiftEvent event ∈
      (runtimeJointRelationSeedAt (stage + 1)).trace := by
  rw [runtimeJointRelationSeedAt_trace] at membership ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership ⊢
  rcases membership with h | h | h | h | h | h | h
  · subst event; simp [rawJointShiftEvent, runtimeJointIncidencePresentedEvent]
  · subst event; simp [rawJointShiftEvent, runtimeJointSourceBoundaryPresentedEvent]
  · subst event; simp [rawJointShiftEvent, runtimeJointQuarterIncidencePresentedEvent]
  · subst event; simp [rawJointShiftEvent, runtimeJointQuarterSourceBoundaryPresentedEvent]
  · subst event; simp [rawJointShiftEvent, runtimeJointQuarterBoundaryEnergyPresentedEvent]
  · subst event; simp [rawJointShiftEvent, runtimeJointQuarterBalancePresentedEvent]
  · subst event; simp [rawJointShiftEvent, runtimeJointBalancePresentedEvent]

private theorem rawJointObservation_frontier
    {current : Current}
    (occurrence :
      CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat) :
    ((runtimeJointRawHistoryAt occurrence).observation stage).frontier =
      [runtimeJointBalancePresentedEvent (currentEffectStage current + stage)] := by
  induction stage with
  | zero =>
      exact runtimeJointRelationSeedAt_frontier _
  | succ stage ih =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ]
      simp only [RootedAccountedUnfolding.frontier_advance]
      rw [ih]
      change (runtimeJointShiftContinuationAt
        (runtimeJointBalancePresentedEvent
          (currentEffectStage current + stage))).frontier = _
      simpa only [List.flatMap_singleton, Nat.add_succ] using
        runtimeJointShiftContinuationAt_balance_frontier
          (currentEffectStage current + stage)

private theorem rawJointObservation_trace_origin
    {current : Current}
    (occurrence :
      CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership : event ∈
      ((runtimeJointRawHistoryAt occurrence).observation stage).trace) :
    ∃ offset ≤ stage,
      event ∈
        (runtimeJointRelationSeedAt
          (currentEffectStage current + offset)).trace := by
  induction stage with
  | zero =>
      exact ⟨0, le_refl 0, membership⟩
  | succ stage ih =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ] at membership
      cases RootedAccountedUnfolding.trace_advance_cases
          (runtimeJointRawHistoryAt occurrence).actualContinuation
          ((runtimeJointRawHistoryAt occurrence).observation stage)
          event membership with
      | inl old =>
          obtain ⟨offset, bound, source⟩ := ih old
          exact ⟨offset, Nat.le_succ_of_le bound, source⟩
      | inr generated =>
          obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
          rw [rawJointObservation_frontier occurrence stage] at leaf_mem
          have leaf_eq : leaf =
              runtimeJointBalancePresentedEvent
                (currentEffectStage current + stage) :=
            List.mem_singleton.mp leaf_mem
          subst leaf
          refine ⟨stage + 1, le_refl _, ?_⟩
          change event ∈
            (runtimeJointShiftContinuationAt
              (runtimeJointBalancePresentedEvent
                (currentEffectStage current + stage))).trace
            at generated_mem
          rw [runtimeJointShiftContinuationAt_balance_trace] at generated_mem
          rw [runtimeJointRelationSeedAt_trace]
          simpa only [Nat.add_succ] using generated_mem

theorem rawJointObservation_currentSeed_trace_subset
    {current : Current}
    (occurrence :
      CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat) :
    ∀ event ∈
      (runtimeJointRelationSeedAt
        (currentEffectStage current + stage)).trace,
      event ∈ ((runtimeJointRawHistoryAt occurrence).observation stage).trace := by
  induction stage with
  | zero =>
      intro event membership
      exact membership
  | succ stage _ih =>
      intro event membership
      rw [RootGeneratedCofinalHistoryAt.observation_succ]
      apply RootedAccountedUnfolding.generated_trace_mem_trace_advance
        (runtimeJointRawHistoryAt occurrence).actualContinuation
        ((runtimeJointRawHistoryAt occurrence).observation stage)
        (runtimeJointBalancePresentedEvent
          (currentEffectStage current + stage))
      · rw [rawJointObservation_frontier occurrence stage]
        simp
      · change event ∈
          (runtimeJointShiftContinuationAt
            (runtimeJointBalancePresentedEvent
              (currentEffectStage current + stage))).trace
        rw [runtimeJointShiftContinuationAt_balance]
        simpa only [Nat.add_succ] using membership

theorem rawJointShiftEvent_observed
    {current : Current}
    (occurrence :
      CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat)
    (event : PresentedRelationEventAt RuntimeJointRelationGenerator)
    (membership :
      event ∈ (runtimeJointRawHistoryAt occurrence).observedEvents stage) :
    rawJointShiftEvent event ∈
      (runtimeJointRawHistoryAt occurrence).observedEvents (stage + 1) := by
  unfold RootGeneratedCofinalHistoryAt.observedEvents at membership ⊢
  obtain ⟨index, index_mem, event_mem⟩ := List.mem_flatMap.mp membership
  obtain ⟨offset, offset_le, source_mem⟩ :=
    rawJointObservation_trace_origin occurrence index event event_mem
  apply List.mem_flatMap.mpr
  refine ⟨offset + 1, ?_, ?_⟩
  · simp only [List.mem_range] at index_mem ⊢
    omega
  · have shifted := rawJointShiftEvent_seed_trace
      (currentEffectStage current + offset) event source_mem
    have shifted' : rawJointShiftEvent event ∈
        (runtimeJointRelationSeedAt
          (currentEffectStage current + (offset + 1))).trace := by
      simpa only [Nat.add_succ] using shifted
    exact rawJointObservation_currentSeed_trace_subset occurrence (offset + 1)
      (rawJointShiftEvent event) shifted'

theorem rawJointShift_generatorSupport
    {current : Current}
    (occurrence :
      CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current)
    (stage : Nat)
    (generator : RuntimeJointRelationGenerator)
    (membership : generator ∈
      (runtimeJointRawHistoryAt occurrence).generatorSupport stage) :
    runtimeJointShiftGenerator generator ∈
      (runtimeJointRawHistoryAt occurrence).generatorSupport (stage + 1) := by
  classical
  simp only [RootGeneratedCofinalHistoryAt.generatorSupport,
    List.mem_toFinset, List.mem_flatMap, Finset.mem_toList] at membership ⊢
  obtain ⟨event, event_mem, support_mem⟩ := membership
  exact ⟨rawJointShiftEvent event,
    rawJointShiftEvent_observed occurrence stage event event_mem,
    rawJointShiftEvent_support event generator support_mem⟩

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
