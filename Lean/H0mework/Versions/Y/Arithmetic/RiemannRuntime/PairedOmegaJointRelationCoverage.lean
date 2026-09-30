import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaJointRelationRoot

/-!
# Coverage and soundness of the paired-Omega joint history

Every finite observation contains the complete current seven-row stage seed:
root-scale boundary/incidence/balance and quarter-scale
boundary/incidence, its energy/remainder split, and balance.
The generated closure contains no other relation family, so the installed
evaluator kills every generated relation without a caller soundness premise.
-/

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
open CofinalFaithfulSettlementFace
open CofinalFaithfulSettlementFace.RootGeneratedCofinalFaithfulSettlementStepAt

noncomputable section

/-- The current stage seed is present in full in every finite observation.
Earlier stage rows may remain in the accumulated trace as provenance. -/
theorem runtimeJointFaithfulObservation_currentSeed_trace_subset
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    ∀ event ∈ (runtimeJointRelationSeedAt (depth + stage)).trace,
      event ∈ ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace := by
  induction stage with
  | zero =>
      intro event membership
      change event ∈
        (runtimeJointRelationSeedAt
          (currentEffectStage
            (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).trace
      simpa using membership
  | succ stage _inductionHypothesis =>
      intro event membership
      rw [RootGeneratedCofinalHistoryAt.observation_succ]
      apply RootedAccountedUnfolding.generated_trace_mem_trace_advance
        (runtimeJointFaithfulStepAt observation nontrivial depth
          ).history.actualContinuation
        ((runtimeJointFaithfulStepAt observation nontrivial depth
          ).history.observation stage)
        (runtimeJointBalancePresentedEvent (depth + stage))
      · have frontierEq := runtimeJointFaithfulObservation_frontier
          observation nontrivial depth stage
        have listMem :
            runtimeJointBalancePresentedEvent (depth + stage) ∈
              [runtimeJointBalancePresentedEvent (depth + stage)] := by
          simp
        exact frontierEq.symm ▸ listMem
      · change event ∈
          (runtimeJointShiftContinuationAt
            (runtimeJointBalancePresentedEvent (depth + stage))).trace
        rw [runtimeJointShiftContinuationAt_balance]
        simpa [Nat.add_assoc] using membership

theorem runtimeJointFaithfulObservation_sourceBoundary_mem
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeJointSourceBoundaryPresentedEvent (depth + stage) ∈
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace := by
  apply runtimeJointFaithfulObservation_currentSeed_trace_subset
    observation nontrivial depth stage
  rw [runtimeJointRelationSeedAt_trace]
  simp

theorem runtimeJointFaithfulObservation_quarterIncidence_mem
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeJointQuarterIncidencePresentedEvent (depth + stage) ∈
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace := by
  apply runtimeJointFaithfulObservation_currentSeed_trace_subset
    observation nontrivial depth stage
  rw [runtimeJointRelationSeedAt_trace]
  simp

theorem runtimeJointFaithfulObservation_quarterSourceBoundary_mem
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeJointQuarterSourceBoundaryPresentedEvent (depth + stage) ∈
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace := by
  apply runtimeJointFaithfulObservation_currentSeed_trace_subset
    observation nontrivial depth stage
  rw [runtimeJointRelationSeedAt_trace]
  simp

theorem runtimeJointFaithfulObservation_quarterBoundaryEnergy_mem
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeJointQuarterBoundaryEnergyPresentedEvent (depth + stage) ∈
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace := by
  apply runtimeJointFaithfulObservation_currentSeed_trace_subset
    observation nontrivial depth stage
  rw [runtimeJointRelationSeedAt_trace]
  simp

theorem runtimeJointFaithfulObservation_quarterBalance_mem
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    runtimeJointQuarterBalancePresentedEvent (depth + stage) ∈
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace := by
  apply runtimeJointFaithfulObservation_currentSeed_trace_subset
    observation nontrivial depth stage
  rw [runtimeJointRelationSeedAt_trace]
  simp

def IsRuntimeJointStageRelation
    (relation : RuntimeJointRelationGenerator →₀ ℤ) : Prop :=
  ∃ stage,
    relation = runtimeJointIncidenceStageRelation stage ∨
      relation = runtimeJointSourceBoundaryStageRelation stage ∨
        relation = runtimeJointQuarterIncidenceStageRelation stage ∨
          relation = runtimeJointQuarterSourceBoundaryStageRelation stage ∨
            relation = runtimeJointQuarterBoundaryEnergyStageRelation stage ∨
              relation = runtimeJointQuarterBalanceStageRelation stage ∨
                relation = runtimeJointBalanceStageRelation stage

private theorem runtimeJointObservation_relation_generated
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat)
    (relation : RuntimeJointRelationGenerator →₀ ℤ)
    (membership : PresentedRelationEventAt.relation relation ∈
      ((runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observation stage).trace) :
    IsRuntimeJointStageRelation relation := by
  induction stage with
  | zero =>
      change PresentedRelationEventAt.relation relation ∈
        (runtimeJointRelationSeedAt
          (currentEffectStage
            (CanonicalUnitArithmeticRoot.finiteVisit depth).current)).trace
        at membership
      rw [currentEffectStage_finiteVisit,
        runtimeJointRelationSeedAt_trace] at membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with
        incidence | boundary | quarterIncidence | quarterBoundary |
          quarterBoundaryEnergy | quarterBalance | balance
      · exact ⟨depth, Or.inl
          (PresentedRelationEventAt.relation.inj incidence)⟩
      · exact ⟨depth, Or.inr <| Or.inl
          (PresentedRelationEventAt.relation.inj boundary)⟩
      · exact ⟨depth, Or.inr <| Or.inr <| Or.inl
          (PresentedRelationEventAt.relation.inj quarterIncidence)⟩
      · exact ⟨depth, Or.inr <| Or.inr <| Or.inr <| Or.inl
          (PresentedRelationEventAt.relation.inj quarterBoundary)⟩
      · exact ⟨depth, Or.inr <| Or.inr <| Or.inr <| Or.inr
          <| Or.inl
          (PresentedRelationEventAt.relation.inj quarterBoundaryEnergy)⟩
      · exact ⟨depth, Or.inr <| Or.inr <| Or.inr <| Or.inr
          <| Or.inr <| Or.inl
          (PresentedRelationEventAt.relation.inj quarterBalance)⟩
      · exact ⟨depth, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
          <| Or.inr
          (PresentedRelationEventAt.relation.inj balance)⟩
  | succ stage inductionHypothesis =>
      rw [RootGeneratedCofinalHistoryAt.observation_succ] at membership
      cases RootedAccountedUnfolding.trace_advance_cases
          (runtimeJointFaithfulStepAt observation nontrivial depth
            ).history.actualContinuation
          ((runtimeJointFaithfulStepAt observation nontrivial depth
            ).history.observation stage) _ membership with
      | inl old => exact inductionHypothesis old
      | inr generated =>
          obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
          rw [runtimeJointFaithfulObservation_frontier] at leaf_mem
          have leaf_eq : leaf =
              runtimeJointBalancePresentedEvent (depth + stage) :=
            List.mem_singleton.mp leaf_mem
          subst leaf
          change PresentedRelationEventAt.relation relation ∈
            (runtimeJointShiftContinuationAt
              (runtimeJointBalancePresentedEvent (depth + stage))).trace
            at generated_mem
          rw [runtimeJointShiftContinuationAt_balance_trace] at generated_mem
          simp only [List.mem_cons, List.not_mem_nil, or_false]
            at generated_mem
          rcases generated_mem with
            incidence | boundary | quarterIncidence | quarterBoundary |
              quarterBoundaryEnergy | quarterBalance | balance
          · exact ⟨depth + stage + 1, Or.inl
              (PresentedRelationEventAt.relation.inj incidence)⟩
          · exact ⟨depth + stage + 1, Or.inr <| Or.inl
              (PresentedRelationEventAt.relation.inj boundary)⟩
          · exact ⟨depth + stage + 1, Or.inr <| Or.inr <| Or.inl
              (PresentedRelationEventAt.relation.inj quarterIncidence)⟩
          · exact ⟨depth + stage + 1,
              Or.inr <| Or.inr <| Or.inr <| Or.inl
                (PresentedRelationEventAt.relation.inj quarterBoundary)⟩
          · exact ⟨depth + stage + 1,
              Or.inr <| Or.inr <| Or.inr <| Or.inr
                <| Or.inl
                (PresentedRelationEventAt.relation.inj quarterBoundaryEnergy)⟩
          · exact ⟨depth + stage + 1,
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
                <| Or.inl
                (PresentedRelationEventAt.relation.inj quarterBalance)⟩
          · exact ⟨depth + stage + 1,
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
                <| Or.inr
                (PresentedRelationEventAt.relation.inj balance)⟩

theorem runtimeJointObserved_relation_generated
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth historyStage : Nat)
    (relation : RuntimeJointRelationGenerator →₀ ℤ)
    (membership : PresentedRelationEventAt.relation relation ∈
      (runtimeJointFaithfulStepAt observation nontrivial depth
        ).history.observedEvents historyStage) :
    IsRuntimeJointStageRelation relation := by
  unfold RootGeneratedCofinalHistoryAt.observedEvents at membership
  obtain ⟨stage, _stage_mem, relation_mem⟩ :=
    List.mem_flatMap.mp membership
  exact runtimeJointObservation_relation_generated
    observation nontrivial depth stage relation relation_mem

theorem runtimeJointFaithful_freeEvaluation_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation =
        runtimeJointRelationEvaluator observation nontrivial :=
  rfl

theorem runtimeJointFaithful_freeEvaluation_incidence_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointIncidenceStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointIncidenceStageRelation stage) = 0
  exact runtimeJointIncidenceStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_freeEvaluation_sourceBoundary_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointSourceBoundaryStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointSourceBoundaryStageRelation stage) = 0
  exact runtimeJointSourceBoundaryStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_freeEvaluation_quarterIncidence_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointQuarterIncidenceStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointQuarterIncidenceStageRelation stage) = 0
  exact runtimeJointQuarterIncidenceStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_freeEvaluation_quarterSourceBoundary_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointQuarterSourceBoundaryStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointQuarterSourceBoundaryStageRelation stage) = 0
  exact runtimeJointQuarterSourceBoundaryStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_freeEvaluation_quarterBalance_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointQuarterBalanceStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointQuarterBalanceStageRelation stage) = 0
  exact runtimeJointQuarterBalanceStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_freeEvaluation_quarterBoundaryEnergy_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointQuarterBoundaryEnergyStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointQuarterBoundaryEnergyStageRelation stage) = 0
  exact runtimeJointQuarterBoundaryEnergyStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_freeEvaluation_balance_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth stage : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.freeEvaluation
        (runtimeJointBalanceStageRelation stage) = 0 := by
  change runtimeJointRelationEvaluator observation nontrivial
      (runtimeJointBalanceStageRelation stage) = 0
  exact runtimeJointBalanceStageRelation_evaluates_zero
    observation nontrivial stage

theorem runtimeJointFaithful_relationsSound
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (runtimeJointFaithfulStepAt observation nontrivial depth
      ).faithful.RelationsSound := by
  apply iSup_le
  intro historyStage
  apply Submodule.span_le.mpr
  intro relation relationEvent
  obtain ⟨stage,
      incidence | boundary | quarterIncidence | quarterBoundary |
        quarterBoundaryEnergy | quarterBalance | balance⟩ :=
    runtimeJointObserved_relation_generated observation nontrivial depth
      historyStage relation relationEvent
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_incidence_zero
      observation nontrivial depth stage
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_sourceBoundary_zero
      observation nontrivial depth stage
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_quarterIncidence_zero
      observation nontrivial depth stage
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_quarterSourceBoundary_zero
      observation nontrivial depth stage
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_quarterBoundaryEnergy_zero
      observation nontrivial depth stage
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_quarterBalance_zero
      observation nontrivial depth stage
  · subst relation
    exact runtimeJointFaithful_freeEvaluation_balance_zero
      observation nontrivial depth stage

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
