import H0mework.Fock.CopyGraph.DecoderInverse

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]
attribute [local instance] imageComplete

theorem error_decomposition (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) (proposal : Space (observed (historyPMF bound) observer)) :
    ‖target - action depth bound index observer proposal‖ ^ 2 = ‖residual depth bound index observer target‖ ^ 2 +
      ‖action depth bound index observer (decode depth bound index observer target - proposal)‖ ^ 2 := by
  have original := IsometricRetainedTransfer.decoder_error_decomposition (Source := SourceJointClockGraph.Carrier)
    (Observed := (action depth bound index observer).range) (inclusion depth bound index observer) target
    (sourceEquiv depth bound index observer proposal)
  rw [source_equiv_value] at original
  apply original.trans
  congr 1
  rw [← (inclusion depth bound index observer).norm_map]
  rw [map_sub, source_equiv_value, ← encoded_decode, ← map_sub]

theorem minimum_cost (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    ‖target - action depth bound index observer (decode depth bound index observer target)‖ ^ 2 =
      ‖residual depth bound index observer target‖ ^ 2 := by
  rw [error_decomposition, sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem decoder_lower (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) (proposal : Space (observed (historyPMF bound) observer)) :
    ‖residual depth bound index observer target‖ ^ 2 ≤ ‖target - action depth bound index observer proposal‖ ^ 2 := by
  rw [error_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem minimum_fibre (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) (proposal : Space (observed (historyPMF bound) observer)) :
    ‖target - action depth bound index observer proposal‖ ^ 2 = ‖residual depth bound index observer target‖ ^ 2 ↔
      proposal = decode depth bound index observer target := by
  constructor
  · intro attained
    rw [error_decomposition] at attained
    have zeroNorm : ‖action depth bound index observer (decode depth bound index observer target - proposal)‖ ^ 2 = 0 := by
      linarith only [attained]
    have zero := norm_eq_zero.mp (sq_eq_zero_iff.mp zeroNorm)
    have sourceZero := source_injective depth bound index observer (zero.trans (map_zero _).symm)
    exact (sub_eq_zero.mp sourceZero).symm
  · rintro rfl
    exact minimum_cost depth bound index observer target

theorem source_minimum (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    IsMinOn (fun proposal => ‖target - action depth bound index observer proposal‖ ^ 2)
      Set.univ (decode depth bound index observer target) := by
  apply isMinOn_univ_iff.mpr
  intro proposal
  rw [minimum_cost]
  exact decoder_lower depth bound index observer target proposal

theorem source_orthogonal (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) (proposal : Space (observed (historyPMF bound) observer)) :
    ⟪action depth bound index observer proposal, residual depth bound index observer target⟫_ℂ = 0 := by
  have original := IsometricRetainedTransfer.residual_orthogonal (Current := SourceJointClockGraph.Carrier)
    (Next := (action depth bound index observer).range) (inclusion depth bound index observer) target
    (sourceEquiv depth bound index observer proposal)
  exact (congrArg (fun value : SourceJointClockGraph.Carrier =>
    inner ℂ value (residual depth bound index observer target))
      (source_equiv_value depth bound index observer proposal)).symm.trans original

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
