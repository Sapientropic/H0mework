import H0mework.Versions.X.Fock.SourceHistoryClock.DecoderFiniteSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointFiniteDecoder

noncomputable section

local instance rangeComplete (bound : Nat) : CompleteSpace (action bound).range :=
  (source_antilipschitz bound).completeSpace_range_clm

abbrev inclusion (bound : Nat) : (action bound).range →ₗᵢ[ℂ] SourceJointClockGraph.Carrier :=
  (action bound).range.subtypeₗᵢ

def sourceEquiv (bound : Nat) : Space bound ≃L[ℂ] (action bound).range :=
  (action bound).equivRange (source_injective bound) (source_closed_range bound)

def decode (bound : Nat) : SourceJointClockGraph.Carrier →L[ℂ] Space bound :=
  (sourceEquiv bound).symm.toContinuousLinearMap.comp (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (action bound).range) (inclusion bound))

abbrev residual (bound : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  IsometricRetainedTransfer.residual (Current := SourceJointClockGraph.Carrier) (Next := (action bound).range) (inclusion bound)

theorem source_equiv_value (bound : Nat) (value : Space bound) :
    inclusion bound (sourceEquiv bound value) = action bound value := rfl

theorem decode_action (bound : Nat) (value : Space bound) : decode bound (action bound value) = value := by
  rw [← source_equiv_value]
  change (sourceEquiv bound).symm
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (action bound).range) (inclusion bound) (inclusion bound (sourceEquiv bound value))) = value
  rw [IsometricRetainedTransfer.transfer_pullback, ContinuousLinearEquiv.symm_apply_apply]

theorem encoded_decode (bound : Nat) (target : SourceJointClockGraph.Carrier) :
    action bound (decode bound target) =
      inclusion bound (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (action bound).range) (inclusion bound) target) := by
  rw [← source_equiv_value]
  change inclusion bound ((sourceEquiv bound) ((sourceEquiv bound).symm
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (action bound).range) (inclusion bound) target))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem residual_action (bound : Nat) (value : Space bound) : residual bound (action bound value) = 0 := by
  change action bound value - inclusion bound
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (action bound).range) (inclusion bound) (action bound value)) = 0
  rw [← encoded_decode, decode_action, sub_self]

theorem error_decomposition (bound : Nat) (target : SourceJointClockGraph.Carrier) (proposal : Space bound) :
    ‖target - action bound proposal‖ ^ 2 = ‖residual bound target‖ ^ 2 +
      ‖action bound (decode bound target - proposal)‖ ^ 2 := by
  have original := IsometricRetainedTransfer.decoder_error_decomposition (inclusion bound) target
    (sourceEquiv bound proposal)
  rw [source_equiv_value] at original
  apply original.trans
  congr 1
  rw [← (inclusion bound).norm_map]
  rw [map_sub, source_equiv_value, ← encoded_decode, ← map_sub]

theorem source_minimum_cost (bound : Nat) (target : SourceJointClockGraph.Carrier) :
    ‖target - action bound (decode bound target)‖ ^ 2 = ‖residual bound target‖ ^ 2 := by
  rw [error_decomposition, sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem decoder_lower (bound : Nat) (target : SourceJointClockGraph.Carrier) (proposal : Space bound) :
    ‖residual bound target‖ ^ 2 ≤ ‖target - action bound proposal‖ ^ 2 := by
  rw [error_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem minimum_fibre (bound : Nat) (target : SourceJointClockGraph.Carrier) (proposal : Space bound) :
    ‖target - action bound proposal‖ ^ 2 = ‖residual bound target‖ ^ 2 ↔ proposal = decode bound target := by
  constructor
  · intro attained
    rw [error_decomposition] at attained
    have zeroNorm : ‖action bound (decode bound target - proposal)‖ ^ 2 = 0 := by linarith only [attained]
    have zero := norm_eq_zero.mp (sq_eq_zero_iff.mp zeroNorm)
    have sourceZero := source_injective bound (zero.trans (map_zero _).symm)
    exact (sub_eq_zero.mp sourceZero).symm
  · rintro rfl
    exact source_minimum_cost bound target

theorem source_minimum (bound : Nat) (target : SourceJointClockGraph.Carrier) :
    IsMinOn (fun proposal => ‖target - action bound proposal‖ ^ 2) Set.univ (decode bound target) := by
  apply isMinOn_univ_iff.mpr
  intro proposal
  rw [source_minimum_cost]
  exact decoder_lower bound target proposal

end
end SourceJointFiniteDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
