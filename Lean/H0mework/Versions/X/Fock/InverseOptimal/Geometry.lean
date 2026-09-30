import H0mework.Versions.X.Fock.InverseDistribution.LossSource
import H0mework.Realization.HilbertTransfer.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimal

open SourceGeneratedActionWords SourceCopyTimeModel
noncomputable section

theorem roundtrip (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let pullback := SourceGWordProgram.hilbertAction (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _)
    SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value) =
      WithLp.toLp 2 (WithLp.toLp 2
        (pullback (IsometricRetainedTransfer.transfer pullback (hilbert value)), mass value),
        SourceJointClockGraph.clock value) := by
  dsimp only
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  change WithLp.toLp 2 (WithLp.toLp 2
    (SourceGWordProgram.hilbertAction program (SourceCompiledWordOperator.slope_positive _)
      (IsometricRetainedTransfer.transfer (SourceGWordProgram.hilbertAction program (SourceCompiledWordOperator.slope_positive _))
        (hilbert value)), mass value),
      (program.1 : ℂ) * ((program.1 : ℂ)⁻¹ * (SourceJointClockGraph.clock value - (program.2 : ℂ) * mass value)) +
        (program.2 : ℂ) * mass value) = _
  rw [mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr (SourceCompiledWordOperator.slope_positive _).ne'), sub_add_cancel]

theorem residual (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let pullback := SourceGWordProgram.hilbertAction (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _)
    SourceGWordInverse.residual depth word value =
      WithLp.toLp 2 (WithLp.toLp 2 (IsometricRetainedTransfer.residual pullback (hilbert value), (0 : ℂ)), (0 : ℂ)) := by
  dsimp only
  change value - SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value) = _
  rw [roundtrip]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · exact sub_self _
  · exact sub_self _

theorem residual_norm (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    let pullback := SourceGWordProgram.hilbertAction (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _)
    ‖SourceGWordInverse.residual depth word value‖ ^ 2 =
      ‖IsometricRetainedTransfer.residual pullback (hilbert value)‖ ^ 2 := by
  dsimp only
  rw [residual, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change (‖IsometricRetainedTransfer.residual
    (SourceGWordProgram.hilbertAction (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _)) (hilbert value)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) + ‖(0 : ℂ)‖ ^ 2 = _
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem error_decomposition (depth : Nat) (word : List (Fock.Letter depth))
    (value candidate : SourceJointClockGraph.Carrier) :
    ‖value - SourceCompiledGWord.effect depth word candidate‖ ^ 2 =
      ‖SourceGWordInverse.residual depth word value‖ ^ 2 +
        ‖SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value - candidate)‖ ^ 2 := by
  rw [map_sub, roundtrip, residual_norm]
  simp only [WithLp.prod_norm_sq_eq_of_L2]
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  let pullback := SourceGWordProgram.hilbertAction program (SourceCompiledWordOperator.slope_positive _)
  change (‖hilbert value - pullback (hilbert candidate)‖ ^ 2 + ‖mass value - mass candidate‖ ^ 2) +
      ‖SourceJointClockGraph.clock value - ((program.1 : ℂ) * SourceJointClockGraph.clock candidate + (program.2 : ℂ) * mass candidate)‖ ^ 2 =
    ‖IsometricRetainedTransfer.residual pullback (hilbert value)‖ ^ 2 +
      ((‖pullback (IsometricRetainedTransfer.transfer pullback (hilbert value)) - pullback (hilbert candidate)‖ ^ 2 +
        ‖mass value - mass candidate‖ ^ 2) +
        ‖SourceJointClockGraph.clock value - ((program.1 : ℂ) * SourceJointClockGraph.clock candidate + (program.2 : ℂ) * mass candidate)‖ ^ 2)
  rw [← map_sub pullback (IsometricRetainedTransfer.transfer pullback (hilbert value)) (hilbert candidate),
    pullback.norm_map, IsometricRetainedTransfer.decoder_error_decomposition]
  ring

end
end SourceInverseDistributionOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
