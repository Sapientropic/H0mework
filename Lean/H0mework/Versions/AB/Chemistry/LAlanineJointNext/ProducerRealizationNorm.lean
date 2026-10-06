import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerNormData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem target_delta_entry (i j : Basis) :
    (Source.targetRealized - HeldForce.Source.realizedHeld) i j =
      ((targetRealDelta i j : ℂ) + Complex.I * (Source.targetImagNumerator i j : ℂ)) / 1000000000000000 := by
  change ((Source.targetRealNumerator i j : ℂ) + Complex.I * (Source.targetImagNumerator i j : ℂ)) /
      1000000000000000 - (HeldForce.Source.gammaNumerator i j : ℂ) / 1000000000000 = _
  simp only [targetRealDelta, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring

theorem target_delta_squared_sum :
    (∑ i : Basis, ∑ j : Basis, ‖(Source.targetRealized - HeldForce.Source.realizedHeld) i j‖ ^ 2) =
      (targetDeltaSquareSum : ℝ) / 10 ^ 30 := by
  simp only [targetDeltaSquareSum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [target_delta_entry, norm_div, div_pow, Complex.sq_norm]
  norm_num [Complex.normSq_apply]
  ring

theorem target_delta_bound :
    ‖Source.targetRealized - HeldForce.Source.realizedHeld‖ ≤ (53 : ℝ) / 10 ^ 12 := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  rw [target_delta_squared_sum, targetDeltaSquareSum_exact]
  norm_num

theorem realized_input_norm : ‖HeldForce.Source.realizedHeld‖ < 11 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub HeldForce.Source.realizedHeld
    ElectronicFrame.Producer.heldMatrix 0
  simp only [sub_zero] at triangle
  have difference := HeldForce.Producer.realized_delta_norm
  have initial := ElectronicFrame.Producer.heldMatrix_norm_le_ten
  linarith

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
