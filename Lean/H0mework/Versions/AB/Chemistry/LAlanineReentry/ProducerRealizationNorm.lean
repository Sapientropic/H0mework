import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNormData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem target_delta_entry (i j : Basis) :
    (Source.targetRealized - Source.currentRealized) i j =
      ((targetRealDelta i j : ℂ) + Complex.I * (targetImagDelta i j : ℂ)) / 1000000000000000 := by
  change ((Source.targetRealNumerator i j : ℂ) + Complex.I * (Source.targetImagNumerator i j : ℂ)) /
      1000000000000000 - Source.currentRealized i j = _
  rw [Source.currentRealized_channels]
  simp only [targetRealDelta, targetImagDelta, Int.cast_sub]
  ring

theorem target_delta_squared_sum :
    (∑ i : Basis, ∑ j : Basis, ‖(Source.targetRealized - Source.currentRealized) i j‖ ^ 2) =
      (targetDeltaSquareSum : ℝ) / 10 ^ 30 := by
  simp only [targetDeltaSquareSum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [target_delta_entry, norm_div, div_pow, Complex.sq_norm]
  norm_num [Complex.normSq_apply]
  ring

theorem target_delta_bound : ‖Source.targetRealized - Source.currentRealized‖ ≤ (86 : ℝ) / 10 ^ 12 := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  rw [target_delta_squared_sum, targetDeltaSquareSum_exact]
  norm_num

theorem realized_input_norm : ‖Source.currentRealized‖ < 11 := Runtime.reentryParent_realizedNorm

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
