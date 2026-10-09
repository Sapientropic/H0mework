import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Small
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exponential_norm (A : Matrix ι ι ℂ) (r : ℝ) (size : ‖A‖ ≤ r) :
    ‖NormedSpace.exp A‖ ≤ Real.exp r := by
  have scalar := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) r
  have series := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have bound (n : ℕ) : ‖((n.factorial : ℂ)⁻¹) • A^n‖ ≤ ((n.factorial : ℝ)⁻¹) • r^n := by
    rw [norm_smul,norm_inv,Complex.norm_natCast,smul_eq_mul]
    gcongr
    exact (norm_pow_le A n).trans (pow_le_pow_left₀ (norm_nonneg A) size n)
  have paid := tsum_of_norm_bounded scalar bound
  rw [series.tsum_eq,← Real.exp_eq_exp_ℝ] at paid
  exact paid

theorem small_exponential_norm (A : Matrix ι ι ℂ) (size : ‖A‖ ≤ (5/32 : ℝ)) :
    ‖NormedSpace.exp A‖ ≤ (117/100 : ℝ) := by
  apply (exponential_norm A (5/32) size).trans
  have bound := Real.exp_bound' (x := (5/32 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at bound ⊢
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
