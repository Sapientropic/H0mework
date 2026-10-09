import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.ExponentialNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Powers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem exponential_128_parts (A : Matrix ι ι ℂ) :
    NormedSpace.exp A=(NormedSpace.exp ((1/128 : ℝ) • A))^128 := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  rw [← NormedSpace.exp_nsmul]
  congr 1
  ext i j
  simp [Matrix.smul_apply,Complex.real_smul]

omit [Nonempty ι] in
theorem scaled_exponential_size (H : Matrix ι ι ℂ) (size : ‖H‖ ≤ 20) :
    ‖(1/128 : ℝ) • (-H)‖ ≤ (5/32 : ℝ) := by
  rw [norm_smul,norm_neg,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/128)]
  nlinarith

theorem source_exponential_comparison (H K : Matrix ι ι ℂ)
    (normH : ‖H‖ ≤ 20) (normK : ‖K‖ ≤ 20) (distance : ‖H-K‖ ≤ (21/10^12 : ℝ)) :
    ‖NormedSpace.exp (-H)-NormedSpace.exp (-K)‖ ≤ (1/50 : ℝ) := by
  have smallH := scaled_exponential_size H normH
  have smallK := scaled_exponential_size K normK
  have difference : ‖(1/128 : ℝ) • (-H)-(1/128 : ℝ) • (-K)‖ ≤ (21/10^12 : ℝ)/128 := by
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/128)]
    have same : -H-(-K)=-(H-K) := by abel
    rw [same,norm_neg]
    nlinarith
  have step := small_exponential_error _ _ (5/32) ((21/10^12)/128) (by norm_num) (by norm_num) (by norm_num) smallH smallK difference
  have paid := power_error (NormedSpace.exp ((1/128 : ℝ) • (-H))) (NormedSpace.exp ((1/128 : ℝ) • (-K)))
    (117/100) (((21/10^12)/128)/(1-5/32)^2) (by norm_num) (by norm_num)
    (small_exponential_norm _ smallH) (small_exponential_norm _ smallK) step 128
  rw [exponential_128_parts (-H),exponential_128_parts (-K)]
  exact paid.trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
