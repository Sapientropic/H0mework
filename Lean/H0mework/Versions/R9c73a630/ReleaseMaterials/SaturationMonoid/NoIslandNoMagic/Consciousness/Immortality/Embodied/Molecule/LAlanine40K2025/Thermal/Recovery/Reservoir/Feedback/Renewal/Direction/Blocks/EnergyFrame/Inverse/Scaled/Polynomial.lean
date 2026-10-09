import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Core
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Trigonometry

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Collision Load.Source Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def cosineHat : ℝ := sinePolynomial (nativeClockStep : ℝ)
def sineHat : ℝ := cosinePolynomial (nativeClockStep : ℝ)

theorem polynomial_bounds : |cosineHat| ≤ 2 ∧ |sineHat| ≤ 2 := by
  have left := abs_sub (Real.cos BasisInverse.actualAngle) (Real.cos BasisInverse.actualAngle-cosineHat)
  have right := abs_sub (Real.sin BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle-sineHat)
  simp only [sub_sub_cancel] at left right
  have errors := source_polynomial_error
  change |Real.cos BasisInverse.actualAngle-cosineHat| ≤ _ ∧ |Real.sin BasisInverse.actualAngle-sineHat| ≤ _ at errors
  constructor <;> linarith [Real.abs_cos_le_one BasisInverse.actualAngle,Real.abs_sin_le_one BasisInverse.actualAngle]

private theorem square_difference (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 2)
    (paid : |a-b| ≤ (1/10^18 : ℝ)) : |a^2-b^2| ≤ (3/10^18 : ℝ) := by
  rw [show a^2-b^2=(a-b)*(a+b) by ring,abs_mul]
  have sum : |a+b| ≤ 3 := (abs_add_le a b).trans (by linarith)
  have bound := mul_le_mul paid sum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/10^18)
  linarith

theorem cosine_square_error : |(Real.cos BasisInverse.actualAngle)^2-cosineHat^2| ≤ (3/10^18 : ℝ) :=
  square_difference _ _ (Real.abs_cos_le_one _) polynomial_bounds.1 source_polynomial_error.1

theorem sine_square_error : |(Real.sin BasisInverse.actualAngle)^2-sineHat^2| ≤ (3/10^18 : ℝ) :=
  square_difference _ _ (Real.abs_sin_le_one _) polynomial_bounds.2 source_polynomial_error.2

theorem sine_cosine_error : |Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle-cosineHat*sineHat| ≤
    (3/10^18 : ℝ) := by
  have split : Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle-cosineHat*sineHat=
      Real.cos BasisInverse.actualAngle*(Real.sin BasisInverse.actualAngle-sineHat)+
      (Real.cos BasisInverse.actualAngle-cosineHat)*sineHat := by ring
  rw [split]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  have first := mul_le_mul (Real.abs_cos_le_one BasisInverse.actualAngle) source_polynomial_error.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have second := mul_le_mul source_polynomial_error.1 polynomial_bounds.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/10^18)
  change |Real.cos BasisInverse.actualAngle| * |Real.sin BasisInverse.actualAngle-sineHat| ≤ _ at first
  change |Real.cos BasisInverse.actualAngle-cosineHat| * |sineHat| ≤ _ at second
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
