import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedAt (tau mu : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((1/2 : ℝ) : ℂ) • 1+((1/(2*(tau+mu)) : ℝ) : ℂ) • A

theorem normalization_error (tau mu epsilon : ℝ) (A : Matrix ι ι ℂ) (positive : 0 < tau)
    (upper : ‖A‖ ≤ mu) (gap : mu-‖A‖ ≤ epsilon) :
    ‖scaledEffect tau A-normalizedAt tau mu A‖ ≤ epsilon/(2*(tau+mu)) := by
  let a := tau+‖A‖
  let b := tau+mu
  have ap : 0 < a := by dsimp only [a]; positivity
  have bp : 0 < b := by dsimp only [b]; linarith [norm_nonneg A]
  have ep : 0 ≤ epsilon := (sub_nonneg.mpr upper).trans gap
  have coefficient : 1/(2*a)-1/(2*b)=(mu-‖A‖)/(2*a*b) := by
    dsimp only [a,b]
    field_simp [show tau+‖A‖ ≠ 0 from ne_of_gt ap,show tau+mu ≠ 0 from ne_of_gt bp]
    ring
  have split : scaledEffect tau A-normalizedAt tau mu A=
      ((1/(2*a)-1/(2*b) : ℝ) : ℂ) • A := by
    simp only [scaledEffect,normalizedAt,a,b,Complex.ofReal_sub,sub_smul]
    abel
  rw [split,norm_smul,Complex.norm_real,Real.norm_eq_abs,coefficient,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr upper) (by positivity)),div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*a*b)).mpr
  have size : ‖A‖ ≤ a := by dsimp only [a]; linarith
  calc
    (mu-‖A‖)*‖A‖ ≤ epsilon*a := mul_le_mul gap size (norm_nonneg A) ep
    _ = _ := by change epsilon*a=epsilon/(2*b)*(2*a*b); field_simp [ne_of_gt bp]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
