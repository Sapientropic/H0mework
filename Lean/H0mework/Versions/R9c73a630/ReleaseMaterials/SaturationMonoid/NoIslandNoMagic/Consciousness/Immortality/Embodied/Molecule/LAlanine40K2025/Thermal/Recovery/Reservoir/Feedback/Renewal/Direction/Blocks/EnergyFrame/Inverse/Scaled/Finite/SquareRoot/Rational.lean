import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squareReal (l m : Matrix ι ι ℚ) : Matrix ι ι ℚ := gramReal (gramReal l m) (gramImag l m)
def squareImag (l m : Matrix ι ι ℚ) : Matrix ι ι ℚ := gramImag (gramReal l m) (gramImag l m)

omit [DecidableEq ι] in
theorem square_cast (l m : Matrix ι ι ℚ) : cast (squareReal l m) (squareImag l m)=
    (cast l m*(cast l m)ᴴ)*(cast l m*(cast l m)ᴴ) := by
  simp only [squareReal,squareImag,cast_gram,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem rational_gram_root (a b l m : Matrix ι ι ℚ) (positive : 0 ≤ cast a b) (d : ℚ) (dpos : 0 ≤ d)
    (checked : squareSum (a-squareReal l m) (b-squareImag l m) ≤ (d*d)^2) :
    ‖CFC.sqrt (cast a b)-cast l m*(cast l m)ᴴ‖ ≤ (d : ℝ) := by
  apply root_gram_residual (cast a b) (cast l m) positive (d : ℝ) (by exact_mod_cast dpos)
  have paid := norm_from_rational_square (a-squareReal l m) (b-squareImag l m) (d*d) (mul_nonneg dpos dpos) checked
  rw [cast_sub,square_cast] at paid
  simpa only [Rat.cast_mul] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
