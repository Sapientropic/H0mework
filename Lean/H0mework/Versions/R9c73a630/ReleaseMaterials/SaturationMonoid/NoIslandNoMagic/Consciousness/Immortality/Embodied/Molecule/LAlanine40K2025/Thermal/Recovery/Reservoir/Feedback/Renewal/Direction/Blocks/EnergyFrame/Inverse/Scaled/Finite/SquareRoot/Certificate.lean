import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Rational

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι]

structure RootGram (a b : Matrix ι ι ℚ) where
  realPart : Matrix ι ι ℚ
  imagPart : Matrix ι ι ℚ
  checked : squareSum (a-squareReal realPart imagPart) (b-squareImag realPart imagPart) ≤ ((2/10^7 : ℚ)*(2/10^7))^2

def RootGram.value {a b : Matrix ι ι ℚ} (G : RootGram a b) : Matrix ι ι ℂ :=
  cast G.realPart G.imagPart*(cast G.realPart G.imagPart)ᴴ

theorem RootGram.positive {a b : Matrix ι ι ℚ} (G : RootGram a b) : G.value.PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem RootGram.error [DecidableEq ι] {a b : Matrix ι ι ℚ} (G : RootGram a b) (positive : 0 ≤ cast a b) :
    ‖CFC.sqrt (cast a b)-G.value‖ ≤ (2/10^7 : ℝ) := by
  have paid := rational_gram_root a b G.realPart G.imagPart positive (2/10^7) (by norm_num) G.checked
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,RootGram.value] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
