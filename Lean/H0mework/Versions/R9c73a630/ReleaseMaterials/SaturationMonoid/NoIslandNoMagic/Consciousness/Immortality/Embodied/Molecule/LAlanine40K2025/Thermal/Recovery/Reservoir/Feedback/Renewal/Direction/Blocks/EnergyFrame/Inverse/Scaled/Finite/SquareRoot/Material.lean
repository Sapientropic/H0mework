import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Rational

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def effectScale : ℚ := 25370179991752913148924687658465822185689272007880723361208978865984139886740247403861761425614330851250000000/2437377361241906499158240765396156260576371263264654431471317699480928578035263395583044109091139004233313895071

theorem effect_scale_exact : (effectScale : ℝ)=1/(2*(rationalRegularizer+480362644764/10^10)) := by
  unfold rationalRegularizer
  rw [cosine_hat_exact]
  norm_num [effectScale]

variable {ι : Type*} [DecidableEq ι]
def effectReal (r : Matrix ι ι ℚ) (sign : ℚ) : Matrix ι ι ℚ := (1/2 : ℚ) • 1+(sign*effectScale) • r
def effectImag (i : Matrix ι ι ℚ) (sign : ℚ) : Matrix ι ι ℚ := (sign*effectScale) • i

theorem effect_cast (r i : Matrix ι ι ℚ) (sign : ℚ) : cast (effectReal r sign) (effectImag i sign)=
    normalizedAt rationalRegularizer (480362644764/10^10) ((sign : ℂ) • cast r i) := by
  have scale : (effectScale : ℂ)=((1/(2*(rationalRegularizer+480362644764/10^10)) : ℝ) : ℂ) := by exact_mod_cast effect_scale_exact
  unfold effectReal effectImag
  have split : (sign*effectScale) • i=(1/2 : ℚ) • (0 : Matrix ι ι ℚ)+(sign*effectScale) • i := by simp
  rw [split,cast_add,cast_scale,cast_scale,cast_one]
  simp only [normalizedAt,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,scale,smul_smul,Complex.ofReal_div,Complex.ofReal_ofNat]
  congr 1
  rw [mul_comm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
