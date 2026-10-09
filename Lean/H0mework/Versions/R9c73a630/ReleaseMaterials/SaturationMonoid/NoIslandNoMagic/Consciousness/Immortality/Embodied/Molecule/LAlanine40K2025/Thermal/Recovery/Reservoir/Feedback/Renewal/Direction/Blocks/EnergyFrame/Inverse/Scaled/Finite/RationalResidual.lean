import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*}

theorem cast_add (r i u v : Matrix ι ι ℚ) : cast (r+u) (i+v)=cast r i+cast u v := by
  ext a b
  simp only [cast,Matrix.add_apply,Rat.cast_add]
  ring

theorem cast_scale (c : ℚ) (r i : Matrix ι ι ℚ) : cast (c • r) (c • i)=(c : ℂ) • cast r i := by
  ext a b
  simp only [cast,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul]
  ring

theorem cast_one [DecidableEq ι] : cast (1 : Matrix ι ι ℚ) 0=(1 : Matrix ι ι ℂ) := by
  ext a b
  by_cases h : a=b <;> simp [cast,Matrix.one_apply,h]

def residualReal [Fintype ι] [DecidableEq ι] (r l m : Matrix ι ι ℚ) (mu delta sign : ℚ) : Matrix ι ι ℚ :=
  (mu-delta) • 1+sign • r-gramReal l m
def residualImag [Fintype ι] (i l m : Matrix ι ι ℚ) (sign : ℚ) : Matrix ι ι ℚ := sign • i-gramImag l m

theorem residual_cast [Fintype ι] [DecidableEq ι] (r i l m : Matrix ι ι ℚ) (mu delta sign : ℚ) :
    cast (residualReal r l m mu delta sign) (residualImag i l m sign)=
      ((mu-delta : ℚ) : ℂ) • (1 : Matrix ι ι ℂ)+(sign : ℂ) • cast r i-cast l m*(cast l m)ᴴ := by
  unfold residualReal residualImag
  rw [cast_sub,cast_gram]
  have split : sign • i=(mu-delta) • (0 : Matrix ι ι ℚ)+sign • i := by simp
  rw [split,cast_add,cast_scale,cast_scale,cast_one]

theorem residual_norm [Fintype ι] [DecidableEq ι] (r i l m : Matrix ι ι ℚ) (mu delta sign : ℚ) (positive : 0 ≤ delta)
    (checked : squareSum (residualReal r l m mu delta sign) (residualImag i l m sign) ≤ delta^2) :
    ‖((mu-delta : ℚ) : ℂ) • (1 : Matrix ι ι ℂ)+(sign : ℂ) • cast r i-cast l m*(cast l m)ᴴ‖ ≤ (delta : ℝ) := by
  rw [← residual_cast]
  exact norm_from_rational_square _ _ delta positive checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
