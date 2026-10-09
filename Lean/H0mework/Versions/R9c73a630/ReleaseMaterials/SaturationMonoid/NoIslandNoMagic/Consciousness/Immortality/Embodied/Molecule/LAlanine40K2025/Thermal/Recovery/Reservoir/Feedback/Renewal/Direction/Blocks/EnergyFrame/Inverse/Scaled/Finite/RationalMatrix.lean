import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*}

def cast (r i : Matrix ι κ ℚ) : Matrix ι κ ℂ := fun a b => (r a b : ℂ)+Complex.I*(i a b : ℂ)
def gramReal [Fintype κ] (r i : Matrix ι κ ℚ) : Matrix ι ι ℚ := fun a b => ∑ k, (r a k*r b k+i a k*i b k)
def gramImag [Fintype κ] (r i : Matrix ι κ ℚ) : Matrix ι ι ℚ := fun a b => ∑ k, (i a k*r b k-r a k*i b k)

theorem cast_gram [Fintype κ] (r i : Matrix ι κ ℚ) : cast (gramReal r i) (gramImag r i)=cast r i*(cast r i)ᴴ := by
  ext a b
  simp only [cast,gramReal,gramImag,Matrix.mul_apply,Matrix.conjTranspose_apply,Rat.cast_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  simp only [star_add,star_mul,star_ratCast,Complex.star_def,Complex.conj_I]
  linear_combination ((i a k : ℂ)*(i b k : ℂ))*Complex.I_sq

theorem cast_sub (r i u v : Matrix ι κ ℚ) : cast (r-u) (i-v)=cast r i-cast u v := by
  ext a b
  simp only [cast,Matrix.sub_apply,Rat.cast_sub]
  ring

theorem cast_norm_square (r i : Matrix ι κ ℚ) (a : ι) (b : κ) :
    ‖cast r i a b‖^2=((r a b^2+i a b^2 : ℚ) : ℝ) := by
  simp [cast,Complex.sq_norm,Complex.normSq_apply]
  ring

def squareSum [Fintype ι] (r i : Matrix ι ι ℚ) : ℚ := ∑ a, ∑ b, (r a b^2+i a b^2)

theorem norm_from_rational_square [Fintype ι] [DecidableEq ι] (r i : Matrix ι ι ℚ) (bound : ℚ) (nonnegative : 0 ≤ bound)
    (paid : squareSum r i ≤ bound^2) : ‖cast r i‖ ≤ (bound : ℝ) := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by exact_mod_cast nonnegative)
  simp_rw [cast_norm_square]
  unfold squareSum at paid
  exact_mod_cast paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
