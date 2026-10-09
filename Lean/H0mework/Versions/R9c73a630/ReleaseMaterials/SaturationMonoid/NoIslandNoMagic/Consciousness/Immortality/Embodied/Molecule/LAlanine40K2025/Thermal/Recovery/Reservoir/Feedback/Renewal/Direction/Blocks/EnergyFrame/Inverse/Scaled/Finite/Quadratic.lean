import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Error

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*}

def testState (v : ι → ℚ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (fun a => (v a : ℂ)) (star (fun a => (v a : ℂ)))
def testMass [Fintype ι] (v : ι → ℚ) : ℚ := ∑ a, v a^2
def testEnergy [Fintype ι] (r : Matrix ι ι ℚ) (v : ι → ℚ) : ℚ := ∑ a, ∑ b, r a b*v b*v a

theorem test_positive [Fintype ι] (v : ι → ℚ) : (testState v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem test_trace [Fintype ι] (v : ι → ℚ) : (testState v).trace.re=(testMass v : ℝ) := by
  simp only [testState,Matrix.trace_vecMulVec,dotProduct,Pi.star_apply,star_ratCast,Complex.re_sum]
  unfold testMass
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  norm_num [Complex.mul_re,pow_two]

theorem test_energy [Fintype ι] (r i : Matrix ι ι ℚ) (v : ι → ℚ) :
    energy (cast r i) (testState v)=(testEnergy r v : ℝ) := by
  simp only [energy,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Complex.re_sum,testState,Matrix.vecMulVec_apply,Pi.star_apply,star_ratCast]
  unfold testEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [cast,Complex.mul_re]
  ring

theorem norm_lower_from_test [Fintype ι] [DecidableEq ι] (r i : Matrix ι ι ℚ) (v : ι → ℚ) (lower : ℚ)
    (mass : 0 < testMass v) (paid : lower*testMass v ≤ -testEnergy r v) :
    (lower : ℝ) ≤ ‖cast r i‖ := by
  have bounded := energy_norm_mass (cast r i) (testState v) (test_positive v)
  rw [test_trace,test_energy] at bounded
  have signed := (neg_le_abs (testEnergy r v : ℝ)).trans bounded
  have exactPaid : (lower : ℝ)*(testMass v : ℝ) ≤ -(testEnergy r v : ℝ) := by exact_mod_cast paid
  exact le_of_mul_le_mul_right (exactPaid.trans signed) (show (0 : ℝ) < (testMass v : ℝ) by exact_mod_cast mass)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.RationalMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
