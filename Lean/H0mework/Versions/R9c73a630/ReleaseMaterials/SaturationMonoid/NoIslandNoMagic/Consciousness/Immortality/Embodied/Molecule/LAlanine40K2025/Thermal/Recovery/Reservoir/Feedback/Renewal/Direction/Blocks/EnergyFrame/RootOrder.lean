import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Measurement
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive spectral floor controls a noncommuting square-root perturbation. -/
theorem sqrt_order_step (A B : Matrix ι ι ℂ) (positiveB : 0 ≤ B)
    (r d : ℝ) (dpos : 0 ≤ d)
    (floor : r • (1 : Matrix ι ι ℂ) ≤ CFC.sqrt B)
    (paid : A-B ≤ (2*r*d) • (1 : Matrix ι ι ℂ)) :
    CFC.sqrt A-CFC.sqrt B ≤ d • (1 : Matrix ι ι ℂ) := by
  have root := CFC.sqrt_nonneg B
  have scaled : (2*d*r) • (1 : Matrix ι ι ℂ) ≤ (2*d) • CFC.sqrt B := by
    simpa only [smul_smul] using smul_le_smul_of_nonneg_left floor (by positivity : (0 : ℝ) ≤ 2*d)
  have squarePositive : (0 : Matrix ι ι ℂ) ≤ (d*d) • (1 : Matrix ι ι ℂ) :=
    smul_nonneg (mul_nonneg dpos dpos) zero_le_one
  have square : (CFC.sqrt B+d • (1 : Matrix ι ι ℂ))*(CFC.sqrt B+d • 1) =
      B+(2*d) • CFC.sqrt B+(d*d) • (1 : Matrix ι ι ℂ) := by
    rw [add_mul,mul_add,mul_add,CFC.sqrt_mul_sqrt_self B positiveB]
    simp only [mul_smul_comm,smul_mul_assoc,one_mul,mul_one,smul_smul]
    module
  have first : A ≤ B+(2*d*r) • (1 : Matrix ι ι ℂ) := by
    have h := (sub_le_iff_le_add).mp paid
    simpa only [add_comm,mul_assoc,mul_comm,mul_left_comm] using h
  have bound : A ≤ (CFC.sqrt B+d • (1 : Matrix ι ι ℂ))*(CFC.sqrt B+d • 1) := by
    rw [square]
    exact first.trans ((add_le_add_right scaled B).trans (le_add_of_nonneg_right squarePositive))
  have roots := CFC.sqrt_le_sqrt A _ bound
  rw [CFC.sqrt_mul_self _ (add_nonneg root (smul_nonneg dpos zero_le_one))] at roots
  exact (sub_le_iff_le_add).mpr (by simpa only [add_comm] using roots)

theorem self_adjoint_norm_of_sides (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian)
    (d : ℝ) (nonnegative : 0 ≤ d)
    (upper : A ≤ d • (1 : Matrix ι ι ℂ)) (lower : -d • (1 : Matrix ι ι ℂ) ≤ A) : ‖A‖ ≤ d := by
  nontriviality (Matrix ι ι ℂ) using (by simpa only [Subsingleton.elim A 0,norm_zero] using nonnegative)
  have up : A ≤ algebraMap ℝ (Matrix ι ι ℂ) d := by simpa only [Algebra.algebraMap_eq_smul_one] using upper
  have down : algebraMap ℝ (Matrix ι ι ℂ) (-d) ≤ A := by simpa only [Algebra.algebraMap_eq_smul_one] using lower
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hermitian.isSelfAdjoint with positive | negative
  · exact (le_algebraMap_iff_spectrum_le hermitian.isSelfAdjoint).mp up _ positive
  · have h := (algebraMap_le_iff_le_spectrum hermitian.isSelfAdjoint).mp down _ negative
    linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
