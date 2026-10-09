import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.RawCoordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem tensor_energy_norm (O : Matrix (ι × κ) (ι × κ) ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hermitian : A.IsHermitian) (positive : B.PosSemidef) :
    |energy O (Matrix.kronecker A B)| ≤ (Fintype.card ι : ℝ)*‖A‖*‖O‖*B.trace.re := by
  let P := ‖A‖ • (1 : Matrix ι ι ℂ)+A
  let Q := ‖A‖ • (1 : Matrix ι ι ℂ)-A
  have up := hermitian.isSelfAdjoint.le_algebraMap_norm_self
  have down := hermitian.neg.isSelfAdjoint.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at up down
  rw [norm_neg] at down
  have ppos : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (by
    have paid := sub_nonneg.mpr down
    simpa only [sub_neg_eq_add] using paid)
  have qpos : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr up)
  have delta : Matrix.kronecker P B-Matrix.kronecker Q B=(2 : ℝ) • Matrix.kronecker A B := by
    ext i j
    simp only [P,Q,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.add_apply,Matrix.sub_apply,
      Matrix.smul_apply,Complex.real_smul]
    push_cast
    ring
  have sum : P+Q=(2*‖A‖) • (1 : Matrix ι ι ℂ) := by dsimp [P,Q]; module
  have totalTrace : (Matrix.kronecker P B).trace.re+(Matrix.kronecker Q B).trace.re=
      2*(Fintype.card ι : ℝ)*‖A‖*B.trace.re := by
    simp only [Matrix.kronecker,Matrix.trace_kronecker]
    rw [← Complex.add_re,← add_mul,← Matrix.trace_add,sum,Matrix.trace_smul,Matrix.trace_one]
    simp only [Complex.mul_re,Complex.smul_re,Complex.smul_im,Complex.natCast_re,Complex.natCast_im,smul_eq_mul,mul_zero,zero_mul,sub_zero]
    ring
  have read : energy O (Matrix.kronecker P B)-energy O (Matrix.kronecker Q B)=2*energy O (Matrix.kronecker A B) := by
    have subRead : energy O (Matrix.kronecker P B)-energy O (Matrix.kronecker Q B)=energy O (Matrix.kronecker P B-Matrix.kronecker Q B) := by
      simp only [energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
    rw [subRead,delta,energy_real_smul]
  have triangle : 2*|energy O (Matrix.kronecker A B)| ≤ |energy O (Matrix.kronecker P B)|+|energy O (Matrix.kronecker Q B)| := by
    have paid := abs_add_le (energy O (Matrix.kronecker P B)) (-energy O (Matrix.kronecker Q B))
    rw [← sub_eq_add_neg,read,abs_mul] at paid
    simpa only [abs_neg,abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using paid
  have bounded := add_le_add (energy_norm_mass O _ (ppos.kronecker positive)) (energy_norm_mass O _ (qpos.kronecker positive))
  simp only [Matrix.kronecker] at totalTrace triangle ⊢
  rw [← mul_add,totalTrace] at bounded
  nlinarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
