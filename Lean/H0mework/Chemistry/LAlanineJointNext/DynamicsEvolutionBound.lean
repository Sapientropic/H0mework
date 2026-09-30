import H0mework.Chemistry.LAlanineJointNext.DynamicsJointEvolution
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.EvolutionBound

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem conjugated_hasDerivAt (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian)
    (current : Matrix Basis Basis ℂ) (time : ℝ) :
    HasDerivAt (fun t => Unitary.conjStarAlgAut ℂ _ (Math.frozenUnitary H hermitian t) current)
      (Unitary.conjStarAlgAut ℂ _ (Math.frozenUnitary H hermitian time)
        (-Complex.I • (H * current - current * H))) time := by
  have derivative := ((Math.frozenUnitary_hasDerivAt H hermitian time).mul_const current).mul
    (Math.frozenUnitary_hasDerivAt H hermitian time).star
  apply derivative.congr_deriv
  simp only [Unitary.conjStarAlgAut_apply, star_mul, star_smul,
    hermitian.isSelfAdjoint.star_eq, star_neg, Complex.star_def, Complex.conj_I,
    neg_neg, smul_mul_assoc, mul_smul_comm, smul_sub, mul_sub, sub_mul, mul_assoc]
  module

theorem conjugated_derivative_norm (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian)
    (current : Matrix Basis Basis ℂ) (time : ℝ) :
    ‖Unitary.conjStarAlgAut ℂ _ (Math.frozenUnitary H hermitian time)
      (-Complex.I • (H * current - current * H))‖ = ‖H * current - current * H‖ := by
  rw [StarAlgEquiv.norm_map, norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- Unitary conjugation keeps the derivative's commutator norm, for any retained matrix. -/
theorem frozen_conjugation_bound (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian)
    (current : Matrix Basis Basis ℂ) (time : ℝ) :
    ‖Unitary.conjStarAlgAut ℂ _ (Math.frozenUnitary H hermitian time) current - current‖ ≤
      |time| * ‖H * current - current * H‖ := by
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := time)
    (fun t _ => (conjugated_hasDerivAt H hermitian current t).hasDerivWithinAt)
    (fun t _ => (conjugated_derivative_norm H hermitian current t).le)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ 0) (Set.mem_univ time)
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Math.frozenUnitary_eq_exp,
    zero_smul, NormedSpace.exp_zero, one_mul, star_one, mul_one, sub_zero,
    Real.norm_eq_abs, mul_comm] using estimate

end
end LAlanine40K2025.JointNext.EvolutionBound
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
