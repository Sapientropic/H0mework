import H0mework.Physics.LowEnergy.Quantum.WavepacketFiltration
import Mathlib.RingTheory.Nilpotent.Exp

/-! The same finite polynomial used by the differential consumer has a
two-sided inverse. No Hilbert adjoint or convergence of an infinite series
is used. -/
set_option autoImplicit false
namespace SourceMagnusExponential
open SourceMagnusDerivative SourceWavepacketFiltration
open scoped BigOperators
noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R] [Module ℚ R]

theorem exponential_eq_partial (x : R) (k : ℕ) (vanishes : x ^ k = 0) :
    IsNilpotent.exp x = partialExp k x := by
  rw [IsNilpotent.exp_eq_sum vanishes]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [term, Rat.cast_inv, Rat.cast_natCast] using
    ratCast_smul_eq ℚ ℂ ((i.factorial : ℚ)⁻¹) (x^i)

theorem partial_inverse (x : R) (k : ℕ) (vanishes : x ^ k = 0) :
    partialExp k x * partialExp k (-x) = 1 ∧
      partialExp k (-x) * partialExp k x = 1 := by
  have neg_vanishes : (-x)^k = 0 := by rw [neg_pow, vanishes, mul_zero]
  rw [← exponential_eq_partial x k vanishes, ← exponential_eq_partial (-x) k neg_vanishes]
  exact ⟨IsNilpotent.exp_mul_exp_neg_self ⟨k, vanishes⟩,
    IsNilpotent.exp_neg_mul_exp_self ⟨k, vanishes⟩⟩

section Configuration
variable {Ω B : Type*} [AddCommGroup B] [Module ℂ B]
variable [Module ℚ (Module.End ℂ (Ω → B))]

theorem graded_inverse (weight : Ω → ℕ) (N : ℕ) (bound : ∀ x, weight x ≤ N)
    (X : Module.End ℂ (Ω → B)) (raises : Raises weight 1 X) :
    partialExp (N+1) X * partialExp (N+1) (-X) = 1 ∧
      partialExp (N+1) (-X) * partialExp (N+1) X = 1 := by
  apply partial_inverse
  apply raises_above_bound_zero weight N ((N+1)*1) bound (by omega)
  exact raises_pow weight 1 X raises (N+1)

theorem graded_log_factorization (weight : Ω → ℕ) (N : ℕ) (bound : ∀ x, weight x ≤ N)
    (X Y : Module.End ℂ (Ω → B)) (linear : Raises weight 1 X)
    (quadratic : Raises weight 2 Y) (commute : Commute X Y) :
    partialExp (N+1) (X+Y) = partialExp (N+1) X * partialExp (N+1) Y := by
  have two := raises_mono weight 1 2 (by omega) Y quadratic
  have nilX : X^(N+1) = 0 :=
    raises_above_bound_zero weight N ((N+1)*1) bound (by omega) _
      (raises_pow weight 1 X linear (N+1))
  have nilY : Y^(N+1) = 0 :=
    raises_above_bound_zero weight N ((N+1)*1) bound (by omega) _
      (raises_pow weight 1 Y two (N+1))
  have nilSum : (X+Y)^(N+1) = 0 :=
    raises_above_bound_zero weight N ((N+1)*1) bound (by omega) _
      (raises_pow weight 1 (X+Y) (raises_add weight 1 X Y linear two) (N+1))
  rw [← exponential_eq_partial _ _ nilSum, ← exponential_eq_partial _ _ nilX,
    ← exponential_eq_partial _ _ nilY]
  exact IsNilpotent.exp_add_of_commute commute ⟨N+1, nilX⟩ ⟨N+1, nilY⟩

end Configuration
end
end SourceMagnusExponential
