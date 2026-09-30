import H0mework.Physics.LowEnergy.Quantum.MagnusTriangle
import H0mework.Physics.LowEnergy.Quantum.WavepacketCurrentAudit

/-! Source-grade consumers of the finite exponential on real-momentum waves.
No toy derivation is identified with physical differentiation in time. -/
set_option autoImplicit false
namespace SourceMagnusDerivativeAudit
open SourceWavepacketGrade SourceWavepacketInteraction SourceWavepacketCurrent
open SourceWavepacketAudit SourceMagnusDerivative SourceWavepacketFiltration
open SourceMagnusExponential SourceMagnusTriangle
open scoped BigOperators
noncomputable section

def weight (x : Config) : ℕ := occupation target x
def X : Module.End ℂ TestWave := current (fun p : ℝ => p-1) (sourceMatrix 0)

theorem actual_weight_bound (x : Config) : weight x ≤ 2 := occupation_bound target x

theorem actual_current_grade :
    grade weight * X = X * grade weight + X := by
  exact interaction_raises_occupation target _ _
    (scalarKernel_support target (sourceMatrix 0) 1 (source_matrix_grade 0))

theorem actual_current_raises : Raises weight 1 X := by
  apply raises_of_grade weight 2 1 actual_weight_bound
  simpa only [Nat.cast_one, one_smul] using actual_current_grade

theorem actual_quadratic_raises : Raises weight 2 (X^2) := by
  simpa only [Nat.mul_one] using raises_pow weight 1 X actual_current_raises 2

theorem actual_cubic_zero : X^3 = 0 := by
  apply raises_above_bound_zero weight 2 3 actual_weight_bound (by decide)
  simpa only [Nat.mul_one] using raises_pow weight 1 X actual_current_raises 3

theorem actual_quadratic_nonzero_readout :
    ((X^2) sameInternalWave) ![(2,1),(0,1)] = 12 := by
  simpa only [X, pow_two, Module.End.mul_apply] using
    SourceWavepacketCurrentAudit.actual_two_currents_survive

theorem actual_nilpotent_exp_identification : IsNilpotent.exp X = partialExp 3 X := by
  exact exponential_eq_partial X 3 actual_cubic_zero

theorem actual_two_sided_inverse :
    partialExp 3 X * partialExp 3 (-X) = 1 ∧
      partialExp 3 (-X) * partialExp 3 X = 1 := by
  exact graded_inverse weight 2 actual_weight_bound X actual_current_raises

theorem actual_log_terms_commute : Commute X (X^2) := by
  change X * X^2 = X^2 * X
  simp only [pow_two, mul_assoc]

theorem actual_mixed_log_factorization :
    partialExp 3 (X+X^2) = partialExp 3 X * partialExp 3 (X^2) := by
  exact graded_log_factorization weight 2 actual_weight_bound X (X^2)
    actual_current_raises actual_quadratic_raises actual_log_terms_commute

theorem actual_weighted_tail_zero (r q : ℕ) (high : 2 < r+2*q) : X^r * (X^2)^q = 0 := by
  exact weighted_monomial_zero weight 2 actual_weight_bound X (X^2)
    actual_current_raises actual_quadratic_raises r q high

theorem actual_weighted_triangle :
    partialExp 3 (X+X^2) =
      ∑ r ∈ Finset.range 3, ∑ q ∈ Finset.range 3,
        if r+2*q ≤ 2 then ((r.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) • (X^r*(X^2)^q)
        else 0 := by
  exact triangle_expansion weight 2 actual_weight_bound X (X^2)
    actual_current_raises actual_quadratic_raises actual_log_terms_commute

theorem actual_mixed_log_polynomial :
    partialExp 3 (X+X^2) = 1+X+(3/2 : ℂ) • X^2 := by
  rw [actual_weighted_triangle]
  norm_num [Finset.sum_range_succ]
  module

theorem actual_exponential_nonzero_second_order :
    (partialExp 3 X sameInternalWave) ![(2,1),(0,1)] = 6 := by
  norm_num [partialExp, term, Finset.sum_range_succ, X, current, interaction,
    pow_two, Module.End.mul_apply, lineAction, scalarKernel, sourceMatrix,
    sameInternalWave, Fin.sum_univ_two, Function.update_apply]

theorem actual_mixed_log_nonzero_quadratic :
    (partialExp 3 (X+X^2) sameInternalWave) ![(2,1),(0,1)] = 18 := by
  rw [actual_mixed_log_polynomial]
  norm_num [X, current, interaction, pow_two, Module.End.mul_apply, lineAction,
    scalarKernel, sourceMatrix, sameInternalWave, Fin.sum_univ_two, Function.update_apply]

#check SourceMagnusDerivative.finite_exp_derivative
#check SourceWavepacketFiltration.all_N_magnus_ODE
#print axioms SourceMagnusDerivative.derivative_power
#print axioms SourceMagnusDerivative.derivative_term
#print axioms SourceMagnusDerivative.derivative_partialExp
#print axioms SourceMagnusDerivative.finite_exp_derivative
#print axioms SourceMagnusDerivative.magnus_ODE
#print axioms SourceWavepacketFiltration.raises_of_grade
#print axioms SourceWavepacketFiltration.raises_mono
#print axioms SourceWavepacketFiltration.raises_add
#print axioms SourceWavepacketFiltration.raises_smul
#print axioms SourceWavepacketFiltration.raises_sub
#print axioms SourceWavepacketFiltration.raises_mul
#print axioms SourceWavepacketFiltration.raises_pow
#print axioms SourceWavepacketFiltration.raises_above_bound_zero
#print axioms SourceWavepacketFiltration.graded_magnus_ODE
#print axioms SourceWavepacketFiltration.all_N_magnus_ODE
#print axioms SourceMagnusExponential.exponential_eq_partial
#print axioms SourceMagnusExponential.partial_inverse
#print axioms SourceMagnusExponential.graded_inverse
#print axioms SourceMagnusExponential.graded_log_factorization
#print axioms SourceMagnusTriangle.weighted_monomial_zero
#print axioms SourceMagnusTriangle.triangle_expansion
#print axioms actual_weight_bound
#print axioms actual_current_grade
#print axioms actual_current_raises
#print axioms actual_quadratic_raises
#print axioms actual_cubic_zero
#print axioms actual_quadratic_nonzero_readout
#print axioms actual_nilpotent_exp_identification
#print axioms actual_two_sided_inverse
#print axioms actual_log_terms_commute
#print axioms actual_mixed_log_factorization
#print axioms actual_weighted_tail_zero
#print axioms actual_weighted_triangle
#print axioms actual_mixed_log_polynomial
#print axioms actual_exponential_nonzero_second_order
#print axioms actual_mixed_log_nonzero_quadratic

end
end SourceMagnusDerivativeAudit
