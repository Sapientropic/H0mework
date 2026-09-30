import H0mework.Physics.LowEnergy.Quantum.MagnusExponential

/-! The exact weighted monomials consumed by the executable fixed-N action. -/
set_option autoImplicit false
namespace SourceMagnusTriangle
open SourceMagnusDerivative SourceWavepacketFiltration SourceMagnusExponential
open scoped BigOperators
noncomputable section
variable {Ω B : Type*} [AddCommGroup B] [Module ℂ B]
variable [Module ℚ (Module.End ℂ (Ω → B))]

omit [Module ℚ (Module.End ℂ (Ω → B))] in
theorem weighted_monomial_zero (weight : Ω → ℕ) (N : ℕ) (bound : ∀ x, weight x ≤ N)
    (X Y : Module.End ℂ (Ω → B)) (linear : Raises weight 1 X)
    (quadratic : Raises weight 2 Y) (r q : ℕ) (high : N < r+2*q) : X^r * Y^q = 0 := by
  apply raises_above_bound_zero weight N (r*1+q*2) bound (by omega)
  exact raises_mul weight (r*1) (q*2) _ _ (raises_pow weight 1 X linear r)
    (raises_pow weight 2 Y quadratic q)

theorem triangle_expansion (weight : Ω → ℕ) (N : ℕ) (bound : ∀ x, weight x ≤ N)
    (X Y : Module.End ℂ (Ω → B)) (linear : Raises weight 1 X)
    (quadratic : Raises weight 2 Y) (commute : Commute X Y) :
    partialExp (N+1) (X+Y) =
      ∑ r ∈ Finset.range (N+1), ∑ q ∈ Finset.range (N+1),
        if r+2*q ≤ N then ((r.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹) • (X^r*Y^q)
        else 0 := by
  rw [graded_log_factorization weight N bound X Y linear quadratic commute]
  simp only [partialExp, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  by_cases within : r+2*q ≤ N
  · simp only [within, if_true, term, smul_mul_smul]
  · simp only [within, if_false, term, smul_mul_smul,
      weighted_monomial_zero weight N bound X Y linear quadratic r q (by omega), smul_zero]

end
end SourceMagnusTriangle
