import H0mework.Physics.LowEnergy.Quantum.ScalarMagnusAlgebra

/-! Noncommutative differentiation of the finite exponential. The derivative
is a linear map satisfying the ordinary product rule; no ODE conclusion is
assumed. This algebraic consumer is independent of a choice of state norm. -/
set_option autoImplicit false
namespace SourceMagnusDerivative
open scoped BigOperators
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem derivative_power (D : R →ₗ[ℂ] R)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (x y c : R) (derivative : D x = y)
    (commutator : x * y - y * x = c) (central : Commute x c) (n : ℕ) :
    D (x ^ (n + 2)) = ((n : ℂ) + 2) • (y * x ^ (n + 1)) +
      ((((n : ℂ) + 2) * ((n : ℂ) + 1)) / 2) • (c * x ^ n) := by
  have xy : x * y = y * x + c := by rw [← commutator]; noncomm_ring
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, mul_one]
    rw [pow_two, leibniz, derivative, xy]
    norm_num
    module
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ', leibniz, derivative, ih]
    simp only [mul_add, mul_smul_comm]
    rw [← mul_assoc x y, xy, add_mul, ← mul_assoc x c, central.eq]
    simp only [mul_assoc, ← pow_succ', Nat.cast_add, Nat.cast_one]
    module

def term (n : ℕ) (x : R) : R := ((n.factorial : ℂ)⁻¹) • x ^ n

def partialExp (n : ℕ) (x : R) : R := ∑ k ∈ Finset.range n, term k x

theorem partialExp_succ (n : ℕ) (x : R) :
    partialExp (n + 1) x = partialExp n x + term n x :=
  Finset.sum_range_succ _ _

theorem derivative_term (D : R →ₗ[ℂ] R)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (x y c : R) (derivative : D x = y)
    (commutator : x * y - y * x = c) (central : Commute x c) (n : ℕ) :
    D (term (n + 2) x) = y * term (n + 1) x + (1 / 2 : ℂ) • (c * term n x) := by
  simp only [term, map_smul, derivative_power D leibniz x y c derivative commutator central,
    smul_add, smul_smul, mul_smul_comm]
  have first : ((n+2).factorial : ℂ)⁻¹ * ((n : ℂ)+2) =
      ((n+1).factorial : ℂ)⁻¹ := by
    rw [show n+2 = (n+1)+1 by omega, Nat.factorial_succ]
    push_cast
    have hn : (n : ℂ)+1+1 ≠ 0 := by exact_mod_cast (show n+1+1 ≠ 0 by omega)
    field_simp
    ring
  have second : ((n+2).factorial : ℂ)⁻¹ * (((n : ℂ)+2)*((n : ℂ)+1)/2) =
      (1/2 : ℂ) * (n.factorial : ℂ)⁻¹ := by
    rw [show n+2 = (n+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
    have hn' : (n : ℂ)+1+1 ≠ 0 := by exact_mod_cast (show n+1+1 ≠ 0 by omega)
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring
  rw [first, second]

theorem derivative_partialExp (D : R →ₗ[ℂ] R) (one : D 1 = 0)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (x y c : R) (derivative : D x = y)
    (commutator : x * y - y * x = c) (central : Commute x c) (n : ℕ) :
    D (partialExp (n+2) x) = y * partialExp (n+1) x +
      (1/2 : ℂ) • (c * partialExp n x) := by
  induction n with
  | zero => simp [partialExp, Finset.sum_range_succ, term, map_add, one, derivative]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, partialExp_succ, map_add, ih,
      derivative_term D leibniz x y c derivative commutator central]
    rw [show n+1+1 = (n+1)+1 by omega, partialExp_succ (n+1), partialExp_succ n]
    simp only [mul_add, smul_add]
    module

theorem finite_exp_derivative (D : R →ₗ[ℂ] R) (one : D 1 = 0)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (x y c : R) (derivative : D x = y)
    (commutator : x * y - y * x = c) (central : Commute x c)
    (n : ℕ) (last_first : y * x ^ (n+1) = 0) (last_second : c * x ^ n = 0) :
    D (partialExp (n+2) x) = (y + (1/2 : ℂ) • c) * partialExp (n+2) x := by
  have first : y * term (n+1) x = 0 := by simp [term, last_first]
  have second : c * term n x = 0 := by simp [term, last_second]
  have next : c * term (n+1) x = 0 := by
    simp [term, pow_succ, ← mul_assoc, last_second]
  rw [derivative_partialExp D one leibniz x y c derivative commutator central n]
  rw [show n+2 = (n+1)+1 by omega, partialExp_succ (n+1)]
  simp only [add_mul, smul_mul_assoc, mul_add, first, next, smul_zero, add_zero]
  simp only [partialExp_succ n, mul_add, second, add_zero]

theorem magnus_ODE (D : R →ₗ[ℂ] R) (one : D 1 = 0)
    (leibniz : ∀ a b, D (a * b) = D a * b + a * D b)
    (x B c : R) (derivative : D x = B - (1/2 : ℂ) • c)
    (commutator : x * (B - (1/2 : ℂ) • c) - (B - (1/2 : ℂ) • c) * x = c)
    (central : Commute x c) (n : ℕ)
    (last_first : (B - (1/2 : ℂ) • c) * x ^ (n+1) = 0)
    (last_second : c * x ^ n = 0) :
    D (partialExp (n+2) x) = B * partialExp (n+2) x := by
  simpa only [sub_add_cancel] using finite_exp_derivative D one leibniz x
    (B - (1/2 : ℂ) • c) c derivative commutator central n last_first last_second

end
end SourceMagnusDerivative
