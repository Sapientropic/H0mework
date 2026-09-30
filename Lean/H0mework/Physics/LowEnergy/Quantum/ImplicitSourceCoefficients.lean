import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic

/-! Coefficient-by-coefficient source branch construction.
The residual at order n consumes only coefficients of orders below n.
The source Jacobian supplies a linear equivalence, not a completed branch.
Analytic convergence and the original constraint's coefficient law are
separate consumers of this formal construction. -/
set_option autoImplicit false
namespace SourceImplicitCoefficients
noncomputable section
variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

def coefficients (initial : V) (jacobian : V ≃ₗ[𝕜] V)
    (residual : (n : ℕ) → (Fin n → V) → V) (n : ℕ) : V :=
  if n = 0 then initial
  else -jacobian.symm (residual n (fun i => coefficients initial jacobian residual i.val))
termination_by n
decreasing_by exact i.isLt

theorem coefficient_zero (initial : V) (jacobian : V ≃ₗ[𝕜] V)
    (residual : (n : ℕ) → (Fin n → V) → V) :
    coefficients initial jacobian residual 0 = initial := by
  rw [coefficients, if_pos rfl]

theorem coefficient_equation (initial : V) (jacobian : V ≃ₗ[𝕜] V)
    (residual : (n : ℕ) → (Fin n → V) → V) (n : ℕ) (positive : n ≠ 0) :
    jacobian (coefficients initial jacobian residual n) +
      residual n (fun i => coefficients initial jacobian residual i.val) = 0 := by
  rw [coefficients, if_neg positive, map_neg, LinearEquiv.apply_symm_apply, neg_add_cancel]

theorem unique_coefficients (initial : V) (jacobian : V ≃ₗ[𝕜] V)
    (residual : (n : ℕ) → (Fin n → V) → V) (other : ℕ → V)
    (same_initial : other 0 = initial)
    (law : ∀ n, n ≠ 0 → jacobian (other n) + residual n (fun i => other i.val) = 0) :
    other = coefficients initial jacobian residual := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n earlier =>
    by_cases base : n = 0
    · subst n
      rw [coefficient_zero, same_initial]
    · have history : (fun i : Fin n => other i.val) =
          (fun i => coefficients initial jacobian residual i.val) := by
        funext i
        exact earlier i.val i.isLt
      have lhs := law n base
      rw [history] at lhs
      have rhs := coefficient_equation initial jacobian residual n base
      apply jacobian.injective
      exact add_right_cancel (lhs.trans rhs.symm)

theorem all_constraint_coefficients_zero (initial : V) (jacobian : V ≃ₗ[𝕜] V)
    (residual : (n : ℕ) → (Fin n → V) → V)
    (constraint : (ℕ → V) → ℕ → V)
    (constant_law : ∀ u, u 0 = initial → constraint u 0 = 0)
    (highest_coefficient_law : ∀ u, u 0 = initial → ∀ n, n ≠ 0 →
      constraint u n = jacobian (u n) + residual n (fun i => u i.val)) :
    ∀ n, constraint (coefficients initial jacobian residual) n = 0 := by
  intro n
  have base := coefficient_zero initial jacobian residual
  by_cases positive : n = 0
  · subst n
    exact constant_law _ base
  · rw [highest_coefficient_law _ base n positive]
    exact coefficient_equation initial jacobian residual n positive

#print axioms coefficient_equation
#print axioms unique_coefficients
#print axioms all_constraint_coefficients_zero
end
end SourceImplicitCoefficients
