import H0mework.Fock.HistoryPolynomial.CopySource
import Mathlib.Algebra.Polynomial.Expand

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyProgram

open SourceCyclicModule Polynomial
noncomputable section

def polynomial (depth : Nat) (index : Index depth) (p : Polynomial ℤ) : Polynomial ℤ :=
  coefficients.symm (action depth index (program p))

theorem polynomial_source (depth : Nat) (index : Index depth) (p : Polynomial ℤ) :
    program (polynomial depth index p) = action depth index (program p) := by
  rw [program_is_coefficients]
  exact coefficients.apply_symm_apply _

theorem polynomial_add (depth : Nat) (index : Index depth) (p q : Polynomial ℤ) :
    polynomial depth index (p + q) = polynomial depth index p + polynomial depth index q := by
  unfold polynomial
  rw [program_add, map_add, map_add]

theorem polynomial_monomial (depth : Nat) (index : Index depth) (n : Nat) (a : ℤ) :
    polynomial depth index (monomial n a) = monomial (indexAfter depth index n) a := by
  apply program_injective
  rw [polynomial_source, program_monomial, program_monomial]
  exact Finsupp.mapDomain_single

theorem polynomial_formula (depth : Nat) (index : Index depth) (p : Polynomial ℤ) :
    polynomial depth index p = X ^ (scale depth index - 1) * expand ℤ (scale depth index) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [polynomial_add, map_add, mul_add, hp, hq]
  | monomial n a =>
      rw [polynomial_monomial, expand_monomial, ← monomial_one_right_eq_X_pow,
        monomial_mul_monomial, one_mul]
      apply congrArg (fun degree => monomial degree a)
      rw [index_source, Nat.add_mul, Nat.one_mul]
      have positive := scale_pos depth index
      omega

theorem polynomial_native_action (depth : Nat) (index : Index depth) (p : Polynomial ℤ) :
    polynomial depth index (X * p) = X ^ scale depth index * polynomial depth index p := by
  rw [polynomial_formula, polynomial_formula, map_mul, expand_X]
  ring

theorem polynomial_injective (depth : Nat) (index : Index depth) :
    Function.Injective (polynomial depth index) := by
  intro p q same
  have source := congrArg program same
  rw [polynomial_source, polynomial_source] at source
  exact program_injective (Finsupp.mapDomain_injective (index_injective depth index) source)

end
end SourceCopyProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
