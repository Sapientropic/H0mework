import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# The logarithmic derivation of Dirichlet convolution

Multiplication of indices is generated inside the divisor antidiagonal.
The real logarithm therefore induces a canonical derivation on arithmetic
functions.  This is the generic engine law; no zeta zero, Euler product,
nonvanishing, or determinant hypothesis enters.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace GenericFoundation
namespace Arithmetic
namespace DirichletLogPosition

open scoped ArithmeticFunction

noncomputable section

/-- Logarithmic position on the multiplicative index carrier. -/
def logPosition (value : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n * value n, by simp⟩

@[simp] theorem logPosition_apply
    (value : ArithmeticFunction ℝ) (n : Nat) :
    logPosition value n = Real.log n * value n :=
  rfl

/-- The complete source relation behind the conductor commutator: logarithmic
position is a derivation for Dirichlet convolution. -/
theorem logPosition_mul
    (left right : ArithmeticFunction ℝ) :
    logPosition (left * right) =
      logPosition left * right + left * logPosition right := by
  apply ArithmeticFunction.ext
  intro n
  simp only [logPosition_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair membership
  have leftNonzero : (pair.1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal membership
  have rightNonzero : (pair.2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.right_ne_zero_of_mem_divisorsAntidiagonal membership
  have product := (Nat.mem_divisorsAntidiagonal.mp membership).1
  rw [← product, Nat.cast_mul, Real.log_mul leftNonzero rightNonzero]
  ring

/-- Commuting logarithmic position past left convolution exposes the source
derivative. -/
theorem leftConvolution_commutator
    (source test : ArithmeticFunction ℝ) :
    logPosition (source * test) - source * logPosition test =
      logPosition source * test := by
  rw [logPosition_mul]
  abel

end
end DirichletLogPosition
end Arithmetic
end GenericFoundation
end SaturationMonoid
