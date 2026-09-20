import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNReal.Defs

/-!
# The positive-real complex power character

One complex coordinate generates a multiplicative character on strictly
positive real scales.  Prime evaluation and square-root Archimedean
evaluation are dependent faces of this single character: they are not two
scalar tables that later need a comparator.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedPositiveRealCharacter

open Complex

noncomputable section

/-- A positive real regarded as a unit of the nonnegative reals. -/
def positiveRealUnit (value : ℝ) (positive : 0 < value) : Units NNReal :=
  Units.mk0 (Real.toNNReal value)
    (ne_of_gt (Real.toNNReal_pos.2 positive))

@[simp]
theorem positiveRealUnit_val (value : ℝ) (positive : 0 < value) :
    (((positiveRealUnit value positive : Units NNReal) : NNReal) : ℝ) =
      value := by
  change ((((Units.mk0 (Real.toNNReal value)
    (ne_of_gt (Real.toNNReal_pos.2 positive)) : Units NNReal) : NNReal)) : ℝ) =
      value
  rw [Units.val_mk0, Real.coe_toNNReal value positive.le]

/-- The common source-generated multiplicative character
`a ↦ a ^ (-coordinate)` on positive real scales. -/
def complexPowerCharacter (coordinate : ℂ) : Units NNReal →* ℂ where
  toFun scale := ((((scale : NNReal) : ℝ) : ℂ)) ^ (-coordinate)
  map_one' := by simp
  map_mul' left right := by
    change ((((((left : Units NNReal) : NNReal) *
        ((right : Units NNReal) : NNReal) : NNReal) : ℝ) : ℂ)) ^
          (-coordinate) = _
    rw [NNReal.coe_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg
        NNReal.zero_le_coe NNReal.zero_le_coe]

@[simp]
theorem complexPowerCharacter_apply
    (coordinate : ℂ) (value : ℝ) (positive : 0 < value) :
    complexPowerCharacter coordinate (positiveRealUnit value positive) =
      (value : ℂ) ^ (-coordinate) := by
  change (((((positiveRealUnit value positive : Units NNReal) : NNReal) : ℝ) : ℂ)) ^
      (-coordinate) = _
  rw [positiveRealUnit_val]

/-- The finite-prime face is literally `p ^ (-coordinate)`. -/
theorem complexPowerCharacter_prime
    (coordinate : ℂ) (prime : Nat.Primes) :
    complexPowerCharacter coordinate
        (positiveRealUnit (prime : ℝ) (by
          exact_mod_cast prime.2.pos)) =
      ((prime : Nat) : ℂ) ^ (-coordinate) := by
  exact complexPowerCharacter_apply coordinate (prime : ℝ)
    (by exact_mod_cast prime.2.pos)

/-- Pullback along the square-root chart is the quarter-Mellin character
`a ^ (-(coordinate / 2))`. -/
theorem complexPowerCharacter_sqrt
    (coordinate : ℂ) (value : ℝ) (positive : 0 < value) :
    complexPowerCharacter coordinate
        (positiveRealUnit (Real.sqrt value) (Real.sqrt_pos.2 positive)) =
      (value : ℂ) ^ (-(coordinate / 2)) := by
  rw [complexPowerCharacter_apply]
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 positive).ne')]
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr positive.ne')]
  rw [← Complex.ofReal_log (Real.sqrt_nonneg value),
    Real.log_sqrt positive.le, ← Complex.ofReal_log positive.le,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 1
  ring

/-- Every value of the positive-real character is a unit; no prime face can
vanish before a global summation or regularized topological quotient. -/
theorem complexPowerCharacter_ne_zero
    (coordinate : ℂ) (scale : Units NNReal) :
    complexPowerCharacter coordinate scale ≠ 0 := by
  apply cpow_ne_zero_iff.mpr
  left
  exact Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr scale.ne_zero)

theorem complexPowerCharacter_isUnit
    (coordinate : ℂ) (scale : Units NNReal) :
    IsUnit (complexPowerCharacter coordinate scale) :=
  isUnit_iff_ne_zero.mpr (complexPowerCharacter_ne_zero coordinate scale)

/-- The norm of the same character records only the real part of its
coordinate. -/
theorem norm_complexPowerCharacter_apply
    (coordinate : ℂ) (value : ℝ) (positive : 0 < value) :
    ‖complexPowerCharacter coordinate (positiveRealUnit value positive)‖ =
      Real.rpow value (-coordinate.re) := by
  rw [complexPowerCharacter_apply,
    Complex.norm_cpow_eq_rpow_re_of_pos positive]
  simp

end

end SourceGeneratedPositiveRealCharacter
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
