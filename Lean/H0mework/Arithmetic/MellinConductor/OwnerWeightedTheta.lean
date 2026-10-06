import H0mework.Arithmetic.EulerLog.ConductorCurrent
import H0mework.Arithmetic.Muntz.CoPoissonMuntzDirichletSource

/-!
# Owner-weighted Müntz theta and cofinal conductor current

The canonical global-germ coefficients act on the actual positive-dilation
Schwartz family.  Their infinite read is the existing Müntz theta kernel.
The Euler conductor acts first on finite prefixes, with an exact successor
term; no completed future, analytic division, or asymptotic estimate is used
to generate that current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor

open CanonicalArithmeticState.AllPlaceEulerLog
open CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open scoped ArithmeticFunction SchwartzMap

noncomputable section

def arithmeticPositiveDilationTerm
    (coefficients : ArithmeticFunction ℝ)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (index : Nat) : ℂ :=
  (coefficients (index + 1) : ℂ) *
    coPoissonMuntzEvenSource test (((index + 1 : Nat) : ℝ) * scale)

def arithmeticPositiveDilationPrefix
    (coefficients : ArithmeticFunction ℝ)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) : ℂ :=
  ∑ index ∈ Finset.range cutoff,
    arithmeticPositiveDilationTerm coefficients test scale index

def arithmeticPositiveDilationSum
    (coefficients : ArithmeticFunction ℝ)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) : ℂ :=
  ∑' index : Nat,
    arithmeticPositiveDilationTerm coefficients test scale index

theorem arithmeticPositiveDilationPrefix_succ
    (coefficients : ArithmeticFunction ℝ)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) :
    arithmeticPositiveDilationPrefix coefficients test scale (cutoff + 1) =
      arithmeticPositiveDilationPrefix coefficients test scale cutoff +
        arithmeticPositiveDilationTerm coefficients test scale cutoff := by
  unfold arithmeticPositiveDilationPrefix
  rw [Finset.sum_range_succ]

def ownerWeightedPositiveDilationSum
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) : ℂ :=
  arithmeticPositiveDilationSum (ownerRealCoefficients owner) test scale

/-- The owner-weighted family is not a new theta object: it is literally the
existing nonzero Müntz theta sum. -/
theorem ownerWeightedPositiveDilationSum_eq_thetaNonzero
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (scale_ne : scale ≠ 0) :
    ownerWeightedPositiveDilationSum owner test scale =
      coPoissonMuntzThetaNonzero test scale := by
  unfold ownerWeightedPositiveDilationSum arithmeticPositiveDilationSum
    arithmeticPositiveDilationTerm
  rw [coPoissonMuntzThetaNonzero_eq_positive_tsum test scale_ne]
  apply tsum_congr
  intro index
  rw [ownerRealCoefficients_eq_zeta]
  simp [ArithmeticFunction.zeta_apply_ne (Nat.succ_ne_zero index)]

def generatedEulerConductorDilationTerm
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (index : Nat) : ℂ :=
  arithmeticPositiveDilationTerm
    (generatedEulerConductorCurrent owner) test scale index

def generatedEulerConductorDilationPrefix
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) : ℂ :=
  arithmeticPositiveDilationPrefix
    (generatedEulerConductorCurrent owner) test scale cutoff

theorem generatedEulerConductorDilationPrefix_succ
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) :
    generatedEulerConductorDilationPrefix owner test scale (cutoff + 1) =
      generatedEulerConductorDilationPrefix owner test scale cutoff +
        generatedEulerConductorDilationTerm owner test scale cutoff :=
  arithmeticPositiveDilationPrefix_succ _ _ _ _

/-- The cofinal dilation current is the image of the actual source
commutator, not an independently supplied Euler table. -/
theorem generatedEulerConductorDilationPrefix_eq_commutator
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) :
    generatedEulerConductorDilationPrefix owner test scale cutoff =
      arithmeticPositiveDilationPrefix
        (ownerLogPositionCommutator owner
          (generatedOwnerDirichletInverse owner))
        test scale cutoff := by
  rfl

theorem generatedEulerConductorDilationTerm_primePower
    (owner : GlobalGermOwner)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    generatedEulerConductorDilationTerm owner test scale
        ((prime : Nat) ^ exponent - 1) =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        coPoissonMuntzEvenSource test
          ((((prime : Nat) ^ exponent : Nat) : ℝ) * scale) := by
  unfold generatedEulerConductorDilationTerm
    arithmeticPositiveDilationTerm
  have powerPositive : 0 < (prime : Nat) ^ exponent :=
    pow_pos prime.property.pos _
  rw [Nat.sub_add_cancel powerPositive]
  rw [generatedEulerConductorCurrent_primePower
    owner prime exponent positive]

end
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
