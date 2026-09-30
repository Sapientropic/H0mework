import H0mework.Versions.Y.Arithmetic.PrimeLeakage.AllPrimeQuadraticLeakage
import H0mework.Versions.Y.Arithmetic.EulerLog.GlobalGerm

/-!
# Euler-weighted prime leakage diagonal

The exact Euler-log coefficient and the selected/reversal character leakage
are read on the same generated prime.  Their product is the finite-place
diagonal required by an all-place Weil quadratic trace.  It is source-positive
and has the same zero fibre as the existing leakage; no positivity or
critical-line witness is accepted from a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace EulerDiagonal

open ActionCofiber.RawEffect
open ActionCofiber.RawEffect.AllPrimeCofinal
open ActionCofiber.RawEffect.AllPrimeLeakage
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open Character.IntegralCharacterGroupRing
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

def eulerWeightedPrimeLeakage
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) : ℝ :=
  globalEulerLogOccurrence.root.2.coefficients prime *
    ‖generatedPrimeCharacterLeakage observation prime‖ ^ 2

theorem globalEulerLogOccurrence_prime_coefficient
    (prime : Nat.Primes) :
    globalEulerLogOccurrence.root.2.coefficients prime =
      Real.log ((prime : ℕ) : ℝ) := by
  rw [globalEulerLogOccurrence.root.2.coefficients_eq_vonMangoldt,
    ArithmeticFunction.vonMangoldt_apply_prime prime.property]

theorem generatedPrimeCharacterLeakage_eq_cpow_sub
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    generatedPrimeCharacterLeakage observation prime =
      ((prime : ℕ) : ℂ) ^ (-observation.coordinate) -
        ((prime : ℕ) : ℂ) ^
          (-(coordinateReversal observation.coordinate)) := by
  unfold generatedPrimeCharacterLeakage
    Character.GlobalCoPoissonCurrent.groupRingPrimeCurrent
  rw [zeroOwnedIntegralCharacterOccurrence_root_selected,
    zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta, characterEvaluation_delta,
    Character.zeroOwnedMultiplicativeCharacterOccurrence_root_selected,
    Character.zeroOwnedMultiplicativeCharacterOccurrence_root_reversal,
    generatedPrimeFactorRow_scaleUnit]
  unfold blockPrimeScaleUnit
  rw [complexPowerCharacter_apply, complexPowerCharacter_apply]
  rfl

theorem norm_sq_cpow_sub_reversal
    (coordinate : ℂ) (prime : Nat.Primes) :
    ‖((prime : ℕ) : ℂ) ^ (-coordinate) -
        ((prime : ℕ) : ℂ) ^ (-(coordinateReversal coordinate))‖ ^ 2 =
      ((prime : ℕ) : ℝ) ^ (-2 * coordinate.re) +
        ((prime : ℕ) : ℝ) ^ (-2 * (1 - coordinate.re)) -
          2 * (((prime : ℕ) : ℝ))⁻¹ := by
  let q : ℝ := (prime : ℕ)
  let phaseExponent : ℂ := -(coordinate.im : ℂ) * Complex.I
  change
    ‖(q : ℂ) ^ (-coordinate) -
        (q : ℂ) ^ (-(coordinateReversal coordinate))‖ ^ 2 =
      q ^ (-2 * coordinate.re) +
        q ^ (-2 * (1 - coordinate.re)) - 2 * q⁻¹
  have qPos : 0 < q := by
    dsimp [q]
    exact_mod_cast prime.property.pos
  have qNonneg : 0 ≤ q := qPos.le
  have qComplexNe : (q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr qPos.ne'
  have selectedExponent :
      -coordinate = (-coordinate.re : ℂ) + phaseExponent := by
    apply Complex.ext <;>
      simp [phaseExponent]
  have reversalExponent :
      -(coordinateReversal coordinate) =
        (coordinate.re - 1 : ℂ) + phaseExponent := by
    apply Complex.ext <;>
      simp [coordinateReversal, phaseExponent]
  have selectedReal :
      (q : ℂ) ^ (-(coordinate.re : ℂ)) =
        ((q ^ (-coordinate.re) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow qNonneg (-coordinate.re)).symm
  have reversalReal :
      (q : ℂ) ^ ((coordinate.re : ℂ) - 1) =
        ((q ^ (coordinate.re - 1) : ℝ) : ℂ) := by
    simpa using
      (Complex.ofReal_cpow qNonneg (coordinate.re - 1)).symm
  rw [selectedExponent, reversalExponent,
    Complex.cpow_add _ _ qComplexNe,
    Complex.cpow_add _ _ qComplexNe,
    selectedReal, reversalReal,
    ← sub_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos qPos]
  have phaseRe : phaseExponent.re = 0 := by
    simp [phaseExponent]
  rw [phaseRe, Real.rpow_zero, mul_one]
  rw [← Complex.ofReal_sub, Complex.norm_real]
  rw [Real.norm_eq_abs, sq_abs]
  have selectedSquare :
      (q ^ (-coordinate.re)) ^ 2 = q ^ (-2 * coordinate.re) := by
    rw [← Real.rpow_mul_natCast qNonneg]
    congr 1
    ring
  have reversalSquare :
      (q ^ (coordinate.re - 1)) ^ 2 =
        q ^ (-2 * (1 - coordinate.re)) := by
    rw [← Real.rpow_mul_natCast qNonneg]
    congr 1
    ring
  have cross :
      q ^ (-coordinate.re) * q ^ (coordinate.re - 1) = q⁻¹ := by
    rw [← Real.rpow_add qPos]
    rw [show -coordinate.re + (coordinate.re - 1) = (-1 : ℝ) by ring,
      Real.rpow_neg_one]
  calc
    (q ^ (-coordinate.re) - q ^ (coordinate.re - 1)) ^ 2 =
        (q ^ (-coordinate.re)) ^ 2 +
          (q ^ (coordinate.re - 1)) ^ 2 -
            2 * (q ^ (-coordinate.re) *
              q ^ (coordinate.re - 1)) := by ring
    _ = _ := by rw [selectedSquare, reversalSquare, cross]

theorem eulerWeightedPrimeLeakage_eq
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    eulerWeightedPrimeLeakage observation prime =
      Real.log ((prime : ℕ) : ℝ) *
        (((prime : ℕ) : ℝ) ^ (-2 * observation.coordinate.re) +
          ((prime : ℕ) : ℝ) ^ (-2 * (1 - observation.coordinate.re)) -
            2 * (((prime : ℕ) : ℝ))⁻¹) := by
  unfold eulerWeightedPrimeLeakage
  rw [globalEulerLogOccurrence.root.2.coefficients_eq_vonMangoldt,
    ArithmeticFunction.vonMangoldt_apply_prime prime.property,
    generatedPrimeCharacterLeakage_eq_cpow_sub,
    norm_sq_cpow_sub_reversal]

theorem eulerWeightedPrimeLeakage_nonnegative
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    0 ≤ eulerWeightedPrimeLeakage observation prime := by
  rw [eulerWeightedPrimeLeakage,
    globalEulerLogOccurrence_prime_coefficient]
  positivity

theorem eulerWeightedPrimeLeakage_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    eulerWeightedPrimeLeakage observation prime = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  rw [eulerWeightedPrimeLeakage,
    globalEulerLogOccurrence_prime_coefficient]
  have primeOne : 1 < ((prime : ℕ) : ℝ) := by
    exact_mod_cast prime.property.two_le
  have logNe : Real.log ((prime : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos primeOne)
  rw [mul_eq_zero, or_iff_right logNe, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero,
    generatedPrimeCharacterLeakage_eq_zero_iff_coordinate_re_eq_half]

end
end EulerDiagonal
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
