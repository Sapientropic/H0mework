import H0mework.Arithmetic.PrimeLeakage.AllPrimeExactPerfectEnvelope
import H0mework.Arithmetic.RiemannCharacter.ZeroRieszPrimeCurrentCoupling

/-!
# All-prime character leakage

The selected/reversal difference is retained separately at every prime, so
distinct prime channels cannot cancel before measurement.  The resulting
finite-support complex current is an integral-linear dependent face of the
exact all-prime carrier.

Its kernel is exact: either the input current is zero or the zero observation
lies on the neutral half-density line.  This theorem does not choose either
branch and does not assert the leakage vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace ActionCofiber
namespace RawEffect
namespace AllPrimeLeakage

open AllPrimeCofinal
open AllPrimePerfectEnvelope
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter

noncomputable section

abbrev PrimeLeakageCarrier := Nat.Primes →₀ ℂ

def generatedPrimeCharacterLeakage
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) : ℂ :=
  groupRingPrimeCurrent observation (generatedPrimeFactorRow prime)

theorem generatedPrimeFactorRow_scaleUnit (prime : Nat.Primes) :
    rowPrimeScaleUnit (generatedPrimeFactorRow prime) =
      blockPrimeScaleUnit prime := by
  apply Units.ext
  apply NNReal.eq
  unfold rowPrimeScaleUnit blockPrimeScaleUnit
  rw [positiveRealUnit_val, positiveRealUnit_val,
    generatedPrimeFactorRow_prime]

theorem generatedPrimeCharacterLeakage_eq_characterDifference
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    generatedPrimeCharacterLeakage observation prime =
      allPrimeReversalCharacterMap observation nontrivial
          (Finsupp.single prime 1) -
        allPrimeSelectedCharacterMap observation nontrivial
          (Finsupp.single prime 1) := by
  rw [allPrimeReversalCharacterMap_single,
    allPrimeSelectedCharacterMap_single]
  simp only [one_smul]
  unfold generatedPrimeCharacterLeakage groupRingPrimeCurrent
  rw [zeroOwnedIntegralCharacterOccurrence_root_selected,
    zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta, characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]
  rw [installedPrimeEigenvalue_eq_complexPowerCharacter,
    installedPrimeEigenvalue_eq_complexPowerCharacter]
  rw [generatedPrimeFactorRow_scaleUnit]
  unfold blockPrimeScaleUnit
  ring

theorem generatedPrimeCharacterLeakage_eq_zero_iff_coordinate_re_eq_half
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    generatedPrimeCharacterLeakage observation prime = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  rw [generatedPrimeCharacterLeakage, groupRingPrimeCurrent, sub_eq_zero]
  rw [zeroOwnedIntegralCharacterOccurrence_root_selected,
    zeroOwnedIntegralCharacterOccurrence_root_reversal,
    characterEvaluation_delta, characterEvaluation_delta,
    zeroOwnedMultiplicativeCharacterOccurrence_root_selected,
    zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]
  constructor
  · intro equal
    have normEqual := congrArg norm equal
    unfold rowPrimeScaleUnit at normEqual
    rw [norm_complexPowerCharacter_apply,
      norm_complexPowerCharacter_apply] at normEqual
    rw [generatedPrimeFactorRow_prime] at normEqual
    have primeGtOne : 1 < (prime : ℝ) := by
      exact_mod_cast prime.property.two_le
    have exponentEqual :=
      (Real.strictMono_rpow_of_base_gt_one primeGtOne).injective normEqual
    simp [coordinateReversal] at exponentEqual
    linarith
  · intro critical
    have fixed : observation.coordinate =
        coordinateReversal observation.coordinate := by
      apply Complex.ext
      · simp [coordinateReversal]
        linarith
      · simp [coordinateReversal]
    exact congrArg (fun coordinate =>
      complexPowerCharacter coordinate
        (rowPrimeScaleUnit (generatedPrimeFactorRow prime))) fixed

def allPrimeCharacterLeakageMap
    (observation : GeneratedRiemannZeroObservation) :
    AllPrimeCurrent →ₗ[ℤ] PrimeLeakageCarrier :=
  (Finsupp.liftAddHom fun prime =>
    AddMonoidHom.flip (smulAddHom ℤ PrimeLeakageCarrier)
      (Finsupp.single prime
        (generatedPrimeCharacterLeakage observation prime))).toIntLinearMap

@[simp] theorem allPrimeCharacterLeakageMap_single
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeCharacterLeakageMap observation
        (Finsupp.single prime coefficient) =
      coefficient • Finsupp.single prime
        (generatedPrimeCharacterLeakage observation prime) := by
  simp [allPrimeCharacterLeakageMap]

theorem allPrimeCharacterLeakageMap_coordinate
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) (prime : Nat.Primes) :
    allPrimeCharacterLeakageMap observation current prime =
      (current prime : ℂ) * generatedPrimeCharacterLeakage observation prime := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      rw [map_add, Finsupp.add_apply, Finsupp.add_apply,
        leftHypothesis, rightHypothesis]
      push_cast
      ring
  | single other coefficient =>
      rw [allPrimeCharacterLeakageMap_single]
      by_cases other_eq : other = prime
      · subst other
        simp
      · simp [other_eq]

theorem allPrimeCharacterLeakageMap_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    allPrimeCharacterLeakageMap observation current = 0 ↔
      current = 0 ∨ observation.coordinate.re = 1 / 2 := by
  constructor
  · intro leakageZero
    by_cases critical : observation.coordinate.re = 1 / 2
    · exact Or.inr critical
    · apply Or.inl
      ext prime
      have coordinateZero := congrArg
        (fun leakage : PrimeLeakageCarrier => leakage prime) leakageZero
      rw [allPrimeCharacterLeakageMap_coordinate, Finsupp.zero_apply]
        at coordinateZero
      have primeLeakageNe :
          generatedPrimeCharacterLeakage observation prime ≠ 0 := by
        intro primeZero
        exact critical
          ((generatedPrimeCharacterLeakage_eq_zero_iff_coordinate_re_eq_half
            observation prime).1 primeZero)
      have coefficientZero : (current prime : ℂ) = 0 :=
        (mul_eq_zero.mp coordinateZero).resolve_right primeLeakageNe
      exact_mod_cast coefficientZero
  · rintro (currentZero | critical)
    · subst current
      exact map_zero _
    · ext prime
      rw [allPrimeCharacterLeakageMap_coordinate,
        (generatedPrimeCharacterLeakage_eq_zero_iff_coordinate_re_eq_half
          observation prime).2 critical, mul_zero]
      rfl

end
end AllPrimeLeakage
end RawEffect
end ActionCofiber
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
