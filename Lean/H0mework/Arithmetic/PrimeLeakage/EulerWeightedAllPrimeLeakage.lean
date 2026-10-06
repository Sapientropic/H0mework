import H0mework.Arithmetic.PrimeLeakage.EulerWeightedPrimeLeakage

/-!
# Euler-weighted all-prime leakage energy

The finite-prime diagonal extends over every source-generated finite current.
Every summand keeps its own prime coordinate and carries the positive Euler-log
weight, so neither cross-prime cancellation nor a zero Euler coefficient can
hide leakage.
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

open ActionCofiber.RawEffect.AllPrimeCofinal
open ActionCofiber.RawEffect.AllPrimeLeakage
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog

noncomputable section

def generatedEulerFaceWeightedLeakageEnergy
    {owner : CanonicalArithmeticState.AllPlaceEulerLog.GlobalGermOwner}
    (eulerFace : GeneratedEulerLogFaceAt owner)
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) : ℝ :=
  (allPrimeCharacterLeakageMap observation current).sum fun prime value =>
    eulerFace.coefficients prime * ‖value‖ ^ 2

def allPrimeEulerWeightedLeakageEnergy
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) : ℝ :=
  (allPrimeCharacterLeakageMap observation current).sum fun prime value =>
    globalEulerLogOccurrence.root.2.coefficients prime * ‖value‖ ^ 2

theorem generatedEulerFaceWeightedLeakageEnergy_eq_allPrime
    {owner : CanonicalArithmeticState.AllPlaceEulerLog.GlobalGermOwner}
    (eulerFace : GeneratedEulerLogFaceAt owner)
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    generatedEulerFaceWeightedLeakageEnergy eulerFace observation current =
      allPrimeEulerWeightedLeakageEnergy observation current := by
  unfold generatedEulerFaceWeightedLeakageEnergy
    allPrimeEulerWeightedLeakageEnergy
  apply Finsupp.sum_congr
  intro prime _primeMem
  rw [eulerFace.coefficients_eq_vonMangoldt,
    globalEulerLogOccurrence.root.2.coefficients_eq_vonMangoldt]

private theorem eulerWeight_nonnegative (prime : Nat.Primes) :
    0 ≤ globalEulerLogOccurrence.root.2.coefficients prime := by
  rw [globalEulerLogOccurrence_prime_coefficient]
  apply (Real.log_pos ?_).le
  exact_mod_cast prime.property.two_le

private theorem eulerWeight_pos (prime : Nat.Primes) :
    0 < globalEulerLogOccurrence.root.2.coefficients prime := by
  rw [globalEulerLogOccurrence_prime_coefficient]
  apply Real.log_pos
  exact_mod_cast prime.property.two_le

theorem allPrimeEulerWeightedLeakageEnergy_nonnegative
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    0 ≤ allPrimeEulerWeightedLeakageEnergy observation current := by
  unfold allPrimeEulerWeightedLeakageEnergy
  apply Finsupp.sum_nonneg
  intro prime _value
  exact mul_nonneg (eulerWeight_nonnegative prime)
    (sq_nonneg ‖allPrimeCharacterLeakageMap observation current prime‖)

theorem allPrimeEulerWeightedLeakageEnergy_eq_zero_iff_map_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    allPrimeEulerWeightedLeakageEnergy observation current = 0 ↔
      allPrimeCharacterLeakageMap observation current = 0 := by
  constructor
  · intro energyZero
    ext prime
    by_cases primeMem : prime ∈
        (allPrimeCharacterLeakageMap observation current).support
    · have termZero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun index _ => mul_nonneg (eulerWeight_nonnegative index)
            (sq_nonneg
              ‖allPrimeCharacterLeakageMap observation current index‖))).1
          (show
            (allPrimeCharacterLeakageMap observation current).support.sum
                (fun index =>
                  globalEulerLogOccurrence.root.2.coefficients index *
                    ‖allPrimeCharacterLeakageMap observation current index‖ ^ 2) =
              0 by
            exact energyZero)
          prime primeMem
      have squareZero :
          ‖allPrimeCharacterLeakageMap observation current prime‖ ^ 2 = 0 :=
        (mul_eq_zero.mp termZero).resolve_left
          (ne_of_gt (eulerWeight_pos prime))
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp squareZero)
    · simpa [Finsupp.mem_support_iff] using primeMem
  · intro mapZero
    unfold allPrimeEulerWeightedLeakageEnergy
    rw [mapZero]
    simp

theorem allPrimeEulerWeightedLeakageEnergy_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    allPrimeEulerWeightedLeakageEnergy observation current = 0 ↔
      current = 0 ∨ observation.coordinate.re = 1 / 2 := by
  rw [allPrimeEulerWeightedLeakageEnergy_eq_zero_iff_map_eq_zero,
    allPrimeCharacterLeakageMap_eq_zero_iff]

@[simp] theorem allPrimeEulerWeightedLeakageEnergy_single_one
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    allPrimeEulerWeightedLeakageEnergy observation
        (Finsupp.single prime 1) =
      eulerWeightedPrimeLeakage observation prime := by
  unfold allPrimeEulerWeightedLeakageEnergy eulerWeightedPrimeLeakage
  rw [allPrimeCharacterLeakageMap_single]
  simp

theorem allPrimeEulerWeightedLeakageEnergy_single_eq_zero_iff_fullRow
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    allPrimeEulerWeightedLeakageEnergy observation
        (Finsupp.single prime 1) = 0 ↔
      generatedPrimeFullRowReadback observation prime = 0 := by
  rw [allPrimeEulerWeightedLeakageEnergy_single_one,
    eulerWeightedPrimeLeakage_eq_zero_iff,
    ← allPrimeCharacterLeakageEnergy_single_eq_zero_iff,
    allPrimeCharacterLeakageEnergy_single_eq_zero_iff_fullRow]

theorem allPrimeEulerWeightedLeakageEnergy_single_eq_zero_iff_omegaLogNorm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (stage : Nat) :
    allPrimeEulerWeightedLeakageEnergy observation
        (Finsupp.single prime 1) = 0 ↔
      ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.omegaLogNormEffect
        observation nontrivial stage = 0 := by
  rw [allPrimeEulerWeightedLeakageEnergy_single_one,
    eulerWeightedPrimeLeakage_eq_zero_iff,
    ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.omegaLogNormEffect_eq_coordinateResidual]
  constructor <;> intro equality <;> linarith

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
