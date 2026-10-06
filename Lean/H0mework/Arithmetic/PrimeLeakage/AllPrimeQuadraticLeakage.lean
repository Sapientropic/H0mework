import H0mework.Arithmetic.PrimeLeakage.AllPrimeCharacterLeakage

/-!
# Positive all-prime leakage energy and detector coupling

The coordinatewise character leakage carries a canonical finite-support
sum-of-norm-squares.  It is nonnegative and its zero fibre is exact.  On every
generated prime basis it has the same zero fibre as the existing q-rich
full-row detector and the installed radial log current.

The generated leakage face is attached to the existing exact-envelope
occurrence.  No no-flux, critical-line, separator-zero or RH field is stored.
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
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

def allPrimeCharacterLeakageEnergy
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) : ℝ :=
  (allPrimeCharacterLeakageMap observation current).sum
    fun _ value => ‖value‖ ^ 2

theorem allPrimeCharacterLeakageEnergy_nonnegative
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    0 ≤ allPrimeCharacterLeakageEnergy observation current := by
  unfold allPrimeCharacterLeakageEnergy
  exact Finsupp.sum_nonneg fun _ _ => sq_nonneg _

theorem allPrimeCharacterLeakageEnergy_eq_zero_iff_map_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    allPrimeCharacterLeakageEnergy observation current = 0 ↔
      allPrimeCharacterLeakageMap observation current = 0 := by
  constructor
  · intro energyZero
    ext prime
    by_cases prime_mem : prime ∈
        (allPrimeCharacterLeakageMap observation current).support
    · have eachZero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun index _ => sq_nonneg
            ‖allPrimeCharacterLeakageMap observation current index‖)).1
          (show
            (allPrimeCharacterLeakageMap observation current).support.sum
                (fun index =>
                  ‖allPrimeCharacterLeakageMap observation current index‖ ^ 2) =
              0 by
            exact energyZero)
          prime prime_mem
      have normZero :
          ‖allPrimeCharacterLeakageMap observation current prime‖ = 0 :=
        sq_eq_zero_iff.mp eachZero
      exact norm_eq_zero.mp normZero
    · simpa [Finsupp.mem_support_iff] using prime_mem
  · intro mapZero
    unfold allPrimeCharacterLeakageEnergy
    rw [mapZero]
    simp

theorem allPrimeCharacterLeakageEnergy_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (current : AllPrimeCurrent) :
    allPrimeCharacterLeakageEnergy observation current = 0 ↔
      current = 0 ∨ observation.coordinate.re = 1 / 2 := by
  rw [allPrimeCharacterLeakageEnergy_eq_zero_iff_map_eq_zero,
    allPrimeCharacterLeakageMap_eq_zero_iff]

@[simp] theorem allPrimeCharacterLeakageEnergy_single_one
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    allPrimeCharacterLeakageEnergy observation
        (Finsupp.single prime 1) =
      ‖generatedPrimeCharacterLeakage observation prime‖ ^ 2 := by
  unfold allPrimeCharacterLeakageEnergy
  rw [allPrimeCharacterLeakageMap_single]
  simp

theorem allPrimeCharacterLeakageEnergy_single_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    allPrimeCharacterLeakageEnergy observation
        (Finsupp.single prime 1) = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  rw [allPrimeCharacterLeakageEnergy_eq_zero_iff]
  simp

def generatedPrimeFullRowReadback
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) : ℂ :=
  QRich.pointFullRowCycleCReadback
    (mathlibZeroPoint observation.coordinate observation.mathlibZero)
    (generatedPrimeFactor prime).stage (generatedPrimeFactorRow prime)
    (zeroIntegralCharacterPointFullRowCycle observation
      (generatedPrimeFactor prime).stage
      (delta (rowPrimeScaleUnit (generatedPrimeFactorRow prime))))

theorem generatedPrimeFullRowReadback_eq_zero_iff_leakage_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    generatedPrimeFullRowReadback observation prime = 0 ↔
      generatedPrimeCharacterLeakage observation prime = 0 := by
  unfold generatedPrimeFullRowReadback generatedPrimeCharacterLeakage
  exact groupRingPrimeCurrent_eq_zero_iff_fullRowReadback_eq_zero
    observation (generatedPrimeFactor prime).stage
      (generatedPrimeFactorRow prime)

theorem allPrimeCharacterLeakageEnergy_single_eq_zero_iff_fullRow
    (observation : GeneratedRiemannZeroObservation)
    (prime : Nat.Primes) :
    allPrimeCharacterLeakageEnergy observation
        (Finsupp.single prime 1) = 0 ↔
      generatedPrimeFullRowReadback observation prime = 0 := by
  rw [allPrimeCharacterLeakageEnergy_single_one, sq_eq_zero_iff,
    norm_eq_zero,
    generatedPrimeFullRowReadback_eq_zero_iff_leakage_eq_zero]

theorem allPrimeCharacterLeakageEnergy_single_eq_zero_iff_omegaLogNorm
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (stage : Nat) :
    allPrimeCharacterLeakageEnergy observation
        (Finsupp.single prime 1) = 0 ↔
      omegaLogNormEffect observation nontrivial stage = 0 := by
  rw [allPrimeCharacterLeakageEnergy_single_eq_zero_iff,
    omegaLogNormEffect_eq_coordinateResidual]
  constructor <;> intro equality <;> linarith

structure GeneratedAllPrimeLeakageFaceAt
    (observation : GeneratedRiemannZeroObservation) : Type where
  private mk ::
  leakageMap : AllPrimeCurrent →ₗ[ℤ] PrimeLeakageCarrier
  energy : AllPrimeCurrent → ℝ
  leakageMap_eq : leakageMap = allPrimeCharacterLeakageMap observation
  energy_eq : energy = allPrimeCharacterLeakageEnergy observation
  energy_nonnegative : ∀ current, 0 ≤ energy current
  energy_zero_iff : ∀ current,
    energy current = 0 ↔
      current = 0 ∨ observation.coordinate.re = 1 / 2

def generatedAllPrimeLeakageFace
    (observation : GeneratedRiemannZeroObservation) :
    GeneratedAllPrimeLeakageFaceAt observation where
  leakageMap := allPrimeCharacterLeakageMap observation
  energy := allPrimeCharacterLeakageEnergy observation
  leakageMap_eq := rfl
  energy_eq := rfl
  energy_nonnegative := allPrimeCharacterLeakageEnergy_nonnegative observation
  energy_zero_iff := allPrimeCharacterLeakageEnergy_eq_zero_iff observation

def allPrimeLeakageOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (allPrimeExactEnvelopeOccurrence observation nontrivial).map
    fun payload => (payload, generatedAllPrimeLeakageFace observation)

theorem allPrimeLeakageOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (allPrimeLeakageOccurrence observation nontrivial).map Prod.fst =
      allPrimeExactEnvelopeOccurrence observation nontrivial := by
  rw [allPrimeLeakageOccurrence, RootedAccountedUnfolding.map_map]
  change (allPrimeExactEnvelopeOccurrence
    observation nontrivial).map id = _
  exact RootedAccountedUnfolding.map_id _

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
