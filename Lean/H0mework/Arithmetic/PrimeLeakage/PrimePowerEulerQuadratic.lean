import H0mework.Arithmetic.PrimeLeakage.PrimePowerBoundaryRead

/-!
# Euler-weighted prime-power quadratic

The source-derived selected/reversal boundary difference is weighted by the
Euler-log coefficient of the same actual prime power.  Exponent one recovers
the existing prime diagonal exactly.
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
namespace PrimePower
namespace Quadratic

open ActionCofiber.RawEffect.AllPrimeLeakage
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open SourceGeneratedPositiveRealCharacter
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Source

noncomputable section

def primePowerCharacterLeakageReadFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) : ℂ :=
  primePowerReversalCharacterReadFromSource source prime exponent -
    primePowerSelectedCharacterReadFromSource source prime exponent

def primePowerEulerWeightFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) : ℝ :=
  source.2.eulerFace.coefficients
    (ClozelGeneralizedDual.thetaDistributionPrimePower prime exponent)

theorem primePowerEulerWeightFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerEulerWeightFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent =
      Real.log ((prime : Nat) : ℝ) := by
  unfold primePowerEulerWeightFromSource
  rw [(zeroOwnedAllPrimeWeilQuadraticOccurrence
    observation nontrivial).root.2.eulerFace.coefficients_eq_vonMangoldt]
  unfold ClozelGeneralizedDual.thetaDistributionPrimePower
  rw [ArithmeticFunction.vonMangoldt_apply_pow positive.ne',
    ArithmeticFunction.vonMangoldt_apply_prime prime.property]

def primePowerEulerWeightedQuadraticFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedAllPrimeWeilQuadraticPayload observation nontrivial)
    (prime : Nat.Primes) (exponent : Nat) : ℝ :=
  primePowerEulerWeightFromSource source prime exponent *
    ‖primePowerCharacterLeakageReadFromSource source prime exponent‖ ^ 2

theorem primePowerEulerWeightedQuadraticFromSource_root_nonnegative
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    0 ≤ primePowerEulerWeightedQuadraticFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root prime exponent := by
  rw [primePowerEulerWeightedQuadraticFromSource,
    primePowerEulerWeightFromSource_root_eq
      observation nontrivial prime exponent positive]
  positivity

theorem primePowerUnit_one (prime : Nat.Primes) :
    primePowerUnit prime 1 =
      positiveRealUnit (prime : ℝ) (by exact_mod_cast prime.property.pos) := by
  simp [primePowerUnit,
    ClozelGeneralizedDual.thetaDistributionPrimePower]

theorem primePowerCharacterLeakageReadFromSource_root_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    primePowerCharacterLeakageReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime 1 =
      generatedPrimeCharacterLeakage observation prime := by
  unfold primePowerCharacterLeakageReadFromSource
  rw [primePowerReversalCharacterReadFromSource_root_eq
      observation nontrivial prime 1 Nat.zero_lt_one,
    primePowerSelectedCharacterReadFromSource_root_eq
      observation nontrivial prime 1 Nat.zero_lt_one,
    EulerDiagonal.generatedPrimeCharacterLeakage_eq_cpow_sub,
    primePowerUnit_one,
    complexPowerCharacter_prime, complexPowerCharacter_prime]
  ring

theorem primePowerEulerWeightedQuadraticFromSource_root_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    primePowerEulerWeightedQuadraticFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime 1 =
      EulerDiagonal.eulerWeightedPrimeLeakage observation prime := by
  unfold primePowerEulerWeightedQuadraticFromSource
    EulerDiagonal.eulerWeightedPrimeLeakage
  rw [primePowerEulerWeightFromSource_root_eq
      observation nontrivial prime 1 Nat.zero_lt_one,
    primePowerCharacterLeakageReadFromSource_root_one,
    EulerDiagonal.globalEulerLogOccurrence_prime_coefficient]

end
end Quadratic
end PrimePower
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
