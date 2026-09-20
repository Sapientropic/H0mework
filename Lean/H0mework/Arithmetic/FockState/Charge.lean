import Mathlib.Data.Finsupp.Single
import H0mework.Arithmetic.Goldbach.ExactUnfolding
import H0mework.Foundation.Relations.ScalarDifferentialResidual
import H0mework.Arithmetic.FockState.ParentOccurrence

/-!
# Exact-owner two-particle charge

Every exact global-germ owner generates its own even-target factorization and
ordered prime candidates.  Their tensor kets are measured by an unconditional
additive charge map.  No candidate is assumed to land in the target fibre.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open ArithmeticGeneration
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalRiemann.ClozelGeneralizedDual
open CanonicalRiemann.ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedScalarDifferentialResidual

noncomputable section

def ownerEvenTargetOccurrence (owner : GlobalParentOwner) (index : Nat) :
    RootedAccountedUnfolding (ExactOccurrenceAdditivePointAt owner) :=
  evenTargetOccurrenceAt owner index

def ownerEvenTargetHistory (owner : GlobalParentOwner) (index : Nat) :
    UnitHistory :=
  evenTargetHistoryAt owner index

@[simp] theorem ownerEvenTargetOccurrence_root_exact
    (owner : GlobalParentOwner) (index : Nat) :
    (ownerEvenTargetOccurrence owner index).root.rootOccurrence = owner :=
  evenTargetOccurrenceAt_root_is_exact owner index

@[simp] theorem ownerEvenTargetHistory_eq_generate
    (owner : GlobalParentOwner) (index : Nat) :
    ownerEvenTargetHistory owner index =
      UnitHistory.generate (2 * (index + 1)) :=
  evenTargetHistoryAt_eq_generate owner index

def ownerEvenFactorization (owner : GlobalParentOwner) (index : Nat) :
    GeneratedUnitFactorizationAt (ownerEvenTargetHistory owner index) :=
  GeneratedUnitFactorizationAt.generate _

abbrev OwnerPrimeIndexAt (owner : GlobalParentOwner) (index : Nat) :=
  PrimeIndex (ownerEvenTargetHistory owner index)

abbrev OwnerPrimePairCandidateAt
    (owner : GlobalParentOwner) (index : Nat) :=
  OwnerPrimeIndexAt owner index × OwnerPrimeIndexAt owner index

def ownerFirstExponent
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    ExponentIndex (ownerEvenTargetHistory owner index) primeIndex :=
  ⟨0, multiplicity_pos _ primeIndex⟩

def ownerPrimeHistory
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) : UnitHistory :=
  (ownerEvenFactorization owner index).actualPrimePowerHistory primeIndex
    (ownerFirstExponent primeIndex)

theorem ownerPrimeHistory_isPrime
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    Nat.Prime (ownerPrimeHistory primeIndex).cardinalShadow := by
  simpa [ownerPrimeHistory,
    GeneratedUnitFactorizationAt.actualPrimePowerHistory,
    primePowerHistory, ownerFirstExponent, exponent] using
    (prime (ownerEvenTargetHistory owner index) primeIndex).property

@[simp] theorem ownerPrimeHistory_cardinalShadow
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    (ownerPrimeHistory primeIndex).cardinalShadow = primeIndex.1 := by
  simp [ownerPrimeHistory,
    GeneratedUnitFactorizationAt.actualPrimePowerHistory,
    primePowerHistory, ownerFirstExponent, exponent, prime]

/-- The prime carried by an exact-owner factorization row. -/
def ownerActualPrime
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) : Nat.Primes :=
  (ownerEvenFactorization owner index).actualPrime primeIndex

@[simp] theorem ownerActualPrime_value
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    (ownerActualPrime primeIndex : Nat) = primeIndex.1 :=
  rfl

def ownerAdditiveEvaluation
    (owner : GlobalParentOwner) (index : Nat)
    (candidate : OwnerPrimePairCandidateAt owner index) : UnitHistory :=
  (ownerPrimeHistory candidate.1).parallel
    (ownerPrimeHistory candidate.2)

def ownerPrimeScaleUnit
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) : Units NNReal :=
  primePowerUnit (ownerActualPrime primeIndex) 1

@[simp] theorem ownerPrimeScaleUnit_value
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    (((ownerPrimeScaleUnit primeIndex : Units NNReal) : NNReal) : ℝ) =
      primeIndex.1 := by
  change scaleValue (primePowerUnit (ownerActualPrime primeIndex) 1) = _
  rw [primePowerUnit_value]
  simp [thetaDistributionPrimePower]

/-- The particle scale is the canonical prime-power coordinate at exponent
one, not a parallel positive-real re-encoding. -/
theorem ownerPrimeScaleUnit_eq_primePowerUnit
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    ownerPrimeScaleUnit primeIndex =
      primePowerUnit (ownerActualPrime primeIndex) 1 :=
  rfl

/-- Additive detector carrier; finite support is on actual nonnegative-real
charges, while the Fock source remains multiplicative and integral. -/
abbrev AdditiveChargeCarrier := NNReal →₀ ℤ

def pairChargeBasis (left right : Units NNReal) : AdditiveChargeCarrier :=
  Finsupp.single ((left : NNReal) + (right : NNReal)) 1

def pairChargeBilinear :
    IntegralOneParticle →ₗ[ℤ] IntegralOneParticle →ₗ[ℤ]
      AdditiveChargeCarrier :=
  canonicalBasis.constr ℤ fun left =>
    canonicalBasis.constr ℤ (pairChargeBasis left)

/-- Unconditional charge of an ordered two-particle tensor. -/
def pairCharge : OrderedParticleTwo →ₗ[ℤ] AdditiveChargeCarrier :=
  TensorProduct.lift pairChargeBilinear

@[simp] theorem pairCharge_delta_tmul_delta
    (left right : Units NNReal) :
    pairCharge (delta left ⊗ₜ[ℤ] delta right) = pairChargeBasis left right := by
  change pairChargeBilinear (delta left) (delta right) = _
  unfold pairChargeBilinear
  change (canonicalBasis.constr ℤ fun left =>
      canonicalBasis.constr ℤ (pairChargeBasis left))
    (canonicalBasis left) (canonicalBasis right) = _
  rw [canonicalBasis.constr_basis, canonicalBasis.constr_basis]

def ownerPrimeCoordinate
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) : ParentCarrier :=
  (GeneratedParentInterface.generate owner).primePowerCoordinate
    (ownerActualPrime primeIndex) 1

/-- The exact-owner one-particle state is read from its own parent interface. -/
def ownerPrimeOneParticle
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) : IntegralOneParticle :=
  (GeneratedParentInterface.generate owner).thetaRead
    (ownerPrimeCoordinate primeIndex)

@[simp] theorem ownerPrimeCoordinate_thetaRead
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    (GeneratedParentInterface.generate owner).thetaRead
        (ownerPrimeCoordinate primeIndex) =
      delta (ownerPrimeScaleUnit primeIndex) := by
  rfl

@[simp] theorem ownerPrimeOneParticle_eq_delta
    {owner : GlobalParentOwner} {index : Nat}
    (primeIndex : OwnerPrimeIndexAt owner index) :
    ownerPrimeOneParticle primeIndex =
      delta (ownerPrimeScaleUnit primeIndex) := by
  rfl

def primePairKet
    {owner : GlobalParentOwner} {index : Nat}
    (candidate : OwnerPrimePairCandidateAt owner index) : OrderedParticleTwo :=
  ownerPrimeOneParticle candidate.1 ⊗ₜ[ℤ]
    ownerPrimeOneParticle candidate.2

/-- Both tensor factors are read from the exact owner's canonical parent
interface. -/
theorem primePairKet_eq_owner_interface_tensor
    {owner : GlobalParentOwner} {index : Nat}
    (candidate : OwnerPrimePairCandidateAt owner index) :
    primePairKet candidate =
      (GeneratedParentInterface.generate owner).thetaRead
          (ownerPrimeCoordinate candidate.1) ⊗ₜ[ℤ]
        (GeneratedParentInterface.generate owner).thetaRead
          (ownerPrimeCoordinate candidate.2) :=
  rfl

def particleEvent
    {owner : GlobalParentOwner} {index : Nat}
    (candidate : OwnerPrimePairCandidateAt owner index) : ParentCarrier :=
  (GeneratedParentInterface.generate owner).pairCoordinate
    (primePairKet candidate)

theorem particleEvent_eq_owner_interface_pairCoordinate
    {owner : GlobalParentOwner} {index : Nat}
    (candidate : OwnerPrimePairCandidateAt owner index) :
    particleEvent candidate =
      (GeneratedParentInterface.generate owner).pairCoordinate
        ((GeneratedParentInterface.generate owner).thetaRead
              (ownerPrimeCoordinate candidate.1) ⊗ₜ[ℤ]
          (GeneratedParentInterface.generate owner).thetaRead
              (ownerPrimeCoordinate candidate.2)) :=
  rfl

def particleMeasurement : ParentCarrier →ₗ[ℤ] AdditiveChargeCarrier :=
  pairCharge.comp pairProjection

def targetCharge (index : Nat) : AdditiveChargeCarrier :=
  Finsupp.single (2 * (index + 1) : NNReal) 1

@[simp] theorem particleMeasurement_primePair
    {owner : GlobalParentOwner} {index : Nat}
    (candidate : OwnerPrimePairCandidateAt owner index) :
    particleMeasurement (particleEvent candidate) =
      Finsupp.single
        (((ownerPrimeScaleUnit candidate.1 : Units NNReal) : NNReal) +
          ((ownerPrimeScaleUnit candidate.2 : Units NNReal) : NNReal)) 1 := by
  change pairCharge (primePairKet candidate) = _
  rw [primePairKet, ownerPrimeOneParticle_eq_delta,
    ownerPrimeOneParticle_eq_delta, pairCharge_delta_tmul_delta]
  rfl

/-- The exact inverse-fibre law, with no fibre or landing premise. -/
theorem primePairKet_charge_target_iff
    {owner : GlobalParentOwner} {index : Nat}
    (candidate : OwnerPrimePairCandidateAt owner index) :
    particleMeasurement (particleEvent candidate) = targetCharge index ↔
      ownerAdditiveEvaluation owner index candidate =
        ownerEvenTargetHistory owner index := by
  rw [particleMeasurement_primePair]
  constructor
  · intro charge_eq
    have key_eq := (Finsupp.single_left_inj
      (by norm_num : (1 : ℤ) ≠ 0)).mp charge_eq
    have real_eq := congrArg (fun value : NNReal => (value : ℝ)) key_eq
    simp only [NNReal.coe_add, ownerPrimeScaleUnit_value] at real_eq
    apply UnitHistory.eq_of_cardinalShadow_eq
    calc
      (ownerAdditiveEvaluation owner index candidate).cardinalShadow =
          candidate.1.1 + candidate.2.1 := by
        simp [ownerAdditiveEvaluation]
      _ = 2 * (index + 1) := by exact_mod_cast real_eq
      _ = (ownerEvenTargetHistory owner index).cardinalShadow := by
        simp [ownerEvenTargetHistory_eq_generate]
  · intro landing
    have cardinal_eq := congrArg UnitHistory.cardinalShadow landing
    have prime_sum : candidate.1.1 + candidate.2.1 = 2 * (index + 1) := by
      calc
        candidate.1.1 + candidate.2.1 =
            (ownerAdditiveEvaluation owner index candidate).cardinalShadow := by
          simp [ownerAdditiveEvaluation]
        _ = (ownerEvenTargetHistory owner index).cardinalShadow := cardinal_eq
        _ = 2 * (index + 1) := by
          simp [ownerEvenTargetHistory_eq_generate]
    apply (Finsupp.single_left_inj
      (by norm_num : (1 : ℤ) ≠ 0)).2
    apply NNReal.eq
    simp only [NNReal.coe_add, ownerPrimeScaleUnit_value]
    exact_mod_cast prime_sum

/-! The faithful observable coimage is the generic scalar differential
quotient; the measurement inverse fibre itself remains its kernel/cosets. -/

abbrev ParticleMeasurementCoimage := ResidualCarrier particleMeasurement

def particleMeasurementCoimage :
    ParentCarrier →ₗ[ℤ] ParticleMeasurementCoimage :=
  canonicalResidual particleMeasurement

theorem particleMeasurementCoimage_zero_iff (state : ParentCarrier) :
    particleMeasurementCoimage state = 0 ↔ particleMeasurement state = 0 :=
  canonicalResidual_eq_zero_iff particleMeasurement state

theorem particleMeasurementCoimage_universal
    {Q : Type*} [AddCommGroup Q] [Module ℤ Q]
    (read : ParentCarrier →ₗ[ℤ] Q)
    (compatible : LinearMap.ker particleMeasurement ≤ LinearMap.ker read) :
    ∃! factor : ParticleMeasurementCoimage →ₗ[ℤ] Q,
      factor.comp particleMeasurementCoimage = read :=
  universal_factorization particleMeasurement read compatible

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
