import H0mework.Arithmetic.RiemannMellinOrbit.PositiveMellinTateOrbit

/-!
# Zero-owned positive Mellin Tate orbit

The conjugate generated zero supplies the parameter `conj(s)/2`, which is
literally `1/2 - reversal(s)/2`.  Tate inversion therefore sends its generated
Gaussian relation to the reversal relation.  This module descends that map to
the full positive-dilation orbit quotients and proves exact preservation of
their Mellin functionals.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

theorem half_sub_reversalHalf_eq_conjugateHalf (s : ℂ) :
    (1 / 2 : ℂ) - coordinateReversal s / 2 =
      starRingEnd ℂ s / 2 := by
  unfold coordinateReversal
  ring

def conjugateZeroObservation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :
    GeneratedRiemannZeroObservationAt owner :=
  GeneratedRiemannZeroObservationAt.ofMathlibZero owner
    (starRingEnd ℂ observation.coordinate)
    observation.conjugate_mathlibZero

theorem conjugateForReversal_hasMellin_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HasMellin (generatedClozelGaussianRemainderKernel owner)
      ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2) 0 := by
  have source :=
    generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
      (conjugateZeroObservation observation)
      (observation.conjugate_nontrivial nontrivial)
  change HasMellin (generatedClozelGaussianRemainderKernel owner)
    (starRingEnd ℂ observation.coordinate / 2) 0 at source
  rw [half_sub_reversalHalf_eq_conjugateHalf]
  exact source

def conjugateForReversalPositiveRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule
      ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2) :=
  positiveClozelMellinRelation owner
    ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2)
    (conjugateForReversal_hasMellin_zero observation nontrivial).1

def reversalPositiveMellinRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule
      (coordinateReversal observation.coordinate / 2) :=
  positiveClozelMellinRelation owner
    (coordinateReversal observation.coordinate / 2)
    (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1

theorem positiveMellinTateMap_conjugateForReversal
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinTateMap
        (coordinateReversal observation.coordinate / 2)
        (conjugateForReversalPositiveRelation observation nontrivial) =
      reversalPositiveMellinRelation observation nontrivial := by
  exact positiveMellinTateMap_clozelRelation owner
    (coordinateReversal observation.coordinate / 2)
    (conjugateForReversal_hasMellin_zero observation nontrivial).1
    (generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial).1

theorem conjugateForReversalPositiveRelation_annihilated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinFunctional
        ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2)
        (conjugateForReversalPositiveRelation observation nontrivial) = 0 := by
  let zeroIncidence :=
    conjugateForReversal_hasMellin_zero observation nontrivial
  change positiveMellinFunctional
      ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2)
      (restrictPositiveMellin _
        ⟨generatedClozelGaussianRemainderKernel owner,
          zeroIncidence.1⟩) = 0
  rw [positiveMellinFunctional_restrictPositive]
  exact zeroIncidence.2

theorem reversalPositiveMellinRelation_annihilated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinFunctional
        (coordinateReversal observation.coordinate / 2)
        (reversalPositiveMellinRelation observation nontrivial) = 0 := by
  let zeroIncidence :=
    generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
      observation nontrivial
  change positiveMellinFunctional
      (coordinateReversal observation.coordinate / 2)
      (restrictPositiveMellin _
        ⟨generatedClozelGaussianRemainderKernel owner,
          zeroIncidence.1⟩) = 0
  rw [positiveMellinFunctional_restrictPositive]
  exact zeroIncidence.2

def zeroOwnedPositiveMellinTateOrbitMap
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PositiveDomainMellinOrbitQuotient
        ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2)
        (conjugateForReversalPositiveRelation observation nontrivial) →ₗ[ℂ]
      PositiveDomainMellinOrbitQuotient
        (coordinateReversal observation.coordinate / 2)
        (reversalPositiveMellinRelation observation nontrivial) :=
  positiveMellinTateOrbitMap
    (coordinateReversal observation.coordinate / 2)
    (conjugateForReversalPositiveRelation observation nontrivial)
    (reversalPositiveMellinRelation observation nontrivial)
    (positiveMellinTateMap_conjugateForReversal observation nontrivial)

theorem zeroOwnedPositiveMellinTateOrbitMap_functional
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : PositiveDomainMellinOrbitQuotient
      ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2)
      (conjugateForReversalPositiveRelation observation nontrivial)) :
    positiveDomainMellinOrbitQuotientFunctional
        (coordinateReversal observation.coordinate / 2)
        (reversalPositiveMellinRelation observation nontrivial)
        (reversalPositiveMellinRelation_annihilated observation nontrivial)
        (zeroOwnedPositiveMellinTateOrbitMap observation nontrivial value) =
      positiveDomainMellinOrbitQuotientFunctional
        ((1 / 2 : ℂ) - coordinateReversal observation.coordinate / 2)
        (conjugateForReversalPositiveRelation observation nontrivial)
        (conjugateForReversalPositiveRelation_annihilated
          observation nontrivial) value := by
  exact positiveDomainFunctional_tateOrbitMap
    (coordinateReversal observation.coordinate / 2)
    (conjugateForReversalPositiveRelation observation nontrivial)
    (reversalPositiveMellinRelation observation nontrivial)
    (positiveMellinTateMap_conjugateForReversal observation nontrivial)
    (conjugateForReversalPositiveRelation_annihilated
      observation nontrivial)
    (reversalPositiveMellinRelation_annihilated observation nontrivial)
    value

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
