import H0mework.Realization.Feature.GramPerfectification
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleKernelCompatibility

/-!
# Prime-exponent pole energy coimage

The complexified factorization carrier is quotiented only by the kernel of
its actual positive-energy face.  The Mellin coordinate descends uniquely to
that quotient because the source-level kernel compatibility has already been
proved.  Thus the algebraic energy/Mellin premise is recovered by the generic
feature-perfectification engine; no bounded extension or spectral-support
premise enters.
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
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History
namespace PrimePowerCurrent

open ClozelGeneralizedDual
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open Character.GlobalCoPoissonCurrent
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedIntegralCoherentCompletion

noncomputable section

abbrev PrimeExponentPoleComplexCarrier :=
  ComplexifiedCarrier PrimeExponentFactorizationCarrier

def primeExponentPoleComplexBase : PrimeExponentPoleComplexCarrier :=
  1 ⊗ₜ[ℤ] AddMonoidAlgebra.single 0 1

abbrev SelectedPrimeExponentPoleEnergyCoimage
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Carrier (complexifiedFeature
    (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial))

abbrev ReversalPrimeExponentPoleEnergyCoimage
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  Carrier (complexifiedFeature
    (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial))

def selectedPrimeExponentPoleEnergyCanonicalMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentPoleComplexCarrier →ₗ[ℂ]
      SelectedPrimeExponentPoleEnergyCoimage observation nontrivial :=
  canonicalMap (complexifiedFeature
    (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial))

def reversalPrimeExponentPoleEnergyCanonicalMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentPoleComplexCarrier →ₗ[ℂ]
      ReversalPrimeExponentPoleEnergyCoimage observation nontrivial :=
  canonicalMap (complexifiedFeature
    (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial))

/-- The selected Mellin coordinate on the faithful energy coimage. -/
def selectedPrimeExponentPoleEnergyMellinFactor
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SelectedPrimeExponentPoleEnergyCoimage observation nontrivial →ₗ[ℂ] ℂ :=
  canonicalFactor
    (complexifiedFeature
      (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial))
    (complexifiedLinearMap
      (selectedPrimeExponentPoleMellinMap observation nontrivial))
    (selectedPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial)

/-- The reversal Mellin coordinate on the faithful energy coimage. -/
def reversalPrimeExponentPoleEnergyMellinFactor
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReversalPrimeExponentPoleEnergyCoimage observation nontrivial →ₗ[ℂ] ℂ :=
  canonicalFactor
    (complexifiedFeature
      (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial))
    (complexifiedLinearMap
      (reversalPrimeExponentPoleMellinMap observation nontrivial))
    (reversalPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial)

theorem selectedPrimeExponentPoleEnergyMellinFactor_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (selectedPrimeExponentPoleEnergyMellinFactor observation nontrivial).comp
        (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial) =
      complexifiedLinearMap
        (selectedPrimeExponentPoleMellinMap observation nontrivial) :=
  canonicalFactor_comp_canonicalMap _ _
    (selectedPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial)

theorem reversalPrimeExponentPoleEnergyMellinFactor_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (reversalPrimeExponentPoleEnergyMellinFactor observation nontrivial).comp
        (reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial) =
      complexifiedLinearMap
        (reversalPrimeExponentPoleMellinMap observation nontrivial) :=
  canonicalFactor_comp_canonicalMap _ _
    (reversalPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial)

theorem selectedPrimeExponentPoleEnergyMellinFactor_unique
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (other : SelectedPrimeExponentPoleEnergyCoimage
      observation nontrivial →ₗ[ℂ] ℂ)
    (readback : other.comp
        (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial) =
      complexifiedLinearMap
        (selectedPrimeExponentPoleMellinMap observation nontrivial)) :
    other = selectedPrimeExponentPoleEnergyMellinFactor
      observation nontrivial := by
  exact canonicalFactor_unique _ _
    (selectedPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial) other readback

theorem reversalPrimeExponentPoleEnergyMellinFactor_unique
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (other : ReversalPrimeExponentPoleEnergyCoimage
      observation nontrivial →ₗ[ℂ] ℂ)
    (readback : other.comp
        (reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial) =
      complexifiedLinearMap
        (reversalPrimeExponentPoleMellinMap observation nontrivial)) :
    other = reversalPrimeExponentPoleEnergyMellinFactor
      observation nontrivial := by
  exact canonicalFactor_unique _ _
    (reversalPrimeExponentPoleComplexEnergy_ker_le_mellin_ker
      observation nontrivial) other readback

theorem selectedPrimeExponentPoleEnergyCanonicalMap_base_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial
        primeExponentPoleComplexBase ≠ 0 := by
  intro baseZero
  let feature := complexifiedFeature
    (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial)
  have readback := LinearMap.congr_fun
    (faithfulFeature_comp_canonicalMap feature)
    primeExponentPoleComplexBase
  have featureZero : feature primeExponentPoleComplexBase = 0 := by
    rw [← readback]
    change faithfulFeature feature
      (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial
        primeExponentPoleComplexBase) = 0
    rw [baseZero, map_zero]
  apply selectedPrimeExponentPolePositiveEnergy_base_ne_zero
    observation nontrivial
  simpa [feature, primeExponentPoleComplexBase] using featureZero

theorem reversalPrimeExponentPoleEnergyCanonicalMap_base_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial
        primeExponentPoleComplexBase ≠ 0 := by
  intro baseZero
  let feature := complexifiedFeature
    (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial)
  have readback := LinearMap.congr_fun
    (faithfulFeature_comp_canonicalMap feature)
    primeExponentPoleComplexBase
  have featureZero : feature primeExponentPoleComplexBase = 0 := by
    rw [← readback]
    change faithfulFeature feature
      (reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial
        primeExponentPoleComplexBase) = 0
    rw [baseZero, map_zero]
  apply reversalPrimeExponentPolePositiveEnergy_base_ne_zero
    observation nontrivial
  simpa [feature, primeExponentPoleComplexBase] using featureZero

theorem selectedPrimeExponentPoleEnergyMellinFactor_base
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleEnergyMellinFactor observation nontrivial
        (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial
          primeExponentPoleComplexBase) = 1 := by
  have readback := LinearMap.congr_fun
    (selectedPrimeExponentPoleEnergyMellinFactor_source
      observation nontrivial) primeExponentPoleComplexBase
  rw [LinearMap.comp_apply] at readback
  rw [readback]
  rw [primeExponentPoleComplexBase, complexifiedLinearMap_tmul, one_smul]
  change primeExponentPoleMellinMap
      (selectedCoPoissonMuntzParameter observation)
      (AllPlaceOriginDefect.Orbit.selectedAllPlacePoleOrbitJointValue
        observation nontrivial)
      (AddMonoidAlgebra.single 0 1) = 1
  rw [selectedPrimeExponentPoleMellinMap_single]
  simp [primeExponentScale_zero, quarterDilationCharacter,
    scaleSquare, scaleValue]

theorem reversalPrimeExponentPoleEnergyMellinFactor_base
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPoleEnergyMellinFactor observation nontrivial
        (reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial
          primeExponentPoleComplexBase) = 1 := by
  have readback := LinearMap.congr_fun
    (reversalPrimeExponentPoleEnergyMellinFactor_source
      observation nontrivial) primeExponentPoleComplexBase
  rw [LinearMap.comp_apply] at readback
  rw [readback]
  rw [primeExponentPoleComplexBase, complexifiedLinearMap_tmul, one_smul]
  change primeExponentPoleMellinMap
      (reversalCoPoissonMuntzParameter observation)
      (AllPlaceOriginDefect.Orbit.reversalAllPlacePoleOrbitJointValue
        observation nontrivial)
      (AddMonoidAlgebra.single 0 1) = 1
  rw [reversalPrimeExponentPoleMellinMap_single]
  simp [primeExponentScale_zero, quarterDilationCharacter,
    scaleSquare, scaleValue]

theorem selectedPrimeExponentPoleEnergyMellinFactor_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleEnergyMellinFactor observation nontrivial ≠ 0 := by
  intro factorZero
  have base := selectedPrimeExponentPoleEnergyMellinFactor_base
    observation nontrivial
  rw [factorZero, LinearMap.zero_apply] at base
  norm_num at base

theorem reversalPrimeExponentPoleEnergyMellinFactor_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPoleEnergyMellinFactor observation nontrivial ≠ 0 := by
  intro factorZero
  have base := reversalPrimeExponentPoleEnergyMellinFactor_base
    observation nontrivial
  rw [factorZero, LinearMap.zero_apply] at base
  norm_num at base

/-- Root-installed canonical points in the two algebraic energy coimages.
The maps and their universal properties remain direct generated definitions,
rather than being duplicated in a large dependent payload. -/
abbrev GeneratedPrimeExponentPoleEnergyCoimageFaceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  SelectedPrimeExponentPoleEnergyCoimage observation nontrivial ×
    ReversalPrimeExponentPoleEnergyCoimage observation nontrivial

def generatedPrimeExponentPoleEnergyCoimageFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GeneratedPrimeExponentPoleEnergyCoimageFaceAt observation nontrivial :=
  (selectedPrimeExponentPoleEnergyCanonicalMap observation nontrivial
      primeExponentPoleComplexBase,
    reversalPrimeExponentPoleEnergyCanonicalMap observation nontrivial
      primeExponentPoleComplexBase)

theorem generatedPrimeExponentPoleEnergyCoimageFace_nonzero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (generatedPrimeExponentPoleEnergyCoimageFace
        observation nontrivial).1 ≠ 0 ∧
      (generatedPrimeExponentPoleEnergyCoimageFace
        observation nontrivial).2 ≠ 0 :=
  ⟨selectedPrimeExponentPoleEnergyCanonicalMap_base_ne_zero
      observation nontrivial,
    reversalPrimeExponentPoleEnergyCanonicalMap_base_ne_zero
      observation nontrivial⟩

theorem generatedPrimeExponentPoleEnergyCoimageFace_reads_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleEnergyMellinFactor observation nontrivial
        (generatedPrimeExponentPoleEnergyCoimageFace
          observation nontrivial).1 = 1 ∧
      reversalPrimeExponentPoleEnergyMellinFactor observation nontrivial
        (generatedPrimeExponentPoleEnergyCoimageFace
          observation nontrivial).2 = 1 :=
  ⟨selectedPrimeExponentPoleEnergyMellinFactor_base observation nontrivial,
    reversalPrimeExponentPoleEnergyMellinFactor_base observation nontrivial⟩

end
end PrimePowerCurrent
end History
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
