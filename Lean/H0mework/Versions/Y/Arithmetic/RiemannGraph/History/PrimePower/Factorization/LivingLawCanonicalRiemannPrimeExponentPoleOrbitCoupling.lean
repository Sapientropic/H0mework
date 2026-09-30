import H0mework.Versions.Y.Arithmetic.PoleOrbit.PositiveRealization.ClozelAllPlaceOrbitPositiveEnergy
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentFaithfulRealization

/-!
# Prime-exponent coupling to the complete pole orbit

The factorization basis acts on one complete all-place pole state.  Integral
prime products, the Archimedean complete orbit, its positive energy, and its
Mellin character are therefore sibling reads of one source carrier.  No free
orthogonal auxiliary coordinate is adjoined.
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

open AllPlaceOriginDefect.Orbit
open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

/-- Coefficient form of the complete pole orbit action. -/
def primeExponentPoleOrbitCoefficientMap
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z) :
    (PrimeExponentLattice →₀ ℤ) →ₗ[ℤ]
      AllPlaceOriginOrbitJointCarrier z :=
  (Finsupp.liftAddHom fun exponent : PrimeExponentLattice =>
    AddMonoidHom.flip
      (smulAddHom ℤ (AllPlaceOriginOrbitJointCarrier z))
      (allPlaceOriginOrbitDilationAction z
        (scaleSquare (primeExponentScale exponent))
        (scaleSquare_pos (primeExponentScale exponent)) pole)
    ).toIntLinearMap

/-- A complete pole state acted on by every generated finite prime-exponent
scale. -/
def primeExponentPoleOrbitMap
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      AllPlaceOriginOrbitJointCarrier z :=
  (primeExponentPoleOrbitCoefficientMap z pole).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem primeExponentPoleOrbitMap_single
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z)
    (exponent : PrimeExponentLattice) (coefficient : ℤ) :
    primeExponentPoleOrbitMap z pole
        (AddMonoidAlgebra.single exponent coefficient) =
      coefficient • allPlaceOriginOrbitDilationAction z
        (scaleSquare (primeExponentScale exponent))
        (scaleSquare_pos (primeExponentScale exponent)) pole := by
  simp [primeExponentPoleOrbitMap, primeExponentPoleOrbitCoefficientMap]

theorem allPlaceOriginOrbitDilationAction_one
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z) :
    allPlaceOriginOrbitDilationAction z 1 (by positivity) pole = pole := by
  apply Prod.ext
  · change quarterDilationTestAction z 1 (by positivity) pole.1 = pole.1
    simpa only [LinearMap.id_apply] using LinearMap.congr_fun
      (quarterDilationTestAction_one z) pole.1
  · rcases pole.2.2 with ⟨test, pole_eq⟩
    have sourceEq : coPoissonLogOrbitSourceMap test = pole.2 := by
      apply Subtype.ext
      exact pole_eq
    change quarterMuntzOrbitDilationAction 1 (by positivity) pole.2 = pole.2
    rw [← sourceEq, quarterMuntzOrbitDilationAction_source]
    apply Subtype.ext
    change coPoissonLogOrbitMap
        (quarterMuntzSchwartzDilationAction 1 (by positivity) test) =
      coPoissonLogOrbitMap test
    congr 1
    apply SchwartzMap.ext
    intro x
    simp [quarterMuntzSchwartzDilationAction,
      positiveMellinQuarterDilationWeight]

theorem primeExponentPoleOrbitMap_zero_basis
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z) :
    primeExponentPoleOrbitMap z pole
        (AddMonoidAlgebra.single 0 1) = pole := by
  rw [primeExponentPoleOrbitMap_single, one_smul,
    primeExponentScale_zero]
  simpa [scaleSquare, scaleValue] using
    allPlaceOriginOrbitDilationAction_one z pole

/-- Prime-power source boundary in the complete orbit face. -/
theorem primeExponentPoleOrbitMap_boundaryValue
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z)
    (index : ConductorPrimePowerIndex) :
    primeExponentPoleOrbitMap z pole (factorizationBoundaryValue index) =
      pole - allPlaceOriginOrbitDilationAction z
        (scaleSquare (primePowerUnit index.1 index.2.1))
        (scaleSquare_pos (primePowerUnit index.1 index.2.1)) pole := by
  rw [factorizationBoundaryValue, map_sub,
    primeExponentPoleOrbitMap_zero_basis,
    primeExponentPoleOrbitMap_single, one_smul,
    primeExponentScale_primePower]

/-- Positive-energy sibling generated from the same factorization carrier. -/
def primeExponentPolePositiveEnergyMap
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      PositiveMellinQuarterEnergy :=
  (allPlaceOrbitPositiveEnergyMap z).restrictScalars ℤ |>.comp
    (primeExponentPoleOrbitMap z pole)

/-- Mellin sibling generated from the same factorization carrier. -/
def primeExponentPoleMellinMap
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  (allPlaceOrbitMellinFunctional z).restrictScalars ℤ |>.comp
    (primeExponentPoleOrbitMap z pole)

def selectedPrimeExponentPoleOrbitMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      AllPlaceOriginOrbitJointCarrier
        (selectedCoPoissonMuntzParameter observation) :=
  primeExponentPoleOrbitMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedAllPlacePoleOrbitJointValue observation nontrivial)

def reversalPrimeExponentPoleOrbitMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      AllPlaceOriginOrbitJointCarrier
        (reversalCoPoissonMuntzParameter observation) :=
  primeExponentPoleOrbitMap
    (reversalCoPoissonMuntzParameter observation)
    (reversalAllPlacePoleOrbitJointValue observation nontrivial)

def selectedPrimeExponentPolePositiveEnergyMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      PositiveMellinQuarterEnergy :=
  primeExponentPolePositiveEnergyMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedAllPlacePoleOrbitJointValue observation nontrivial)

def reversalPrimeExponentPolePositiveEnergyMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ]
      PositiveMellinQuarterEnergy :=
  primeExponentPolePositiveEnergyMap
    (reversalCoPoissonMuntzParameter observation)
    (reversalAllPlacePoleOrbitJointValue observation nontrivial)

def selectedPrimeExponentPoleMellinMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  primeExponentPoleMellinMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedAllPlacePoleOrbitJointValue observation nontrivial)

def reversalPrimeExponentPoleMellinMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  primeExponentPoleMellinMap
    (reversalCoPoissonMuntzParameter observation)
    (reversalAllPlacePoleOrbitJointValue observation nontrivial)

theorem primeExponentPolePositiveEnergyMap_single
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (pole : AllPlaceOriginOrbitJointCarrier z)
    (exponent : PrimeExponentLattice) :
    primeExponentPolePositiveEnergyMap z pole
        (AddMonoidAlgebra.single exponent 1) =
      positiveMellinQuarterEnergyTranslationIsometry
        (Real.log (scaleSquare (primeExponentScale exponent)))
        (allPlaceOrbitPositiveEnergyMap z pole) := by
  change allPlaceOrbitPositiveEnergyMap z
      (primeExponentPoleOrbitMap z pole
        (AddMonoidAlgebra.single exponent 1)) = _
  rw [primeExponentPoleOrbitMap_single, one_smul]
  exact allPlaceOrbitPositiveEnergyMap_dilation z positiveZ belowHalf
    (scaleSquare (primeExponentScale exponent))
    (scaleSquare_pos (primeExponentScale exponent)) pole

theorem primeExponentPoleMellinMap_single
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z)
    (poleRead : allPlaceOrbitMellinFunctional z pole = 1)
    (exponent : PrimeExponentLattice) :
    primeExponentPoleMellinMap z pole
        (AddMonoidAlgebra.single exponent 1) =
      quarterDilationCharacter z
        (scaleSquare (primeExponentScale exponent)) := by
  change allPlaceOrbitMellinFunctional z
      (primeExponentPoleOrbitMap z pole
        (AddMonoidAlgebra.single exponent 1)) = _
  rw [primeExponentPoleOrbitMap_single, one_smul]
  change quarterMellinL2Functional z
      (quarterDilationTestAction z
        (scaleSquare (primeExponentScale exponent))
        (scaleSquare_pos (primeExponentScale exponent)) pole.1) = _
  have eigen := LinearMap.congr_fun
    (quarterDilationFunctional_eigenlaw z
      (scaleSquare (primeExponentScale exponent))
      (scaleSquare_pos (primeExponentScale exponent))) pole.1
  change quarterMellinL2Functional z
      (quarterDilationTestAction z
        (scaleSquare (primeExponentScale exponent))
        (scaleSquare_pos (primeExponentScale exponent)) pole.1) =
      quarterDilationCharacter z
        (scaleSquare (primeExponentScale exponent)) •
        quarterMellinL2Functional z pole.1 at eigen
  change quarterMellinL2Functional z pole.1 = 1 at poleRead
  rw [eigen, poleRead, smul_eq_mul, mul_one]

theorem primeExponentPoleMellinMap_boundaryValue
    (z : ℂ) (pole : AllPlaceOriginOrbitJointCarrier z)
    (poleRead : allPlaceOrbitMellinFunctional z pole = 1)
    (index : ConductorPrimePowerIndex) :
    primeExponentPoleMellinMap z pole (factorizationBoundaryValue index) =
      1 - quarterDilationCharacter z
        (scaleSquare (primePowerUnit index.1 index.2.1)) := by
  rw [factorizationBoundaryValue, map_sub,
    primeExponentPoleMellinMap_single z pole poleRead,
    primeExponentPoleMellinMap_single z pole poleRead,
    primeExponentScale_zero, primeExponentScale_primePower]
  simp [quarterDilationCharacter, scaleSquare, scaleValue]

theorem selectedPrimeExponentPoleMellinMap_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (exponent : PrimeExponentLattice) :
    primeExponentPoleMellinMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial)
        (AddMonoidAlgebra.single exponent 1) =
      quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare (primeExponentScale exponent)) := by
  apply primeExponentPoleMellinMap_single
  change quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation)
      (selectedAllPlacePoleOrbitJointValue observation nontrivial).1 = 1
  rw [selectedAllPlacePoleOrbit_fst,
    selectedModifiedWeakFEPoleTraceTest_functional_one]

theorem reversalPrimeExponentPoleMellinMap_single
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (exponent : PrimeExponentLattice) :
    primeExponentPoleMellinMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial)
        (AddMonoidAlgebra.single exponent 1) =
      quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare (primeExponentScale exponent)) := by
  apply primeExponentPoleMellinMap_single
  change quarterMellinL2Functional
      (reversalCoPoissonMuntzParameter observation)
      (reversalAllPlacePoleOrbitJointValue observation nontrivial).1 = 1
  rw [reversalAllPlacePoleOrbit_fst,
    reversalModifiedWeakFEPoleTraceTest_functional_one]

theorem selectedPrimeExponentPolePositiveEnergy_base_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPolePositiveEnergyMap observation nontrivial
        (AddMonoidAlgebra.single 0 1) ≠ 0 := by
  change allPlaceOrbitPositiveEnergyMap
      (selectedCoPoissonMuntzParameter observation)
      (primeExponentPoleOrbitMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial)
        (AddMonoidAlgebra.single 0 1)) ≠ 0
  rw [primeExponentPoleOrbitMap_zero_basis]
  exact selectedAllPlacePole_positiveEnergy_ne_zero observation nontrivial

theorem reversalPrimeExponentPolePositiveEnergy_base_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPolePositiveEnergyMap observation nontrivial
        (AddMonoidAlgebra.single 0 1) ≠ 0 := by
  change allPlaceOrbitPositiveEnergyMap
      (reversalCoPoissonMuntzParameter observation)
      (primeExponentPoleOrbitMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial)
        (AddMonoidAlgebra.single 0 1)) ≠ 0
  rw [primeExponentPoleOrbitMap_zero_basis]
  exact reversalAllPlacePole_positiveEnergy_ne_zero observation nontrivial

theorem selectedPrimeExponentPoleMellin_boundaryValue
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    selectedPrimeExponentPoleMellinMap observation nontrivial
        (factorizationBoundaryValue index) =
      1 - quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare (primePowerUnit index.1 index.2.1)) := by
  apply primeExponentPoleMellinMap_boundaryValue
  change quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation)
      (selectedAllPlacePoleOrbitJointValue observation nontrivial).1 = 1
  rw [selectedAllPlacePoleOrbit_fst,
    selectedModifiedWeakFEPoleTraceTest_functional_one]

theorem reversalPrimeExponentPoleMellin_boundaryValue
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (index : ConductorPrimePowerIndex) :
    reversalPrimeExponentPoleMellinMap observation nontrivial
        (factorizationBoundaryValue index) =
      1 - quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare (primePowerUnit index.1 index.2.1)) := by
  apply primeExponentPoleMellinMap_boundaryValue
  change quarterMellinL2Functional
      (reversalCoPoissonMuntzParameter observation)
      (reversalAllPlacePoleOrbitJointValue observation nontrivial).1 = 1
  rw [reversalAllPlacePoleOrbit_fst,
    reversalModifiedWeakFEPoleTraceTest_functional_one]

/-- Root-installable mathematical payload.  All reads are generated from one
multiplicative carrier, and the receipt square recovers the already installed
integral boundary. -/
structure GeneratedPrimeExponentPoleCouplingFaceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) where
  private mk ::
  receiptMap : ConductorPrimePowerCurrent →ₗ[ℤ]
    PrimeExponentFactorizationCarrier
  integralRealization : PrimeExponentFactorizationCarrier →ₗ[ℤ]
    IntegralScaleCarrier
  selectedOrbit : PrimeExponentFactorizationCarrier →ₗ[ℤ]
    AllPlaceOriginOrbitJointCarrier
      (selectedCoPoissonMuntzParameter observation)
  reversalOrbit : PrimeExponentFactorizationCarrier →ₗ[ℤ]
    AllPlaceOriginOrbitJointCarrier
      (reversalCoPoissonMuntzParameter observation)
  selectedEnergy : PrimeExponentFactorizationCarrier →ₗ[ℤ]
    PositiveMellinQuarterEnergy
  reversalEnergy : PrimeExponentFactorizationCarrier →ₗ[ℤ]
    PositiveMellinQuarterEnergy
  selectedMellin : PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ
  reversalMellin : PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ
  integralSquare : integralRealization.comp receiptMap =
    integralBoundaryMap observation nontrivial
  integralRealization_injective : Function.Injective integralRealization
  selectedEnergySquare : selectedEnergy =
    ((allPlaceOrbitPositiveEnergyMap
      (selectedCoPoissonMuntzParameter observation)).restrictScalars ℤ).comp
        selectedOrbit
  reversalEnergySquare : reversalEnergy =
    ((allPlaceOrbitPositiveEnergyMap
      (reversalCoPoissonMuntzParameter observation)).restrictScalars ℤ).comp
        reversalOrbit
  selectedMellinSquare : selectedMellin =
    ((allPlaceOrbitMellinFunctional
      (selectedCoPoissonMuntzParameter observation)).restrictScalars ℤ).comp
        selectedOrbit
  reversalMellinSquare : reversalMellin =
    ((allPlaceOrbitMellinFunctional
      (reversalCoPoissonMuntzParameter observation)).restrictScalars ℤ).comp
        reversalOrbit
  selectedBaseEnergy_ne_zero :
    selectedEnergy (AddMonoidAlgebra.single 0 1) ≠ 0
  reversalBaseEnergy_ne_zero :
    reversalEnergy (AddMonoidAlgebra.single 0 1) ≠ 0
  selectedReceiptRead : ∀ index,
    selectedMellin (factorizationBoundaryValue index) =
      1 - quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare (primePowerUnit index.1 index.2.1))
  reversalReceiptRead : ∀ index,
    reversalMellin (factorizationBoundaryValue index) =
      1 - quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation)
        (scaleSquare (primePowerUnit index.1 index.2.1))

def generatedPrimeExponentPoleCouplingFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    GeneratedPrimeExponentPoleCouplingFaceAt observation nontrivial where
  receiptMap := factorizationBoundaryMap
  integralRealization := primeExponentIntegralRealization.toLinearMap
  selectedOrbit := selectedPrimeExponentPoleOrbitMap observation nontrivial
  reversalOrbit := reversalPrimeExponentPoleOrbitMap observation nontrivial
  selectedEnergy :=
    selectedPrimeExponentPolePositiveEnergyMap observation nontrivial
  reversalEnergy :=
    reversalPrimeExponentPolePositiveEnergyMap observation nontrivial
  selectedMellin := selectedPrimeExponentPoleMellinMap observation nontrivial
  reversalMellin := reversalPrimeExponentPoleMellinMap observation nontrivial
  integralSquare := factorization_integral_square observation nontrivial
  integralRealization_injective :=
    primeExponentIntegralRealization_injective
  selectedEnergySquare := rfl
  reversalEnergySquare := rfl
  selectedMellinSquare := rfl
  reversalMellinSquare := rfl
  selectedBaseEnergy_ne_zero :=
    selectedPrimeExponentPolePositiveEnergy_base_ne_zero observation nontrivial
  reversalBaseEnergy_ne_zero :=
    reversalPrimeExponentPolePositiveEnergy_base_ne_zero observation nontrivial
  selectedReceiptRead :=
    selectedPrimeExponentPoleMellin_boundaryValue observation nontrivial
  reversalReceiptRead :=
    reversalPrimeExponentPoleMellin_boundaryValue observation nontrivial

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
