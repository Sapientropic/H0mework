import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.LivingLawCanonicalRiemannPrimeExponentPoleKernelCompatibility
import H0mework.Versions.Y.Arithmetic.RiemannGraph.ZeroJointStateModuleOccurrence

/-!
# Prime-exponent pole Riesz-energy/vertical split

The spectral state is read from the fixed zero-owned joint-state root.  On
the actual prime-exponent quarter-test factorization, its graph pairing
splits the Mellin coordinate into the energy Riesz pairing and the scalar
vertical trace.  The scalar inner-product convention is kept literally.
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
open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedHilbertCokernel
open SourceGeneratedIntegralCharacterGroupRing
open scoped InnerProductSpace

noncomputable section

abbrev selectedPrimeExponentPoleRootSpectralState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    JointGraphTarget :=
  ((zeroOwnedJointStateModuleOccurrence
    observation nontrivial).root.2).selectedSpectralState

abbrev reversalPrimeExponentPoleRootSpectralState
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    JointGraphTarget :=
  ((zeroOwnedJointStateModuleOccurrence
    observation nontrivial).root.2).reversalSpectralState

theorem selectedPrimeExponentPoleRootState_quarterTest_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (selectedCoPoissonMuntzParameter observation)) :
    inner ℂ (selectedPrimeExponentPoleRootSpectralState
        observation nontrivial)
        (graphFeature
          (quarterMellinL2Feature
            (selectedCoPoissonMuntzParameter observation))
          (quarterMellinL2Functional
            (selectedCoPoissonMuntzParameter observation)) value) =
      quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation) value := by
  unfold selectedPrimeExponentPoleRootSpectralState
  rw [zeroOwnedJointStateModuleOccurrence_root_selectedState]
  let feature := quarterMellinL2Feature
    (selectedCoPoissonMuntzParameter observation)
  let functional := quarterMellinL2Functional
    (selectedCoPoissonMuntzParameter observation)
  let relation := coPoissonQuarterMellinConvergentMap
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
  let T := relationGraphMap feature functional relation
  let sourcePoint := graphSourceMap feature functional value
  have projectionRead :
      inner ℂ
          (selectedRieszOrthogonalRepresentative observation nontrivial)
          (residual T sourcePoint) = functional value := by
    rw [← quotientOrthogonalEquiv_quotientClass T sourcePoint]
    exact selectedRieszOrthogonalRepresentative_source_readback
      observation nontrivial value
  have literalRead :
      inner ℂ
          (selectedRieszOrthogonalRepresentative observation nontrivial :
            GraphHilbertAmbient feature functional)
          sourcePoint = functional value := by
    rw [← projectionRead]
    symm
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (selectedRieszOrthogonalRepresentative observation nontrivial)
      sourcePoint
  change inner ℂ
      (graphHilbertAmbientRealization feature functional
        (selectedRieszOrthogonalRepresentative observation nontrivial))
      (graphFeature feature functional value) = functional value
  rw [← graphHilbertAmbientRealization_source_readback
    feature functional value, LinearIsometry.inner_map_map]
  exact literalRead

theorem reversalPrimeExponentPoleRootState_quarterTest_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (reversalCoPoissonMuntzParameter observation)) :
    inner ℂ (reversalPrimeExponentPoleRootSpectralState
        observation nontrivial)
        (graphFeature
          (quarterMellinL2Feature
            (reversalCoPoissonMuntzParameter observation))
          (quarterMellinL2Functional
            (reversalCoPoissonMuntzParameter observation)) value) =
      quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation) value := by
  unfold reversalPrimeExponentPoleRootSpectralState
  rw [zeroOwnedJointStateModuleOccurrence_root_reversalState]
  let feature := quarterMellinL2Feature
    (reversalCoPoissonMuntzParameter observation)
  let functional := quarterMellinL2Functional
    (reversalCoPoissonMuntzParameter observation)
  let relation := coPoissonQuarterMellinConvergentMap
    (reversalCoPoissonMuntzParameter observation)
    (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
    (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
  let T := relationGraphMap feature functional relation
  let sourcePoint := graphSourceMap feature functional value
  have projectionRead :
      inner ℂ
          (reversalRieszOrthogonalRepresentative observation nontrivial)
          (residual T sourcePoint) = functional value := by
    rw [← quotientOrthogonalEquiv_quotientClass T sourcePoint]
    exact reversalRieszOrthogonalRepresentative_source_readback
      observation nontrivial value
  have literalRead :
      inner ℂ
          (reversalRieszOrthogonalRepresentative observation nontrivial :
            GraphHilbertAmbient feature functional)
          sourcePoint = functional value := by
    rw [← projectionRead]
    symm
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (reversalRieszOrthogonalRepresentative observation nontrivial)
      sourcePoint
  change inner ℂ
      (graphHilbertAmbientRealization feature functional
        (reversalRieszOrthogonalRepresentative observation nontrivial))
      (graphFeature feature functional value) = functional value
  rw [← graphHilbertAmbientRealization_source_readback
    feature functional value, LinearIsometry.inner_map_map]
  exact literalRead

theorem selectedPrimeExponentPoleRootState_quarterTest_verticalSplit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (selectedCoPoissonMuntzParameter observation)) :
    quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation) value =
      inner ℂ
          (selectedPrimeExponentPoleRootSpectralState
            observation nontrivial).fst
          (quarterMellinL2Feature
            (selectedCoPoissonMuntzParameter observation) value) +
        inner ℂ
          (selectedPrimeExponentPoleRootSpectralState
            observation nontrivial).snd
          (quarterMellinL2Functional
            (selectedCoPoissonMuntzParameter observation) value) := by
  have readback := selectedPrimeExponentPoleRootState_quarterTest_readback
    observation nontrivial value
  rw [WithLp.prod_inner_apply] at readback
  exact readback.symm

theorem reversalPrimeExponentPoleRootState_quarterTest_verticalSplit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (reversalCoPoissonMuntzParameter observation)) :
    quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation) value =
      inner ℂ
          (reversalPrimeExponentPoleRootSpectralState
            observation nontrivial).fst
          (quarterMellinL2Feature
            (reversalCoPoissonMuntzParameter observation) value) +
        inner ℂ
          (reversalPrimeExponentPoleRootSpectralState
            observation nontrivial).snd
          (quarterMellinL2Functional
            (reversalCoPoissonMuntzParameter observation) value) := by
  have readback := reversalPrimeExponentPoleRootState_quarterTest_readback
    observation nontrivial value
  rw [WithLp.prod_inner_apply] at readback
  exact readback.symm

/-- Root-owned Riesz pairing with the selected factor energy. -/
def selectedPrimeExponentPoleRieszEnergyPair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  ((innerSL ℂ (selectedPrimeExponentPoleRootSpectralState
    observation nontrivial).fst).toLinearMap.restrictScalars ℤ).comp
      (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial)

/-- Root-owned scalar vertical trace.  On `ℂ`, `innerSL` retains the
conjugation of the fixed state scalar. -/
def selectedPrimeExponentPoleVerticalScalarTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  ((innerSL ℂ (selectedPrimeExponentPoleRootSpectralState
    observation nontrivial).snd).toLinearMap.restrictScalars ℤ).comp
      (selectedPrimeExponentPoleMellinMap observation nontrivial)

def reversalPrimeExponentPoleRieszEnergyPair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  ((innerSL ℂ (reversalPrimeExponentPoleRootSpectralState
    observation nontrivial).fst).toLinearMap.restrictScalars ℤ).comp
      (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial)

def reversalPrimeExponentPoleVerticalScalarTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PrimeExponentFactorizationCarrier →ₗ[ℤ] ℂ :=
  ((innerSL ℂ (reversalPrimeExponentPoleRootSpectralState
    observation nontrivial).snd).toLinearMap.restrictScalars ℤ).comp
      (reversalPrimeExponentPoleMellinMap observation nontrivial)

private theorem selectedPrimeExponentPole_baseMellin_eq_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    allPlaceOrbitMellinFunctional
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial) =
      quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation)
        (selectedSourceModifiedUnitQuarterTest observation nontrivial) := by
  change quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation)
      (selectedAllPlacePoleOrbitJointValue observation nontrivial).1 = _
  rw [selectedAllPlacePoleOrbit_fst,
    selectedModifiedWeakFEPoleTraceTest_functional_one,
    selectedSourceModifiedUnitQuarterTest_functional_one]

private theorem reversalPrimeExponentPole_baseMellin_eq_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    allPlaceOrbitMellinFunctional
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial) =
      quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation)
        (reversalSourceModifiedUnitQuarterTest observation nontrivial) := by
  change quarterMellinL2Functional
      (reversalCoPoissonMuntzParameter observation)
      (reversalAllPlacePoleOrbitJointValue observation nontrivial).1 = _
  rw [reversalAllPlacePoleOrbit_fst,
    reversalModifiedWeakFEPoleTraceTest_functional_one,
    reversalSourceModifiedUnitQuarterTest_functional_one]

/-- Exact selected factor map split into root-owned horizontal and vertical
coordinates. -/
theorem selectedPrimeExponentPoleMellin_verticalSplit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleMellinMap observation nontrivial =
      selectedPrimeExponentPoleRieszEnergyPair observation nontrivial +
        selectedPrimeExponentPoleVerticalScalarTrace
          observation nontrivial := by
  apply LinearMap.ext
  intro event
  let z := selectedCoPoissonMuntzParameter observation
  let pole := selectedAllPlacePoleOrbitJointValue observation nontrivial
  let seed := selectedSourceModifiedUnitQuarterTest observation nontrivial
  let test := primeExponentPoleQuarterTestMap z seed event
  have energyPoint := LinearMap.congr_fun
    (primeExponentPolePositiveEnergy_quarterTest_square z
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      pole seed
      (selectedAllPlacePole_positiveEnergy_readback observation nontrivial))
    event
  have mellinPoint := LinearMap.congr_fun
    (primeExponentPoleMellin_quarterTest_square z pole seed
      (selectedPrimeExponentPole_baseMellin_eq_source
        observation nontrivial)) event
  change selectedPrimeExponentPolePositiveEnergyMap
      observation nontrivial event = quarterMellinL2Feature z test
    at energyPoint
  change selectedPrimeExponentPoleMellinMap observation nontrivial event =
    quarterMellinL2Functional z test at mellinPoint
  change selectedPrimeExponentPoleMellinMap observation nontrivial event =
    inner ℂ (selectedPrimeExponentPoleRootSpectralState
        observation nontrivial).fst
        (selectedPrimeExponentPolePositiveEnergyMap
          observation nontrivial event) +
      inner ℂ (selectedPrimeExponentPoleRootSpectralState
        observation nontrivial).snd
        (selectedPrimeExponentPoleMellinMap observation nontrivial event)
  rw [energyPoint, mellinPoint]
  exact selectedPrimeExponentPoleRootState_quarterTest_verticalSplit
    observation nontrivial test

theorem reversalPrimeExponentPoleMellin_verticalSplit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPoleMellinMap observation nontrivial =
      reversalPrimeExponentPoleRieszEnergyPair observation nontrivial +
        reversalPrimeExponentPoleVerticalScalarTrace
          observation nontrivial := by
  apply LinearMap.ext
  intro event
  let z := reversalCoPoissonMuntzParameter observation
  let pole := reversalAllPlacePoleOrbitJointValue observation nontrivial
  let seed := reversalSourceModifiedUnitQuarterTest observation nontrivial
  let test := primeExponentPoleQuarterTestMap z seed event
  have energyPoint := LinearMap.congr_fun
    (primeExponentPolePositiveEnergy_quarterTest_square z
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
      (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      pole seed
      (reversalAllPlacePole_positiveEnergy_readback observation nontrivial))
    event
  have mellinPoint := LinearMap.congr_fun
    (primeExponentPoleMellin_quarterTest_square z pole seed
      (reversalPrimeExponentPole_baseMellin_eq_source
        observation nontrivial)) event
  change reversalPrimeExponentPolePositiveEnergyMap
      observation nontrivial event = quarterMellinL2Feature z test
    at energyPoint
  change reversalPrimeExponentPoleMellinMap observation nontrivial event =
    quarterMellinL2Functional z test at mellinPoint
  change reversalPrimeExponentPoleMellinMap observation nontrivial event =
    inner ℂ (reversalPrimeExponentPoleRootSpectralState
        observation nontrivial).fst
        (reversalPrimeExponentPolePositiveEnergyMap
          observation nontrivial event) +
      inner ℂ (reversalPrimeExponentPoleRootSpectralState
        observation nontrivial).snd
        (reversalPrimeExponentPoleMellinMap observation nontrivial event)
  rw [energyPoint, mellinPoint]
  exact reversalPrimeExponentPoleRootState_quarterTest_verticalSplit
    observation nontrivial test

/-- Canonical selected factor base reads one after the horizontal/vertical
split. -/
theorem selectedPrimeExponentPoleCanonicalBase_verticalSplit_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedPrimeExponentPoleRieszEnergyPair observation nontrivial
          (AddMonoidAlgebra.single 0 1) +
        selectedPrimeExponentPoleVerticalScalarTrace observation nontrivial
          (AddMonoidAlgebra.single 0 1) = 1 := by
  have split := LinearMap.congr_fun
    (selectedPrimeExponentPoleMellin_verticalSplit observation nontrivial)
    (AddMonoidAlgebra.single 0 1)
  change selectedPrimeExponentPoleMellinMap observation nontrivial
      (AddMonoidAlgebra.single 0 1) =
    selectedPrimeExponentPoleRieszEnergyPair observation nontrivial
        (AddMonoidAlgebra.single 0 1) +
      selectedPrimeExponentPoleVerticalScalarTrace observation nontrivial
        (AddMonoidAlgebra.single 0 1) at split
  rw [← split]
  change primeExponentPoleMellinMap
      (selectedCoPoissonMuntzParameter observation)
      (selectedAllPlacePoleOrbitJointValue observation nontrivial)
      (AddMonoidAlgebra.single 0 1) = 1
  rw [selectedPrimeExponentPoleMellinMap_single]
  simp [quarterDilationCharacter, scaleSquare, scaleValue]

theorem reversalPrimeExponentPoleCanonicalBase_verticalSplit_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalPrimeExponentPoleRieszEnergyPair observation nontrivial
          (AddMonoidAlgebra.single 0 1) +
        reversalPrimeExponentPoleVerticalScalarTrace observation nontrivial
          (AddMonoidAlgebra.single 0 1) = 1 := by
  have split := LinearMap.congr_fun
    (reversalPrimeExponentPoleMellin_verticalSplit observation nontrivial)
    (AddMonoidAlgebra.single 0 1)
  change reversalPrimeExponentPoleMellinMap observation nontrivial
      (AddMonoidAlgebra.single 0 1) =
    reversalPrimeExponentPoleRieszEnergyPair observation nontrivial
        (AddMonoidAlgebra.single 0 1) +
      reversalPrimeExponentPoleVerticalScalarTrace observation nontrivial
        (AddMonoidAlgebra.single 0 1) at split
  rw [← split]
  change primeExponentPoleMellinMap
      (reversalCoPoissonMuntzParameter observation)
      (reversalAllPlacePoleOrbitJointValue observation nontrivial)
      (AddMonoidAlgebra.single 0 1) = 1
  rw [reversalPrimeExponentPoleMellinMap_single]
  simp [quarterDilationCharacter, scaleSquare, scaleValue]

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
