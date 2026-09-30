import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.Measurement.LivingLawCanonicalRiemannRuntimeMuntzConductorSeedTermMeasurement

/-!
# Prime-power retained conductor pair readback

At the receipt-selected physical index, the primitive Euler conductor term
acts on both character siblings of one normalized retained pair.  Its affine
image keeps the quarter-density inverse explicit and does not identify the
owner whole coefficient with the retained Euler coefficient.
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
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace History

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.MuntzConductor.GraphLogPositionCone
open ClozelGeneralizedDual.MuntzConductor.HalfPositionSource
open ClozelGeneralizedDual.MuntzConductor.HalfPositionSource.GraphAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimePower.Runtime
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Consumer
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.Consumer

noncomputable section

theorem normalizedRetainedPair_fst_eq_complexPower
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (normalizedRetainedPair observation nontrivial scale).1 =
      complexPowerCharacter observation.coordinate scale := by
  rw [normalizedRetainedPair_eq_jointStateModulePairEvaluation]
  change jointStateModuleSelectedEvaluation observation nontrivial
      (delta scale) = _
  rw [jointStateModuleSelectedEvaluation_delta,
    jointStateModuleSelectedBasisReadback_eq_graph,
    selectedGraphCharacterBasisReadback_eq_complexPower]

theorem normalizedRetainedPair_snd_eq_complexPower
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (normalizedRetainedPair observation nontrivial scale).2 =
      complexPowerCharacter (coordinateReversal observation.coordinate)
        scale := by
  rw [normalizedRetainedPair_eq_jointStateModulePairEvaluation]
  change jointStateModuleReversalEvaluation observation nontrivial
      (delta scale) = _
  rw [jointStateModuleReversalEvaluation_delta,
    jointStateModuleReversalBasisReadback_eq_graph,
    reversalGraphCharacterBasisReadback_eq_complexPower]

/-- Selected scalar sibling of the primitive Euler conductor term. -/
def selectedPrimePowerRetainedConductorMeasurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) : ℂ :=
  let face := primePowerRuntimeFace observation nontrivial prime exponent
  let index := primePowerConductorObservationIndex prime exponent
  (graphNormalizedHalfPositionJointActionTerm
    (selectedCoPoissonMuntzParameter observation)
    face.eulerConductorCurrent index
    (graphFeature
      (halfPositionGraphFeature
        (selectedCoPoissonMuntzParameter observation))
      (halfPositionGraphFunctional
        (selectedCoPoissonMuntzParameter observation))
      (selectedPrimePowerConductorSeed observation nontrivial))).snd

/-- Reversal scalar sibling of the same retained Euler term. -/
def reversalPrimePowerRetainedConductorMeasurement
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) : ℂ :=
  let face := primePowerRuntimeFace observation nontrivial prime exponent
  let index := primePowerConductorObservationIndex prime exponent
  (graphNormalizedHalfPositionJointActionTerm
    (reversalCoPoissonMuntzParameter observation)
    face.eulerConductorCurrent index
    (graphFeature
      (halfPositionGraphFeature
        (reversalCoPoissonMuntzParameter observation))
      (halfPositionGraphFunctional
        (reversalCoPoissonMuntzParameter observation))
      (reversalPrimePowerConductorSeed observation nontrivial))).snd

theorem selectedPrimePowerRetainedConductorMeasurement_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    selectedPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        complexPowerCharacter observation.coordinate
          (primePowerUnit prime exponent) := by
  unfold selectedPrimePowerRetainedConductorMeasurement
  rw [selectedJointConductorTerm_measurement]
  rw [primePowerConductorObservationIndex_succ prime exponent positive]
  change ((primePowerRuntimeFace observation nontrivial prime exponent
        ).eulerConductorCurrent
          (thetaDistributionPrimePower prime exponent) : ℂ) *
      selectedGraphCharacterBasisReadback observation nontrivial
        (graphIntegerScaleUnit
          (primePowerConductorObservationIndex prime exponent)) = _
  rw [primePowerRuntimeFace_conductorRead
    observation nontrivial prime exponent positive]
  rw [selectedGraphCharacterBasisReadback_eq_complexPower,
    graphIntegerScaleUnit_primePower prime exponent positive]

theorem reversalPrimePowerRetainedConductorMeasurement_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    reversalPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        complexPowerCharacter (coordinateReversal observation.coordinate)
          (primePowerUnit prime exponent) := by
  unfold reversalPrimePowerRetainedConductorMeasurement
  rw [reversalJointConductorTerm_measurement]
  rw [primePowerConductorObservationIndex_succ prime exponent positive]
  change ((primePowerRuntimeFace observation nontrivial prime exponent
        ).eulerConductorCurrent
          (thetaDistributionPrimePower prime exponent) : ℂ) *
      reversalGraphCharacterBasisReadback observation nontrivial
        (graphIntegerScaleUnit
          (primePowerConductorObservationIndex prime exponent)) = _
  rw [primePowerRuntimeFace_conductorRead
    observation nontrivial prime exponent positive]
  rw [reversalGraphCharacterBasisReadback_eq_complexPower,
    graphIntegerScaleUnit_primePower prime exponent positive]

/-- Both scalar siblings are one retained pair scaled by the primitive
Euler conductor coefficient from the same receipt. -/
theorem primePowerRetainedConductorMeasurement_pair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (selectedPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent,
      reversalPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent) =
      (Real.log ((prime : Nat) : ℝ) : ℂ) •
        normalizedRetainedPair observation nontrivial
          (primePowerUnit prime exponent) := by
  apply Prod.ext
  · change selectedPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        (normalizedRetainedPair observation nontrivial
          (primePowerUnit prime exponent)).1
    rw [selectedPrimePowerRetainedConductorMeasurement_eq
        observation nontrivial prime exponent positive,
      normalizedRetainedPair_fst_eq_complexPower]
  · change reversalPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        (normalizedRetainedPair observation nontrivial
          (primePowerUnit prime exponent)).2
    rw [reversalPrimePowerRetainedConductorMeasurement_eq
        observation nontrivial prime exponent positive,
      normalizedRetainedPair_snd_eq_complexPower]

/-- Exact affine image of the paired quarter-incidence measurement, with
the source-generated inverse quarter-density retained. -/
theorem primePowerRetainedConductorMeasurement_pair_affineIncidence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (selectedPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent,
      reversalPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent) =
      (Real.log ((prime : Nat) : ℝ) : ℂ) •
        ((positiveMellinQuarterDilationWeight
          (scaleSquare (primePowerUnit prime exponent)))⁻¹ •
            (pairedOne -
              pairedOmegaMeasurementResidual observation nontrivial
                (primePowerUnit prime exponent))) := by
  rw [primePowerRetainedConductorMeasurement_pair
    observation nontrivial prime exponent positive]
  rfl

/-- The affine complement is the installed raw action target; its
normalization is not cancelled. -/
theorem primePowerRetainedConductorMeasurement_pair_eq_rawTarget
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (selectedPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent,
      reversalPrimePowerRetainedConductorMeasurement
        observation nontrivial prime exponent) =
      (Real.log ((prime : Nat) : ℝ) : ℂ) •
        ((positiveMellinQuarterDilationWeight
          (scaleSquare (primePowerUnit prime exponent)))⁻¹ •
            pairedRawActionTarget observation nontrivial
              (primePowerUnit prime exponent)) := by
  rw [primePowerRetainedConductorMeasurement_pair_affineIncidence
      observation nontrivial prime exponent positive,
    pairedOmegaMeasurementResidual_eq_one_sub_target]
  apply congrArg
  apply congrArg
  ext <;> simp [pairedOne]

/-- Selected minus reversal matches the installed runtime leakage. -/
theorem primePowerRetainedConductorMeasurement_difference
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    selectedPrimePowerRetainedConductorMeasurement
          observation nontrivial prime exponent -
        reversalPrimePowerRetainedConductorMeasurement
          observation nontrivial prime exponent =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        runtimeFaceMuntzCharacterLeakage
          (primePowerRuntimeFace observation nontrivial prime exponent) := by
  rw [selectedPrimePowerRetainedConductorMeasurement_eq
      observation nontrivial prime exponent positive,
    reversalPrimePowerRetainedConductorMeasurement_eq
      observation nontrivial prime exponent positive,
    primePowerRuntimeFace_muntzLeakage_eq_source]
  unfold PrimePower.Quadratic.primePowerCharacterLeakageReadFromSource
  rw [PrimePower.Source.primePowerReversalCharacterReadFromSource_root_eq
      observation nontrivial prime exponent positive,
    PrimePower.Source.primePowerSelectedCharacterReadFromSource_root_eq
      observation nontrivial prime exponent positive]
  ring

end
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
