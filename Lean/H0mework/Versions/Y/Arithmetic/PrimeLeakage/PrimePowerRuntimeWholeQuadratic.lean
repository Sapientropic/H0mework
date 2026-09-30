import H0mework.Versions.Y.Arithmetic.PrimeLeakage.RuntimePhaseQuadratic

/-!
# Prime-power restriction of the installed phase whole

The existing runtime `phase` is quadraticized before any local split.  Its
linear conservation then yields the prime-power retained quadratic plus a
forward polarization residual generated from the centered trace.  The
residual is not defined by subtracting the desired finite term.
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
namespace Consumer

open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open Complex
open Material
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open Quadratic
open Root
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Quadratic
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Source
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Source
open scoped InnerProductSpace

noncomputable section

def primePowerRuntimeOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    JointRuntimeOccurrenceAt observation nontrivial
      (CanonicalUnitArithmeticRoot.finiteVisit
        (primePowerRuntimeStage prime exponent)).current :=
  (runtimeAllPlaceWeilRoot observation nontrivial).emitted _

def primePowerRuntimeFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    GeneratedRuntimeAllPlaceWeilFaceAt observation nontrivial
      (primePowerRuntimeOccurrence
        observation nontrivial prime exponent) :=
  generateRuntimeAllPlaceWeilFace observation nontrivial
    (primePowerRuntimeOccurrence observation nontrivial prime exponent)

theorem primePowerRuntimeFace_stage
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    (primePowerRuntimeFace observation nontrivial prime exponent).stage =
      primePowerRuntimeStage prime exponent := by
  exact currentEffectStage_finiteVisit _

theorem primePowerRuntimeRetainedAmplitude_eq_characterLeakage
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    runtimeFaceRetainedAmplitude
        (primePowerRuntimeFace observation nontrivial prime exponent) =
      primePowerCharacterLeakageReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent := by
  unfold runtimeFaceRetainedAmplitude
  rw [(primePowerRuntimeFace observation nontrivial prime exponent).retained_eq]
  change normalizedPairSkew
      (stageSqrtScaleUnit
        (primePowerRuntimeFace observation nontrivial prime exponent).stage)
      (installedRuntimeEffectValueAt observation nontrivial
        (primePowerRuntimeFace observation nontrivial prime exponent).stage
        ).retained = _
  rw [primePowerRuntimeFace_stage,
    installedRuntimeEffectValueAt_retained_eq_jointIncidence,
    primePowerRuntimeStage_scaleUnit prime exponent positive]
  let scale := primePowerUnit prime exponent
  calc
    normalizedPairSkew scale
        (pairedOmegaMeasurementResidual observation nontrivial scale) =
      (normalizedRetainedPair observation nontrivial scale).1 -
        (normalizedRetainedPair observation nontrivial scale).2 := by
          simp [normalizedPairSkew, pairSkew, normalizedRetainedPair,
            pairedOne]
          ring
    _ = (jointStateModulePairEvaluation observation nontrivial
          (delta scale)).1 -
        (jointStateModulePairEvaluation observation nontrivial
          (delta scale)).2 := by
      rw [normalizedRetainedPair_eq_jointStateModulePairEvaluation]
    _ = selectedGraphCharacterEvaluation observation nontrivial
          (delta scale) -
        reversalGraphCharacterEvaluation observation nontrivial
          (delta scale) := by
      change jointStateModuleSelectedEvaluation observation nontrivial
          (delta scale) -
        jointStateModuleReversalEvaluation observation nontrivial
          (delta scale) = _
      rw [jointStateModuleSelectedEvaluation_eq_graph,
        jointStateModuleReversalEvaluation_eq_graph]
    _ = complexPowerCharacter observation.coordinate scale -
        complexPowerCharacter
          (coordinateReversal observation.coordinate) scale := by
      rw [selectedGraphCharacterEvaluation_eq_integralOccurrence,
        reversalGraphCharacterEvaluation_eq_integralOccurrence,
        zeroOwnedIntegralCharacterOccurrence_root_selected,
        zeroOwnedIntegralCharacterOccurrence_root_reversal,
        characterEvaluation_delta, characterEvaluation_delta,
        zeroOwnedMultiplicativeCharacterOccurrence_root_selected,
        zeroOwnedMultiplicativeCharacterOccurrence_root_reversal]
    _ = _ := by
      unfold primePowerCharacterLeakageReadFromSource
      rw [primePowerReversalCharacterReadFromSource_root_eq
          observation nontrivial prime exponent positive,
        primePowerSelectedCharacterReadFromSource_root_eq
          observation nontrivial prime exponent positive]
      ring

theorem primePowerRuntimeFace_eulerWeight
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    runtimeFaceEulerWeight
        (primePowerRuntimeFace observation nontrivial prime exponent)
        prime exponent = Real.log ((prime : Nat) : ℝ) := by
  unfold runtimeFaceEulerWeight primePowerRuntimeFace
    generateRuntimeAllPlaceWeilFace
  exact primePowerEulerWeightFromSource_root_eq
    observation nontrivial prime exponent positive

theorem primePowerRuntimeFace_conductor_eq_eulerWeight
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    (primePowerRuntimeFace observation nontrivial prime exponent
      ).eulerConductorCurrent
        (thetaDistributionPrimePower prime exponent) =
      runtimeFaceEulerWeight
        (primePowerRuntimeFace observation nontrivial prime exponent)
        prime exponent := by
  change generatedEulerConductorCurrent
        (jointStateAnalyticOwner
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root.1)
        (thetaDistributionPrimePower prime exponent) =
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root.2.eulerFace.coefficients
        (thetaDistributionPrimePower prime exponent)
  rw [generatedEulerConductorCurrent_eq_eulerFace,
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.eulerFace_eq]

theorem primePowerRuntimeFace_conductorRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    (primePowerRuntimeFace observation nontrivial prime exponent
      ).eulerConductorCurrent
        (thetaDistributionPrimePower prime exponent) =
      Real.log ((prime : Nat) : ℝ) := by
  rw [primePowerRuntimeFace_conductor_eq_eulerWeight]
  exact primePowerRuntimeFace_eulerWeight
    observation nontrivial prime exponent positive

theorem primePowerRuntimeRetainedQuadratic_eq_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerRuntimeRetainedQuadratic
        (primePowerRuntimeFace observation nontrivial prime exponent)
        prime exponent =
      primePowerEulerWeightedQuadraticFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent := by
  unfold primePowerRuntimeRetainedQuadratic
    primePowerEulerWeightedQuadraticFromSource
  rw [primePowerRuntimeFace_eulerWeight
      observation nontrivial prime exponent positive,
    primePowerRuntimeRetainedAmplitude_eq_characterLeakage
      observation nontrivial prime exponent positive,
    primePowerEulerWeightFromSource_root_eq
      observation nontrivial prime exponent positive]

theorem primePowerRuntimeWholeQuadratic_source_decomposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    primePowerRuntimeWholeQuadratic
        (primePowerRuntimeFace observation nontrivial prime exponent)
        prime exponent =
      primePowerEulerWeightedQuadraticFromSource
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root prime exponent +
        centeredRuntimeQuadraticResidual
          (primePowerRuntimeFace observation nontrivial prime exponent)
          prime exponent := by
  calc
    primePowerRuntimeWholeQuadratic
        (primePowerRuntimeFace observation nontrivial prime exponent)
        prime exponent =
      primePowerRuntimeRetainedQuadratic
          (primePowerRuntimeFace observation nontrivial prime exponent)
          prime exponent +
        centeredRuntimeQuadraticResidual
          (primePowerRuntimeFace observation nontrivial prime exponent)
          prime exponent :=
      primePowerRuntimeWholeQuadratic_decomposition
        (primePowerRuntimeFace observation nontrivial prime exponent)
        prime exponent
    _ = _ := by
      rw [primePowerRuntimeRetainedQuadratic_eq_source
        observation nontrivial prime exponent positive]

/-- The first prime-power restriction is the previously installed Euler
prime diagonal, now as the retained face of the runtime whole. -/
theorem primePowerRuntimeWholeQuadratic_one_decomposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    primePowerRuntimeWholeQuadratic
        (primePowerRuntimeFace observation nontrivial prime 1)
        prime 1 =
      EulerDiagonal.eulerWeightedPrimeLeakage observation prime +
        centeredRuntimeQuadraticResidual
          (primePowerRuntimeFace observation nontrivial prime 1)
          prime 1 := by
  rw [primePowerRuntimeWholeQuadratic_source_decomposition
      observation nontrivial prime 1 Nat.zero_lt_one,
    primePowerEulerWeightedQuadraticFromSource_root_one]

end
end Consumer
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
