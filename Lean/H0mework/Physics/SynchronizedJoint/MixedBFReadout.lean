import H0mework.Physics.SynchronizedJoint.Response
import H0mework.Physics.Lorentz.LorentzTemporalGaussFirstVariation

/-!
# Stage-9 full-synchronized Lorentz mixed-BF readout

The C3h203 contact-local actual installs its action-generated Lorentz
auxiliary velocity along the canonical time coordinate only.  This module
computes the resulting BF momentum on the whole local chart:

```text
constant action-generated pairing
+ time-coordinate * generated velocity pairing.
```

Consequently every spatial BF-momentum derivative, the spatial divergence,
and the mixed-BF sector of the temporal-Gauss first variation vanish.  This
is a direct readout of the already generated actual; no residual, zero
certificate, repair coefficient, or branch enters the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentFullSynchronizedLorentzMixedBFReadout

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineLorentzTemporalGaussFirstVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-- Whole-chart normal form of the installed auxiliary field. -/
theorem currentFullSynchronizedLorentzActualFirstJetLift_gravityAuxiliary_point
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (currentFullSynchronizedLorentzActualFirstJetLift source current
        space).gravityAuxiliary point =
      actionGeneratedGravityAuxiliary current space +
        localBaseCoordinate canonicalLorentzianTimeDirection point •
          currentFullSynchronizedLorentzAuxiliaryVelocity source current
            space := by
  change
    (currentCanonicalFullActionActual source current
        space).gravityAuxiliary point +
      localBaseCoordinate canonicalLorentzianTimeDirection point •
        currentFullSynchronizedLorentzAuxiliaryVelocity source current
          space =
      _
  rw [show
    (currentCanonicalFullActionActual source current
        space).gravityAuxiliary point =
      actionGeneratedGravityAuxiliary current space by
    change
      (currentFullSynchronizedCompleteP286BaseActual source current
        space).gravityAuxiliary point =
        actionGeneratedGravityAuxiliary current space
    exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_auxiliary
      source current space point]

/-- The full-synchronized BF momentum depends on the chart only through the
canonical time coordinate. -/
theorem currentFullSynchronizedLorentzActualFirstJetLift_BFMomentum_affineTime
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (derivativeDirection : LorentzianIndex)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentum
        (currentFullSynchronizedLorentzActualFirstJetLift source current
          space)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          direction)
        point =
      gravityAuxiliaryHodgePairingPolynomial 1
          (actionGeneratedGravityAuxiliary current space)
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction) +
        localBaseCoordinate canonicalLorentzianTimeDirection point *
          gravityAuxiliaryHodgePairingPolynomial 1
            (currentFullSynchronizedLorentzAuxiliaryVelocity source current
              space)
            (lorentzConnectionExteriorDerivativeDirection derivativeDirection
              direction) := by
  unfold lorentzConnectionBFDifferentialMomentum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    currentFullSynchronizedLorentzActualFirstJetLift_coframe_one
      source current space identityCoframe point,
    currentFullSynchronizedLorentzActualFirstJetLift_gravityAuxiliary_point]
  simp only [Matrix.det_one, abs_one, one_mul]
  exact gravityAuxiliaryHodgePairingPolynomial_add_smul_left
    1 (by simp)
    (actionGeneratedGravityAuxiliary current space)
    (currentFullSynchronizedLorentzAuxiliaryVelocity source current space)
    (lorentzConnectionExteriorDerivativeDirection derivativeDirection
      direction)
    (localBaseCoordinate canonicalLorentzianTimeDirection point)

/-- Directional derivative of a real affine function in the canonical time
coordinate. -/
theorem fieldDirectionalDerivative_const_add_timeCoordinate_mul
    (constant slope : ℝ)
    (point : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate : BasePoint =>
          constant +
            localBaseCoordinate canonicalLorentzianTimeDirection candidate *
              slope)
        point derivativeDirection =
      if derivativeDirection = canonicalLorentzianTimeDirection then
        slope
      else
        0 := by
  unfold fieldDirectionalDerivative
  have coordinateDerivative :
      HasFDerivAt
          (fun candidate : BasePoint =>
            localBaseCoordinate canonicalLorentzianTimeDirection candidate)
          (localBaseCoordinate canonicalLorentzianTimeDirection)
          point :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
  have affineDerivative :=
    (coordinateDerivative.mul_const' slope).const_add constant
  rw [affineDerivative.fderiv]
  fin_cases derivativeDirection <;>
    simp [canonicalLorentzianTimeDirection, localBaseCoordinate_apply,
      coordinateDirection]

/-- Every spatial BF-momentum derivative of the contact-local actual is zero.
The temporal slope may be nonzero; no response is discarded. -/
theorem
    currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDerivative_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (derivativeDirection : LorentzianIndex)
    (spatial : derivativeDirection ≠ canonicalLorentzianTimeDirection)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (lorentzConnectionBFDifferentialMomentum
          (currentFullSynchronizedLorentzActualFirstJetLift source current
            space)
          (lorentzConnectionExteriorDerivativeDirection derivativeDirection
            direction))
        point derivativeDirection =
      0 := by
  rw [show
    lorentzConnectionBFDifferentialMomentum
        (currentFullSynchronizedLorentzActualFirstJetLift source current
          space)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          direction) =
      fun candidate : BasePoint =>
        gravityAuxiliaryHodgePairingPolynomial 1
            (actionGeneratedGravityAuxiliary current space)
            (lorentzConnectionExteriorDerivativeDirection derivativeDirection
              direction) +
          localBaseCoordinate canonicalLorentzianTimeDirection candidate *
            gravityAuxiliaryHodgePairingPolynomial 1
              (currentFullSynchronizedLorentzAuxiliaryVelocity source current
                space)
              (lorentzConnectionExteriorDerivativeDirection
                derivativeDirection direction) by
    funext candidate
    exact
      currentFullSynchronizedLorentzActualFirstJetLift_BFMomentum_affineTime
        source current space identityCoframe derivativeDirection direction
        candidate]
  rw [fieldDirectionalDerivative_const_add_timeCoordinate_mul]
  simp [spatial]

/-- The complete three-term spatial BF divergence vanishes on the generated
contact-local actual. -/
theorem
    currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDivergence_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionSpatialBFMomentumDivergence
        (currentFullSynchronizedLorentzActualFirstJetLift source current
          space)
        direction point =
      0 := by
  unfold lorentzConnectionSpatialBFMomentumDivergence
  rw [
    currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDerivative_zero
      source current space identityCoframe 1 (by decide) direction point,
    currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDerivative_zero
      source current space identityCoframe 2 (by decide) direction point,
    currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDerivative_zero
      source current space identityCoframe 3 (by decide) direction point]
  ring

/-- The mixed-BF sector of the temporal-Gauss first variation is therefore
zero on this actual family. -/
theorem
    currentFullSynchronizedLorentzActualFirstJetLift_mixedBFTangencyTerm_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : current.coframe space = 1)
    (component : LorentzTemporalBivectorDirection) :
    lorentzTemporalGaussMixedBFTangencyTerm
        (currentFullSynchronizedLorentzActualFirstJetLift source current
          space)
        component =
      0 := by
  unfold lorentzTemporalGaussMixedBFTangencyTerm
  rw [show
    lorentzConnectionSpatialBFMomentumDivergence
        (currentFullSynchronizedLorentzActualFirstJetLift source current
          space)
        (canonicalLorentzTemporalBivectorOneForm component) =
      fun _ => 0 by
    funext point
    exact
      currentFullSynchronizedLorentzActualFirstJetLift_spatialBFMomentumDivergence_zero
        source current space identityCoframe
        (canonicalLorentzTemporalBivectorOneForm component) point]
  simp [fieldDirectionalDerivative]

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentFullSynchronizedLorentzMixedBFReadout
