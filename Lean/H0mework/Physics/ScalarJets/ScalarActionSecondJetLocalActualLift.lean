import H0mework.Physics.Exterior.JointActionLocalActualLift

/-!
# S9-C3h102: action-generated scalar second-jet local actual lift

This checkpoint continues the path-first/action-first construction.  The
positive proof-free source and the actual scalar action first generate the
temporal canonical-momentum force.  The fixed finite real coordinate basis of
the existing complex scalar representation then reconstructs its unique real
dual coordinate; no residual, target endpoint, inverse Hessian, preimage,
branch receipt, or supplied acceleration is consumed.

The canonical Taylor coefficient `1 / 2` installs that generated acceleration
as a quadratic physical-time correction of the C3h101 local actual field:

```text
source + actual scalar action
→ temporal momentum force
→ explicit real-dual scalar coordinate
→ quadratic local actual field U
→ initial / first-jet / second-time-jet acceptance.
```

For the current positive source the action itself computes the force to be
zero, so the generated second jet is stationary and the corrected whole
configuration is extensionally C3h101.  The second-derivative theorem is
nevertheless proved from the forward quadratic construction, while the
faithfulness theorem records that a future nonzero action force cannot be
silently lost by this dual lift.

This is not yet a nonzero scalar acceleration example, a closed vector field
on the whole primitive Cauchy carrier, or a full interacting local
development.  Residual laws remain downstream acceptance only.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineScalarActionSecondJetLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineJointActionLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

def scalarRealBasis
    (index : ScalarBasisIndex) : ScalarCoordinateCarrier :=
  EuclideanSpace.single index 1

def scalarImaginaryBasis
    (index : ScalarBasisIndex) : ScalarCoordinateCarrier :=
  EuclideanSpace.single index Complex.I

def scalarActionRealDual
    (force : Module.Dual ℝ ScalarCoordinateCarrier) :
    ScalarCoordinateCarrier :=
  WithLp.toLp 2 fun index =>
    (force (scalarRealBasis index) : ℂ) +
      (force (scalarImaginaryBasis index) : ℂ) * Complex.I

theorem scalarCoordinate_decomposition
    (coordinates : ScalarCoordinateCarrier) :
    coordinates =
      ∑ index : ScalarBasisIndex,
        ((coordinates index).re • scalarRealBasis index +
          (coordinates index).im • scalarImaginaryBasis index) := by
  classical
  apply PiLp.ext
  intro coordinate
  change coordinates coordinate =
    (PiLp.projₗ (p := 2) (𝕜 := ℝ)
      (fun _ : ScalarBasisIndex => ℂ) coordinate)
      (∑ index : ScalarBasisIndex,
        ((coordinates index).re • scalarRealBasis index +
          (coordinates index).im • scalarImaginaryBasis index))
  rw [map_sum]
  simp [scalarRealBasis, scalarImaginaryBasis, Finset.sum_add_distrib]

theorem scalarCoordinatePairingRe_actionRealDual
    (force : Module.Dual ℝ ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe direction (scalarActionRealDual force) =
      force direction := by
  classical
  conv_rhs => rw [scalarCoordinate_decomposition direction]
  rw [map_sum]
  simp only [map_add, map_smul, smul_eq_mul]
  unfold scalarCoordinatePairingRe scalarActionRealDual
  apply Finset.sum_congr rfl
  intro index _indexMem
  simp [scalarRealBasis, scalarImaginaryBasis, Complex.mul_re,
    Complex.mul_im]

theorem scalarActionRealDual_ne_zero_of_apply_ne_zero
    (force : Module.Dual ℝ ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier)
    (forceNonzero : force direction ≠ 0) :
    scalarActionRealDual force ≠ 0 := by
  intro dualZero
  have reconstruction :=
    scalarCoordinatePairingRe_actionRealDual force direction
  rw [dualZero] at reconstruction
  have pairingZero :
      scalarCoordinatePairingRe direction
          (0 : ScalarCoordinateCarrier) = 0 := by
    change scalarCoordinatePairingReBilinear direction 0 = 0
    exact map_zero (scalarCoordinatePairingReBilinear direction)
  rw [pairingZero] at reconstruction
  exact forceNonzero reconstruction.symm

def positiveScalarTemporalMomentumVelocityDual :
    Module.Dual ℝ ScalarCoordinateCarrier where
  toFun :=
    sourceActionGeneratedScalarTemporalMomentumVelocity
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
  map_add' := by
    intro first second
    rw [congrFun positiveScalarTemporalMomentumVelocity_zero first]
    rw [congrFun positiveScalarTemporalMomentumVelocity_zero second]
    rw [congrFun positiveScalarTemporalMomentumVelocity_zero (first + second)]
    simp
  map_smul' := by
    intro parameter direction
    rw [congrFun positiveScalarTemporalMomentumVelocity_zero
      (parameter • direction)]
    rw [congrFun positiveScalarTemporalMomentumVelocity_zero direction]
    simp

def positiveActionGeneratedScalarCovariantAcceleration :
    ScalarCoordinateCarrier :=
  -scalarActionRealDual positiveScalarTemporalMomentumVelocityDual

theorem positiveActionGeneratedScalarCovariantAcceleration_eq_zero :
    positiveActionGeneratedScalarCovariantAcceleration = 0 := by
  apply PiLp.ext
  intro index
  simp [positiveActionGeneratedScalarCovariantAcceleration,
    scalarActionRealDual, positiveScalarTemporalMomentumVelocityDual,
    scalarRealBasis, scalarImaginaryBasis,
    positiveScalarTemporalMomentumVelocity_zero]

def scalarQuadraticTimeCoefficient (point : BasePoint) : ℝ :=
  (1 / 2 : ℝ) *
    (localBaseCoordinate canonicalLorentzianTimeDirection point *
      localBaseCoordinate canonicalLorentzianTimeDirection point)

@[simp] theorem scalarQuadraticTimeCoefficient_origin :
    scalarQuadraticTimeCoefficient (0 : BasePoint) = 0 := by
  simp [scalarQuadraticTimeCoefficient]

theorem scalarQuadraticTimeCoefficient_hasFDerivAt
    (point : BasePoint) :
    HasFDerivAt scalarQuadraticTimeCoefficient
      ((1 / 2 : ℝ) •
        ((localBaseCoordinate canonicalLorentzianTimeDirection point) •
            localBaseCoordinate canonicalLorentzianTimeDirection +
          (localBaseCoordinate canonicalLorentzianTimeDirection point) •
            localBaseCoordinate canonicalLorentzianTimeDirection))
      point := by
  have squareDerivative :=
    ((localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := point)).mul
      ((localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
        (x := point))
  have scaledDerivative :=
    squareDerivative.const_mul (1 / 2 : ℝ)
  exact scaledDerivative

theorem scalarQuadraticTimeCoefficient_timeDerivative
    (point : BasePoint) :
    fieldDirectionalDerivative scalarQuadraticTimeCoefficient point
        canonicalLorentzianTimeDirection =
      point canonicalLorentzianTimeDirection := by
  unfold fieldDirectionalDerivative
  rw [(scalarQuadraticTimeCoefficient_hasFDerivAt point).fderiv]
  simp [coordinateDirection]
  ring

def scalarQuadraticTimeCorrection
    (acceleration : ScalarCoordinateCarrier)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  scalarQuadraticTimeCoefficient point • acceleration

theorem scalarQuadraticTimeCorrection_timeDerivative
    (acceleration : ScalarCoordinateCarrier)
    (point : BasePoint) :
    fieldDirectionalDerivative
        (scalarQuadraticTimeCorrection acceleration) point
        canonicalLorentzianTimeDirection =
      point canonicalLorentzianTimeDirection • acceleration := by
  have derivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt point).smul_const acceleration
  unfold fieldDirectionalDerivative scalarQuadraticTimeCorrection
  rw [derivative.fderiv]
  simp [coordinateDirection]
  ring_nf

@[simp] theorem scalarQuadraticTimeCorrection_origin
    (acceleration : ScalarCoordinateCarrier) :
    scalarQuadraticTimeCorrection acceleration 0 = 0 := by
  simp [scalarQuadraticTimeCorrection]

theorem scalarQuadraticTimeCorrection_firstTimeDerivative_origin
    (acceleration : ScalarCoordinateCarrier) :
    fieldDirectionalDerivative
        (scalarQuadraticTimeCorrection acceleration) 0
        canonicalLorentzianTimeDirection = 0 := by
  rw [scalarQuadraticTimeCorrection_timeDerivative]
  simp

theorem scalarQuadraticTimeCorrection_secondTimeDerivative_origin
    (acceleration : ScalarCoordinateCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (scalarQuadraticTimeCorrection acceleration) point
            canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection =
      acceleration := by
  rw [show
    (fun point =>
      fieldDirectionalDerivative
        (scalarQuadraticTimeCorrection acceleration) point
        canonicalLorentzianTimeDirection) =
      fun point =>
        point canonicalLorentzianTimeDirection • acceleration by
    funext point
    exact scalarQuadraticTimeCorrection_timeDerivative acceleration point]
  unfold fieldDirectionalDerivative
  have derivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := (0 : BasePoint))
      |>.smul_const acceleration
  rw [show
    (fun point : BasePoint =>
      point canonicalLorentzianTimeDirection • acceleration) =
      fun point =>
        localBaseCoordinate canonicalLorentzianTimeDirection point •
          acceleration by
    rfl,
    derivative.fderiv]
  simp [coordinateDirection]

def positiveActionGeneratedScalarSecondJetField
    (point : BasePoint) : ScalarCoordinateCarrier :=
  positivePathFirstJointLocalActualLift.scalar point +
    scalarQuadraticTimeCorrection
      positiveActionGeneratedScalarCovariantAcceleration point

def positiveActionGeneratedScalarSecondJetLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positivePathFirstJointLocalActualLift with
    scalar := positiveActionGeneratedScalarSecondJetField }

theorem
    positiveActionGeneratedScalarSecondJetLocalActualLift_eq_C3h101 :
    positiveActionGeneratedScalarSecondJetLocalActualLift =
      positivePathFirstJointLocalActualLift := by
  unfold positiveActionGeneratedScalarSecondJetLocalActualLift
    positiveActionGeneratedScalarSecondJetField
  rw [positiveActionGeneratedScalarCovariantAcceleration_eq_zero]
  apply StageNineHolonomicConfiguration.ext <;>
    simp [scalarQuadraticTimeCorrection]

theorem positiveActionGeneratedScalarCovariantAcceleration_actionLaw
    (direction : ScalarCoordinateCarrier) :
    sourceActionGeneratedScalarTemporalMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction =
      -scalarCoordinatePairingRe direction
        positiveActionGeneratedScalarCovariantAcceleration := by
  change
    positiveScalarTemporalMomentumVelocityDual direction =
      -scalarCoordinatePairingRe direction
        (-scalarActionRealDual positiveScalarTemporalMomentumVelocityDual)
  rw [show
    scalarCoordinatePairingRe direction
        (-scalarActionRealDual positiveScalarTemporalMomentumVelocityDual) =
      -scalarCoordinatePairingRe direction
        (scalarActionRealDual positiveScalarTemporalMomentumVelocityDual) by
    change
      scalarCoordinatePairingReBilinear direction
          (-scalarActionRealDual positiveScalarTemporalMomentumVelocityDual) =
        -scalarCoordinatePairingReBilinear direction
          (scalarActionRealDual positiveScalarTemporalMomentumVelocityDual)
    exact map_neg
      (scalarCoordinatePairingReBilinear direction)
      (scalarActionRealDual positiveScalarTemporalMomentumVelocityDual)]
  rw [neg_neg, scalarCoordinatePairingRe_actionRealDual]

theorem positiveActionGeneratedScalarSecondJetField_firstTimeDerivative
    (point : BasePoint) :
    fieldDirectionalDerivative
        positiveActionGeneratedScalarSecondJetField point
        canonicalLorentzianTimeDirection =
      point canonicalLorentzianTimeDirection •
        positiveActionGeneratedScalarCovariantAcceleration := by
  have correctionDerivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt point).smul_const
      positiveActionGeneratedScalarCovariantAcceleration
  have derivative :=
    (hasFDerivAt_const (x := point)
      (c := sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).add
      correctionDerivative
  unfold positiveActionGeneratedScalarSecondJetField
    fieldDirectionalDerivative
  rw [positivePathFirstJointLocalActualLift_scalar]
  change
    (fderiv ℝ
      ((fun _ : BasePoint =>
          sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) +
        fun candidate =>
          scalarQuadraticTimeCoefficient candidate •
            positiveActionGeneratedScalarCovariantAcceleration)
      point)
      (coordinateDirection canonicalLorentzianTimeDirection) =
        point canonicalLorentzianTimeDirection •
          positiveActionGeneratedScalarCovariantAcceleration
  rw [derivative.fderiv]
  simp [coordinateDirection]
  ring_nf

theorem
    positiveActionGeneratedScalarSecondJetLocalActualLift_scalarSecondTimeDerivative :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            positiveActionGeneratedScalarSecondJetLocalActualLift.scalar
            point canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection =
      positiveActionGeneratedScalarCovariantAcceleration := by
  rw [show
    (fun point =>
      fieldDirectionalDerivative
        positiveActionGeneratedScalarSecondJetLocalActualLift.scalar point
        canonicalLorentzianTimeDirection) =
      fun point =>
        point canonicalLorentzianTimeDirection •
          positiveActionGeneratedScalarCovariantAcceleration by
    funext point
    exact
      positiveActionGeneratedScalarSecondJetField_firstTimeDerivative point]
  unfold fieldDirectionalDerivative
  have derivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := (0 : BasePoint))
      |>.smul_const positiveActionGeneratedScalarCovariantAcceleration
  rw [show
    (fun point : BasePoint =>
      point canonicalLorentzianTimeDirection •
        positiveActionGeneratedScalarCovariantAcceleration) =
      fun point =>
        localBaseCoordinate canonicalLorentzianTimeDirection point •
          positiveActionGeneratedScalarCovariantAcceleration by
    rfl,
    derivative.fderiv]
  simp [coordinateDirection]

theorem
    positiveActionGeneratedScalarSecondJetLocalActualLift_realizes_C3h102 :
    StageNineJointCanonicalActualInitialLaw positiveSmoothUnifiedSource
          positivePhaseProbeCauchyState 0
            positiveActionGeneratedScalarSecondJetLocalActualLift ∧
      StageNineJointCanonicalActualFirstJetLaw positiveSmoothUnifiedSource
          positivePhaseProbeCauchyState 0
            positiveActionGeneratedScalarSecondJetLocalActualLift ∧
      fieldDirectionalDerivative
          (fun point =>
            fieldDirectionalDerivative
              positiveActionGeneratedScalarSecondJetLocalActualLift.scalar
              point canonicalLorentzianTimeDirection)
          0 canonicalLorentzianTimeDirection =
        positiveActionGeneratedScalarCovariantAcceleration ∧
      ∀ direction,
        sourceActionGeneratedScalarTemporalMomentumVelocity
            positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
            direction =
          -scalarCoordinatePairingRe direction
            positiveActionGeneratedScalarCovariantAcceleration := by
  have initialLaw :
      StageNineJointCanonicalActualInitialLaw positiveSmoothUnifiedSource
        positivePhaseProbeCauchyState 0
          positiveActionGeneratedScalarSecondJetLocalActualLift := by
    rw [positiveActionGeneratedScalarSecondJetLocalActualLift_eq_C3h101]
    exact positivePathFirstJointLocalActualLift_initialLaw
  have firstJetLaw :
      StageNineJointCanonicalActualFirstJetLaw positiveSmoothUnifiedSource
        positivePhaseProbeCauchyState 0
          positiveActionGeneratedScalarSecondJetLocalActualLift := by
    rw [positiveActionGeneratedScalarSecondJetLocalActualLift_eq_C3h101]
    exact positivePathFirstJointLocalActualLift_firstJetLaw
  exact
    ⟨initialLaw,
      firstJetLaw,
      positiveActionGeneratedScalarSecondJetLocalActualLift_scalarSecondTimeDerivative,
      positiveActionGeneratedScalarCovariantAcceleration_actionLaw⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineScalarActionSecondJetLocalActualLift
