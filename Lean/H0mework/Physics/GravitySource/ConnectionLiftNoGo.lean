import H0mework.Physics.GravitySource.TransportCurvature
import H0mework.Physics.Geometry.JointShellZeroFiber
import H0mework.Physics.Lorentz.LorentzConnectionVariation

/-!
# S9-C3g7b: transport is not closure and origin curvature is not a field selector

The framework transport remains entirely upstream of a configuration lift:
forgetting the derived Spin-stable responsibility subtype commutes
definitionally with the same ambient scalar keep.  For the actual positive
mouth the concrete first step is `5/4 ↦ 5/8`; it is nonzero, so a
configuration realizing that one gravity projection is deliberately not yet
in the joint zero fiber.

The Layer-3 obstruction is then stated on an explicit carrier class.  Two
different componentwise smooth, pointwise Lorentz-skew connection fields have
the same origin value and the same genuine `dω + ω∧ω` curvature at the
origin.  The difference is a nonzero quadratic field whose complete first jet
vanishes there.  Hence the curvature obligation from C3g7a cannot select a
global connection field, even after the origin connection value is fixed.

This is a stable typed no-go, not evidence that the gravity shell is empty and
not permission to add a field, coupling, source slot, or realization receipt.
The next producer must first state a normalized local-germ carrier that removes
this kernel without adding an observable branch choice.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthConnectionLiftNoGo

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthObstruction
open StageNinePositiveSourceGravityMouthSpinOrbitCarrier
open StageNinePositiveSourceGravityMouthTransportCurvature
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! ## Layer-0 transport and concrete non-closure regressions -/

/-- Ambient form of the same source-supplied scalar keep. -/
def positiveSourceGravityMouthAmbientKeep :
    PhysicalBivector →ₗ[ℝ] PhysicalBivector :=
  scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma

/-- Layer-0 transport commutes definitionally with forgetting the derived
Spin-stable responsibility subtype.  No configuration is involved. -/
@[simp] theorem positiveSourceGravityMouthSpinOrbitResponsibilityKeep_coe
    (residual : PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) :
    ((positiveSourceGravityMouthSpinOrbitResponsibilityKeep residual :
        PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) :
      PhysicalBivector) =
      positiveSourceGravityMouthAmbientKeep (residual : PhysicalBivector) :=
  rfl

@[simp] theorem transportedPositiveSourceGravityMouthSpinOrbitObstruction_coe :
    (transportedPositiveSourceGravityMouthSpinOrbitObstruction :
        PhysicalBivector) =
      positiveSourceGravityMouthAmbientKeep
        positiveSourceGravityMouthObstruction :=
  rfl

@[simp] theorem positiveSourceGravityMouthConstitutiveCurvature_zero_zero :
    positiveSourceGravityMouthConstitutiveCurvature 0 0 = (-1 : ℝ) := by
  have sourceCurvature :
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 =
        (1 / 4 : ℝ) := by
    change canonicalPhysicalSource.lorentzCurvatureAtOrigin 0 0 =
      (1 / 4 : ℝ)
    simp [Source.lorentzCurvatureAtOrigin, pairFirst, pairSecond,
      minkowskiInternalSign, canonicalPhysicalSource_curvature_component]
  have obstruction := positiveSourceGravityMouthObstruction_zero_zero
  change
    positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 -
        positiveSourceGravityMouthConstitutiveCurvature 0 0 =
      (5 / 4 : ℝ) at obstruction
  linarith

@[simp] theorem positiveSourceGravityMouthTransportedResidual_zero_zero :
    positiveSourceGravityMouthTransportedResidual 0 0 = (5 / 8 : ℝ) := by
  rw [positiveSourceGravityMouthTransportedResidual_eq_scalarKeep]
  change
    (1 - canonicalPhysicalSource.sigma) *
        positiveSourceGravityMouthObstruction 0 0 = (5 / 8 : ℝ)
  rw [positiveSourceGravityMouthObstruction_zero_zero]
  norm_num [canonicalPhysicalSource, canonicalSource,
    StageEightProofFreeSource.Source.toPhysicalSource, Source.sigma]

theorem positiveSourceGravityMouthTransportedResidual_ne_zero :
    positiveSourceGravityMouthTransportedResidual ≠ 0 := by
  intro residualZero
  have componentZero := congrFun (congrFun residualZero 0) 0
  norm_num at componentZero

@[simp] theorem positiveSourceGravityMouthRequiredCurvature_zero_zero :
    positiveSourceGravityMouthRequiredCurvature 0 0 = (-3 / 8 : ℝ) := by
  rw [positiveSourceGravityMouthRequiredCurvature]
  norm_num

/-- A configuration whose gravity projection realizes the first transported
residual still cannot inhabit the full joint zero fiber, because `K r ≠ 0`.
Transport and terminal closure are different predicates. -/
theorem transportedGravityProjection_not_jointZeroFiber
    (configuration : StageNineHolonomicConfiguration)
    (transported :
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          configuration 0).gravityAuxiliary =
        positiveSourceGravityMouthTransportedResidual) :
    ¬ CurrentJointShellZeroFiber positiveSmoothUnifiedSource configuration := by
  intro zeroFiber
  have residualZero :=
    (currentJointShellZeroFiber_iff_pointwise
      positiveSmoothUnifiedSource configuration).mp zeroFiber 0
  have gravityZero := congrArg
    (fun residual => residual.algebraic.gravityAuxiliary)
    residualZero
  apply positiveSourceGravityMouthTransportedResidual_ne_zero
  rw [← transported]
  simpa [currentPointwiseJointShellResidual] using gravityZero

/-! ## Stable origin-curvature non-injectivity carrier -/

def timeCoordinate : BasePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (EuclideanSpace.equiv LorentzianIndex ℝ).toContinuousLinearMap

@[simp] theorem timeCoordinate_zero :
    timeCoordinate (0 : BasePoint) = 0 :=
  map_zero timeCoordinate

/-- A scalar quadratic perturbation.  Its value and first jet vanish at the
origin, but the field is globally nonzero. -/
def quadraticCoordinateScalar : BasePoint → ℝ :=
  (timeCoordinate : BasePoint → ℝ) * timeCoordinate

theorem quadraticCoordinateScalar_fderiv_origin :
    fderiv ℝ quadraticCoordinateScalar (0 : BasePoint) = 0 := by
  have derivative :=
    (timeCoordinate.hasFDerivAt (x := (0 : BasePoint))).mul
      (timeCoordinate.hasFDerivAt (x := (0 : BasePoint)))
  simpa [quadraticCoordinateScalar] using derivative.fderiv

theorem quadraticCoordinateScalar_hasFDerivAt_origin :
    HasFDerivAt quadraticCoordinateScalar
      (0 : BasePoint →L[ℝ] ℝ) (0 : BasePoint) := by
  have derivative :=
    (timeCoordinate.hasFDerivAt (x := (0 : BasePoint))).mul
      (timeCoordinate.hasFDerivAt (x := (0 : BasePoint)))
  simpa [quadraticCoordinateScalar] using derivative

theorem quadraticCoordinateScalar_contDiff :
    ContDiff ℝ ∞ quadraticCoordinateScalar := by
  exact timeCoordinate.contDiff.mul timeCoordinate.contDiff

/-- One fixed nonzero internal boost coordinate.  It is a probe direction in
connection-field space, not a source datum. -/
def seedLorentzBivectorOneForm : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    if formDirection = 0 ∧ internalPair = 0 then 1 else 0

def zeroLorentzConnectionField : LorentzConnectionField :=
  fun _ => 0

/-- A different connection whose zero- and first-order jets agree with the
zero connection at the origin. -/
def quadraticLorentzConnectionField : LorentzConnectionField :=
  fun point =>
    lorentzSkewConnectionOfBivectorOneForm
      (quadraticCoordinateScalar point • seedLorentzBivectorOneForm)

def SmoothLorentzConnectionField
    (connection : LorentzConnectionField) : Prop :=
  ∀ formDirection internalOut internalIn,
    ContDiff ℝ ∞ fun point =>
      connection point formDirection internalOut internalIn

/-- Explicit carrier class used by this no-go.  It audits connection fields;
it is not a new primitive dynamics type. -/
structure SmoothLorentzAdmissibleConnectionField where
  connection : LorentzConnectionField
  smooth : SmoothLorentzConnectionField connection
  lorentzSkew : ∀ point, LorentzSkew (connection point)

theorem zeroLorentzConnectionField_smooth :
    SmoothLorentzConnectionField zeroLorentzConnectionField := by
  intro formDirection internalOut internalIn
  exact contDiff_const

theorem quadraticLorentzConnectionField_component_eq
    (formDirection internalOut internalIn : LorentzianIndex) :
    (fun point =>
      quadraticLorentzConnectionField point formDirection internalOut
        internalIn) =
      quadraticCoordinateScalar * fun _ : BasePoint =>
        lorentzSkewConnectionOfBivectorOneForm
          seedLorentzBivectorOneForm formDirection internalOut internalIn := by
  funext point
  rw [show quadraticLorentzConnectionField point =
      lorentzSkewConnectionOfBivectorOneForm
        (quadraticCoordinateScalar point • seedLorentzBivectorOneForm) from rfl,
    lorentzSkewConnectionOfBivectorOneForm_smul]
  rfl

theorem quadraticLorentzConnectionField_smooth :
    SmoothLorentzConnectionField quadraticLorentzConnectionField := by
  intro formDirection internalOut internalIn
  rw [quadraticLorentzConnectionField_component_eq]
  exact quadraticCoordinateScalar_contDiff.mul contDiff_const

theorem zeroLorentzConnectionField_lorentzSkew (point : BasePoint) :
    LorentzSkew (zeroLorentzConnectionField point) := by
  have liftZero :
      lorentzSkewConnectionOfBivectorOneForm
          (0 : LorentzBivectorOneForm) = 0 := by
    simpa only [zero_smul] using lorentzSkewConnectionOfBivectorOneForm_smul
      0 seedLorentzBivectorOneForm
  change LorentzSkew (0 : PointwiseLorentzSpinConnection)
  rw [← liftZero]
  exact lorentzSkewConnectionOfBivectorOneForm_lorentzSkew _

theorem quadraticLorentzConnectionField_lorentzSkew (point : BasePoint) :
    LorentzSkew (quadraticLorentzConnectionField point) := by
  exact lorentzSkewConnectionOfBivectorOneForm_lorentzSkew _

@[simp] theorem quadraticCoordinateScalar_origin :
    quadraticCoordinateScalar (0 : BasePoint) = 0 := by
  simp [quadraticCoordinateScalar]

theorem quadraticLorentzConnectionField_origin :
    quadraticLorentzConnectionField (0 : BasePoint) =
      zeroLorentzConnectionField (0 : BasePoint) := by
  funext formDirection internalOut internalIn
  have component := congrFun
    (quadraticLorentzConnectionField_component_eq formDirection internalOut
      internalIn) (0 : BasePoint)
  simpa [zeroLorentzConnectionField] using component

theorem quadraticLorentzConnectionField_fderiv_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    fderiv ℝ
        (fun point => quadraticLorentzConnectionField point formDirection
          internalOut internalIn)
        (0 : BasePoint) = 0 := by
  rw [quadraticLorentzConnectionField_component_eq]
  have derivative := quadraticCoordinateScalar_hasFDerivAt_origin.mul
    (hasFDerivAt_const (x := (0 : BasePoint))
      (c := lorentzSkewConnectionOfBivectorOneForm
        seedLorentzBivectorOneForm formDirection internalOut internalIn))
  simpa using derivative.fderiv

/-- Embed a connection field only to reuse the actual Stage-9
`holonomicGravityCurvature` readout.  The zero values in unrelated fields are
not claimed to form an admissible or stationary physical configuration. -/
def configurationOfLorentzConnection
    (connection : LorentzConnectionField) :
    StageNineHolonomicConfiguration where
  coframe := 0
  gravityConnection := connection
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection := 0
  gaugeAuxiliary := 0
  scalar := 0
  matter := 0
  conjugateMatter := 0

def originHolonomicGravityCurvature
    (field : SmoothLorentzAdmissibleConnectionField) : PhysicalBivector :=
  holonomicGravityCurvature
    (configurationOfLorentzConnection field.connection) 0

def zeroConnectionCarrier : SmoothLorentzAdmissibleConnectionField where
  connection := zeroLorentzConnectionField
  smooth := zeroLorentzConnectionField_smooth
  lorentzSkew := zeroLorentzConnectionField_lorentzSkew

def quadraticConnectionCarrier : SmoothLorentzAdmissibleConnectionField where
  connection := quadraticLorentzConnectionField
  smooth := quadraticLorentzConnectionField_smooth
  lorentzSkew := quadraticLorentzConnectionField_lorentzSkew

theorem zeroConnectionCarrier_curvature_origin :
    originHolonomicGravityCurvature zeroConnectionCarrier = 0 := by
  funext internalPair spacetimePair
  simp [originHolonomicGravityCurvature, zeroConnectionCarrier,
    holonomicGravityCurvature, gravityConnectionDerivative,
    configurationOfLorentzConnection, zeroLorentzConnectionField]

theorem quadraticConnectionCarrier_curvature_origin :
    originHolonomicGravityCurvature quadraticConnectionCarrier = 0 := by
  funext internalPair spacetimePair
  simp [originHolonomicGravityCurvature, quadraticConnectionCarrier,
    holonomicGravityCurvature, gravityConnectionDerivative,
    configurationOfLorentzConnection,
    quadraticLorentzConnectionField_fderiv_origin,
    quadraticLorentzConnectionField_origin, zeroLorentzConnectionField]

theorem quadraticLorentzConnectionField_witness_component :
    quadraticLorentzConnectionField (coordinateDirection 0) 0 0 1 = -1 := by
  simp [quadraticLorentzConnectionField,
    quadraticCoordinateScalar, timeCoordinate, coordinateDirection,
    seedLorentzBivectorOneForm,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    minkowskiInternalSign, pairFirst, pairSecond]

theorem lorentzConnectionFields_ne :
    zeroLorentzConnectionField ≠ quadraticLorentzConnectionField := by
  intro equality
  have component := congrArg
    (fun connection : LorentzConnectionField =>
      connection (coordinateDirection 0) 0 0 1) equality
  rw [quadraticLorentzConnectionField_witness_component] at component
  simp [zeroLorentzConnectionField] at component

theorem zeroConnectionCarrier_ne_quadraticConnectionCarrier :
    zeroConnectionCarrier ≠ quadraticConnectionCarrier := by
  intro carrierEquality
  exact lorentzConnectionFields_ne
    (congrArg SmoothLorentzAdmissibleConnectionField.connection carrierEquality)

/-- Stable typed no-go: the actual origin-curvature readout is not injective
on smooth Lorentz-admissible connection fields. -/
theorem originHolonomicGravityCurvature_not_injective :
    ¬ Function.Injective originHolonomicGravityCurvature := by
  intro injective
  apply zeroConnectionCarrier_ne_quadraticConnectionCarrier
  apply injective
  rw [zeroConnectionCarrier_curvature_origin,
    quadraticConnectionCarrier_curvature_origin]

/-- The same no-go retains the stronger fixed-origin-value witness. -/
theorem originHolonomicGravityCurvature_not_injective_with_fixed_value :
    ∃ first second : SmoothLorentzAdmissibleConnectionField,
      first.connection (0 : BasePoint) = second.connection 0 ∧
      first ≠ second ∧
      originHolonomicGravityCurvature first =
        originHolonomicGravityCurvature second := by
  refine ⟨zeroConnectionCarrier, quadraticConnectionCarrier,
    quadraticLorentzConnectionField_origin.symm,
    zeroConnectionCarrier_ne_quadraticConnectionCarrier, ?_⟩
  rw [zeroConnectionCarrier_curvature_origin,
    quadraticConnectionCarrier_curvature_origin]

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthConnectionLiftNoGo
