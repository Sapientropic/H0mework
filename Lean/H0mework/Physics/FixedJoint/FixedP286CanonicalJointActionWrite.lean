import H0mework.Physics.GaugeAction.P286CanonicalDiagonalActionPrincipal
import H0mework.Physics.FinalJoint.FixedGlobalRegularity
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity
import H0mework.Physics.GaugeAction.P286GaugeDerivativeIntegrationByParts
import H0mework.Physics.GaugeAction.P286GaugeYangMillsReadout

/-!
# Fixed P506/L0 canonical P286 joint action write

This module applies the canonical diagonal P286 action principal to the fixed
P506/L0 final common current.  A candidate first installs the generated
connection Hessian and then recomputes the primitive auxiliary field through
the authoritative form-native constitutive inverse:

```text
fixed final current
  -> canonical action-principal connection second jet
  -> live post-connection curvature
  -> form-native constitutive auxiliary
  -> one common A/B candidate actual.
```

The origin forcing is read from the complete W13 action covector of the zero
candidate.  No residual carrier, support coordinate, target field, equation
receipt, branch choice, or free coefficient enters a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonMatterAcceptance
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineCoframeFirstJet
open StageNineCoframeTwoFormPairing
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ColorCartanConstitutiveResponse
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalFourFormPairing
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

open scoped ContDiff Matrix.Norms.Elementwise

local instance fixedCanonicalWriteP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedCanonicalWriteP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance fixedCanonicalWriteP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Forward candidate family -/

/-- The fixed P506/L0 current whose live P286 action channel is advanced. -/
abbrev fixedP506L0P286CanonicalActionInput :
    StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

/-- First write only the canonical action-principal connection Hessian. -/
def fixedP506L0P286CanonicalConnectionCandidate
    (write : P286GaugeOneForm) : StageNineHolonomicConfiguration :=
  installP286HolonomicConnectionSecondJet
    fixedP506L0P286CanonicalActionInput
    (p286CanonicalDiagonalResponseSecondJet write) 1

/-- Recompute `B` from the post-`A` live curvature on the same actual. -/
def fixedP506L0P286CanonicalJointCandidate
    (write : P286GaugeOneForm) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource
    (fixedP506L0P286CanonicalConnectionCandidate write)

@[simp] theorem fixedP506L0P286CanonicalJointCandidate_coframe
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).coframe =
      fixedP506L0P286CanonicalActionInput.coframe :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalJointCandidate_gaugeConnection
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).gaugeConnection =
      (fixedP506L0P286CanonicalConnectionCandidate write).gaugeConnection :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalJointCandidate_gaugeAuxiliary
    (write : P286GaugeOneForm) (point : BasePoint) :
    (fixedP506L0P286CanonicalJointCandidate write).gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0P286CanonicalActionInput.coframe point)
        (holonomicGaugeCurvature
          (fixedP506L0P286CanonicalConnectionCandidate write) point) :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalJointCandidate_gravityConnection
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).gravityConnection =
      fixedP506L0P286CanonicalActionInput.gravityConnection :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalJointCandidate_scalar
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).scalar =
      fixedP506L0P286CanonicalActionInput.scalar :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalJointCandidate_matter
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).matter =
      fixedP506L0P286CanonicalActionInput.matter :=
  rfl

theorem fixedP506L0P286CanonicalJointCandidate_connection_origin
    (write : P286GaugeOneForm) :
    holonomicP286GaugeConnectionCoordinate
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      holonomicP286GaugeConnectionCoordinate
        fixedP506L0P286CanonicalActionInput 0 := by
  change
    holonomicP286GaugeConnectionCoordinate
        (fixedP506L0P286CanonicalConnectionCandidate write) 0 = _
  exact installP286HolonomicConnectionSecondJet_connection_origin
    fixedP506L0P286CanonicalActionInput
    (p286CanonicalDiagonalResponseSecondJet write) 1

theorem fixedP506L0P286CanonicalJointCandidate_curvature_origin
    (write : P286GaugeOneForm) :
    holonomicP286GaugeCurvatureCoordinate
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      holonomicP286GaugeCurvatureCoordinate
        fixedP506L0P286CanonicalActionInput 0 := by
  change
    holonomicP286GaugeCurvatureCoordinate
        (fixedP506L0P286CanonicalConnectionCandidate write) 0 = _
  exact installP286HolonomicConnectionSecondJet_curvature_origin
    fixedP506L0P286CanonicalActionInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet write) 1

/-! ## Fixed live constitutive tangent -/

private abbrev FixedP506L0P286CanonicalBoundary :=
  sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource

/-- The already authoritative action inverse, exposed on its faithful joint
coframe/curvature chart at the fixed source boundary. -/
def fixedP506L0P286CanonicalActionInverse :
    LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm →
      FormNativeP286GaugeCoordinateTwoForm :=
  fun joint =>
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
      FixedP506L0P286CanonicalBoundary joint.1 joint.2

private theorem fixedP506L0P286CanonicalBlockCoupling_same
    (parameter : ℝ) (coordinate : P286CoordinateCarrier) :
    formNativeP286BlockwiseCouplingCoordinateLinear
        parameter parameter parameter coordinate =
      parameter • coordinate := by
  apply p286CoordinateEquiv.symm.injective
  simp [formNativeP286BlockwiseCouplingCoordinateLinear,
    formNativeP286BlockwiseCouplingActualLinear]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

private theorem
    fixedP506L0P286CanonicalCoordinateBlockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe
        ((FixedP506L0P286CanonicalBoundary.strongCouplingSquared : ℝ)⁻¹)
        ((FixedP506L0P286CanonicalBoundary.weakCouplingSquared : ℝ)⁻¹)
        ((FixedP506L0P286CanonicalBoundary.hyperchargeCouplingSquared : ℝ)⁻¹)
        form =
      liftGaugeTwoFormOperator
        (((FixedP506L0P286CanonicalBoundary.strongCouplingSquared : ℝ)⁻¹ •
          coframeGaugeSpacetimeHodgeLinear coframe))
        form := by
  have weakEq :
      ((FixedP506L0P286CanonicalBoundary.weakCouplingSquared : ℝ)⁻¹) =
        ((FixedP506L0P286CanonicalBoundary.strongCouplingSquared : ℝ)⁻¹) := by
    rfl
  have hyperchargeEq :
      ((FixedP506L0P286CanonicalBoundary.hyperchargeCouplingSquared : ℝ)⁻¹) =
        ((FixedP506L0P286CanonicalBoundary.strongCouplingSquared : ℝ)⁻¹) := by
    rfl
  rw [weakEq, hyperchargeEq,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum,
    liftGaugeTwoFormOperator_smul_operator_p286]
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  simp_rw [fixedP506L0P286CanonicalBlockCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

theorem fixedP506L0P286CanonicalActionInverse_one_eq_existing
    (curvature : FormNativeP286GaugeCoordinateTwoForm) :
    fixedP506L0P286CanonicalActionInverse (1, curvature) =
      p286GaugeConstitutiveAuxiliaryCoordinate positiveSmoothUnifiedSource 1
        curvature := by
  unfold fixedP506L0P286CanonicalActionInverse
  rw [
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_eq_neg_constitutive,
    fixedP506L0P286CanonicalCoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  module

/-- The only linear operator needed below: curvature transport through the
existing constitutive inverse with the coframe fixed to the actual origin
value.  No linearity in a varying coframe is asserted. -/
def fixedP506L0P286CanonicalIdentityConstitutiveLinear :
    FormNativeP286GaugeCoordinateTwoForm →ₗ[ℝ]
      FormNativeP286GaugeCoordinateTwoForm where
  toFun :=
    p286GaugeConstitutiveAuxiliaryCoordinate positiveSmoothUnifiedSource 1
  map_add' := by
    intro first second
    funext pair
    simp [p286GaugeConstitutiveAuxiliaryCoordinate,
      liftGaugeTwoFormOperator_add_p286]
  map_smul' := by
    intro parameter form
    funext pair
    simp [p286GaugeConstitutiveAuxiliaryCoordinate,
      liftGaugeTwoFormOperator_smul_p286]
    module

private theorem fixedP506L0P286CanonicalActionInput_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt
        fixedP506L0P286CanonicalActionInput.coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [← fixedP506L0FinalCommonMatterSmoothComparison_coframe_eq_final 0]
  exact fixedP506L0FinalCommonMatterSmoothComparison_coframeFirstJet_origin 0

private theorem fixedP506L0P286CanonicalActionInput_coframe_origin :
    fixedP506L0P286CanonicalActionInput.coframe 0 = 1 := by
  exact congrArg PointwiseLorentzianCoframeJet.coframe
    fixedP506L0P286CanonicalActionInput_coframeFirstJet_origin

private theorem fixedP506L0P286CanonicalConnectionCandidate_smooth
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalConnectionCandidate write).Smooth :=
  installP286HolonomicConnectionSecondJet_smooth
    fixedP506L0P286CanonicalActionInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet write) 1

private theorem fixedP506L0P286CanonicalConnectionCandidate_zero :
    fixedP506L0P286CanonicalConnectionCandidate 0 =
      fixedP506L0P286CanonicalActionInput := by
  unfold fixedP506L0P286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [map_zero, map_zero]
  apply StageNineHolonomicConfiguration.ext <;>
    simp [varyP286GaugeConnectionCoordinate,
      holonomicP286GaugeConnectionCoordinate]

private theorem
    fixedP506L0P286CanonicalJointCandidate_auxiliaryCoordinate
    (write : P286GaugeOneForm) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (fixedP506L0P286CanonicalJointCandidate write) point =
      fixedP506L0P286CanonicalActionInverse
        (fixedP506L0P286CanonicalActionInput.coframe point,
          holonomicP286GaugeCurvatureCoordinate
            (fixedP506L0P286CanonicalConnectionCandidate write) point) := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
    fixedP506L0P286CanonicalActionInverse
  change
    formNativeP286GaugeActualToCoordinateLinear
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          FixedP506L0P286CanonicalBoundary
          (fixedP506L0P286CanonicalActionInput.coframe point)
          (holonomicGaugeCurvature
            (fixedP506L0P286CanonicalConnectionCandidate write) point)) =
      formNativeP286GaugeActualToCoordinateLinear
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          FixedP506L0P286CanonicalBoundary
          (fixedP506L0P286CanonicalActionInput.coframe point)
          (formNativeP286GaugeCoordinateToActualLinear
            (formNativeP286GaugeActualToCoordinateLinear
              (holonomicGaugeCurvature
                (fixedP506L0P286CanonicalConnectionCandidate write)
                point))))
  rw [formNativeP286GaugeActual_coordinate_actual]

private theorem fixedP506L0P286CanonicalJointCandidate_connection_origin_raw
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).gaugeConnection 0 =
      fixedP506L0P286CanonicalActionInput.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  exact congrFun
    (fixedP506L0P286CanonicalJointCandidate_connection_origin write)
    direction

private theorem fixedP506L0P286CanonicalJointCandidate_curvature_origin_raw
    (write : P286GaugeOneForm) :
    holonomicGaugeCurvature
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      holonomicGaugeCurvature fixedP506L0P286CanonicalActionInput 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (fixedP506L0P286CanonicalJointCandidate_curvature_origin write) pair

private theorem fixedP506L0P286CanonicalJointCandidate_auxiliary_origin
    (write : P286GaugeOneForm) :
    (fixedP506L0P286CanonicalJointCandidate write).gaugeAuxiliary 0 =
      (fixedP506L0P286CanonicalJointCandidate 0).gaugeAuxiliary 0 := by
  rw [fixedP506L0P286CanonicalJointCandidate_gaugeAuxiliary,
    fixedP506L0P286CanonicalJointCandidate_gaugeAuxiliary]
  have curvatureCoordinateEquality :
      holonomicP286GaugeCurvatureCoordinate
          (fixedP506L0P286CanonicalConnectionCandidate write) 0 =
        holonomicP286GaugeCurvatureCoordinate
          (fixedP506L0P286CanonicalConnectionCandidate 0) 0 :=
    (installP286HolonomicConnectionSecondJet_curvature_origin
      fixedP506L0P286CanonicalActionInput
      (fixedP506L0FinalCommonActionActual_smooth 0)
      (p286CanonicalDiagonalResponseSecondJet write) 1).trans
      (installP286HolonomicConnectionSecondJet_curvature_origin
        fixedP506L0P286CanonicalActionInput
        (fixedP506L0FinalCommonActionActual_smooth 0)
        (p286CanonicalDiagonalResponseSecondJet 0) 1).symm
  have curvatureEquality :
      holonomicGaugeCurvature
          (fixedP506L0P286CanonicalConnectionCandidate write) 0 =
        holonomicGaugeCurvature
          (fixedP506L0P286CanonicalConnectionCandidate 0) 0 := by
    funext pair
    apply p286CoordinateEquiv.injective
    exact congrFun curvatureCoordinateEquality pair
  rw [curvatureEquality]

private theorem fixedP506L0P286CanonicalJointCandidate_pointField_origin
    (write : P286GaugeOneForm) :
    toContinuumPointField
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      toContinuumPointField
        (fixedP506L0P286CanonicalJointCandidate 0) 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (fixedP506L0P286CanonicalJointCandidate_curvature_origin_raw
      write).trans
      (fixedP506L0P286CanonicalJointCandidate_curvature_origin_raw 0).symm
  · exact fixedP506L0P286CanonicalJointCandidate_auxiliary_origin write
  · rfl
  · change
      holonomicScalarCovariantDerivative
          (fixedP506L0P286CanonicalJointCandidate write) 0 =
        holonomicScalarCovariantDerivative
          (fixedP506L0P286CanonicalJointCandidate 0) 0
    funext direction
    unfold holonomicScalarCovariantDerivative
    rw [fixedP506L0P286CanonicalJointCandidate_scalar,
      fixedP506L0P286CanonicalJointCandidate_scalar,
      fixedP506L0P286CanonicalJointCandidate_connection_origin_raw,
      fixedP506L0P286CanonicalJointCandidate_connection_origin_raw]
  · rfl
  · change
      holonomicMatterCovariantDerivative
          (fixedP506L0P286CanonicalJointCandidate write) 0 =
        holonomicMatterCovariantDerivative
          (fixedP506L0P286CanonicalJointCandidate 0) 0
    funext direction
    unfold holonomicMatterCovariantDerivative
    rw [fixedP506L0P286CanonicalJointCandidate_matter,
      fixedP506L0P286CanonicalJointCandidate_matter,
      fixedP506L0P286CanonicalJointCandidate_gravityConnection,
      fixedP506L0P286CanonicalJointCandidate_gravityConnection,
      fixedP506L0P286CanonicalJointCandidate_connection_origin_raw,
      fixedP506L0P286CanonicalJointCandidate_connection_origin_raw]
  · rfl

private def fixedP506L0P286CanonicalJointInput
    (write : P286GaugeOneForm) (point : BasePoint) :
    LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm :=
  (fixedP506L0P286CanonicalActionInput.coframe point,
    holonomicP286GaugeCurvatureCoordinate
      (fixedP506L0P286CanonicalConnectionCandidate write) point)

private theorem fixedP506L0P286CanonicalJointInput_origin
    (write : P286GaugeOneForm) :
    fixedP506L0P286CanonicalJointInput write 0 =
      (1,
        holonomicP286GaugeCurvatureCoordinate
          fixedP506L0P286CanonicalActionInput 0) := by
  apply Prod.ext
  · exact fixedP506L0P286CanonicalActionInput_coframe_origin
  · exact fixedP506L0P286CanonicalJointCandidate_curvature_origin write

private theorem fixedP506L0P286CanonicalInput_coframe_differentiableAt :
    DifferentiableAt ℝ fixedP506L0P286CanonicalActionInput.coframe 0 :=
  (holonomicCoframe_contDiff fixedP506L0P286CanonicalActionInput
    (fixedP506L0FinalCommonActionActual_smooth 0)).differentiable (by simp)
      |>.differentiableAt

private theorem fixedP506L0P286CanonicalCandidate_curvature_differentiableAt
    (write : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (holonomicP286GaugeCurvatureCoordinate
        (fixedP506L0P286CanonicalConnectionCandidate write)) 0 := by
  apply differentiableAt_pi.mpr
  intro pair
  exact
    (holonomicGaugeCurvature_coordinate_contDiff
      (fixedP506L0P286CanonicalConnectionCandidate write)
      (fixedP506L0P286CanonicalConnectionCandidate_smooth write) pair
      ).differentiable (by simp) |>.differentiableAt

private theorem fixedP506L0P286CanonicalJointInput_differentiableAt
    (write : P286GaugeOneForm) :
    DifferentiableAt ℝ (fixedP506L0P286CanonicalJointInput write) 0 :=
  fixedP506L0P286CanonicalInput_coframe_differentiableAt.prodMk
    (fixedP506L0P286CanonicalCandidate_curvature_differentiableAt write)

private theorem fixedP506L0P286CanonicalActionInverse_differentiableAt :
    DifferentiableAt ℝ fixedP506L0P286CanonicalActionInverse
      (1,
        holonomicP286GaugeCurvatureCoordinate
          fixedP506L0P286CanonicalActionInput 0) :=
  formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_differentiableAt
    FixedP506L0P286CanonicalBoundary 1 (by norm_num)
    (holonomicP286GaugeCurvatureCoordinate
      fixedP506L0P286CanonicalActionInput 0)

/-- The vertical derivative of the live inverse is the same action inverse
applied to the curvature tangent.  This is obtained from the existing
operator's exact curvature-linearity, not from a residual coordinate. -/
theorem fixedP506L0P286CanonicalActionInverse_fderiv_vertical
    (curvature displacement : FormNativeP286GaugeCoordinateTwoForm) :
    (fderiv ℝ fixedP506L0P286CanonicalActionInverse (1, curvature))
        (0, displacement) =
      fixedP506L0P286CanonicalActionInverse (1, displacement) := by
  let axis : ℝ →
      LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm :=
    fun parameter => (1, curvature + parameter • displacement)
  have outerDifferentiable :
      DifferentiableAt ℝ fixedP506L0P286CanonicalActionInverse
        (1, curvature) :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_differentiableAt
      FixedP506L0P286CanonicalBoundary 1 (by norm_num) curvature
  have axisDerivative : HasDerivAt axis (0, displacement) 0 := by
    have curvatureDerivative :
        HasDerivAt (fun parameter : ℝ =>
          curvature + parameter • displacement) displacement 0 := by
      have displacementDerivative :
          HasDerivAt (fun parameter : ℝ => parameter • displacement)
            displacement 0 := by
        simpa using
          (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const displacement
      exact displacementDerivative.const_add curvature
    change HasDerivAt
      (fun parameter : ℝ =>
        ((1 : LorentzianCoframe), curvature + parameter • displacement))
      (0, displacement) 0
    exact (hasDerivAt_const (x := (0 : ℝ))
      (c := (1 : LorentzianCoframe))).prodMk curvatureDerivative
  have outerAtAxisOrigin :
      HasFDerivAt fixedP506L0P286CanonicalActionInverse
        (fderiv ℝ fixedP506L0P286CanonicalActionInverse (1, curvature))
        (axis 0) := by
    simpa [axis] using outerDifferentiable.hasFDerivAt
  have direct := outerAtAxisOrigin.comp_hasDerivAt 0 axisDerivative
  change HasDerivAt
    (fun parameter : ℝ =>
      fixedP506L0P286CanonicalActionInverse
        (1, curvature + parameter • displacement))
    ((fderiv ℝ fixedP506L0P286CanonicalActionInverse (1, curvature))
      (0, displacement)) 0 at direct
  have expected :
      HasDerivAt
        (fun parameter : ℝ =>
          fixedP506L0P286CanonicalActionInverse
            (1, curvature + parameter • displacement))
        (fixedP506L0P286CanonicalActionInverse (1, displacement)) 0 := by
    have scaledDerivative :
        HasDerivAt
          (fun parameter : ℝ =>
            parameter •
              fixedP506L0P286CanonicalIdentityConstitutiveLinear displacement)
          (fixedP506L0P286CanonicalIdentityConstitutiveLinear displacement)
          0 := by
      simpa using
        (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const
          (fixedP506L0P286CanonicalIdentityConstitutiveLinear displacement)
    have linearDerivative :
        HasDerivAt
          (fun parameter : ℝ =>
            fixedP506L0P286CanonicalIdentityConstitutiveLinear curvature +
              parameter •
                fixedP506L0P286CanonicalIdentityConstitutiveLinear
                  displacement)
          (fixedP506L0P286CanonicalIdentityConstitutiveLinear displacement)
          0 := by
      exact scaledDerivative.const_add
        (fixedP506L0P286CanonicalIdentityConstitutiveLinear curvature)
    have functionEquality :
        (fun parameter : ℝ =>
          fixedP506L0P286CanonicalActionInverse
            (1, curvature + parameter • displacement)) =
          fun parameter : ℝ =>
            fixedP506L0P286CanonicalIdentityConstitutiveLinear curvature +
              parameter •
                fixedP506L0P286CanonicalIdentityConstitutiveLinear
                  displacement := by
      funext parameter
      rw [fixedP506L0P286CanonicalActionInverse_one_eq_existing]
      change
        fixedP506L0P286CanonicalIdentityConstitutiveLinear
            (curvature + parameter • displacement) = _
      rw [map_add, map_smul]
    have derivativeEquality :
        fixedP506L0P286CanonicalActionInverse (1, displacement) =
          fixedP506L0P286CanonicalIdentityConstitutiveLinear displacement := by
      rw [fixedP506L0P286CanonicalActionInverse_one_eq_existing]
      rfl
    rw [functionEquality, derivativeEquality]
    simpa only [zero_add, one_smul] using linearDerivative
  exact direct.unique expected

private theorem fixedP506L0P286CanonicalCandidate_curvature_fderiv_apply
    (write : P286GaugeOneForm) (direction : LorentzianIndex)
    (pair : Fin 6) :
    ((fderiv ℝ
        (holonomicP286GaugeCurvatureCoordinate
          (fixedP506L0P286CanonicalConnectionCandidate write)) 0)
        (coordinateDirection direction)) pair =
      fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (fixedP506L0P286CanonicalConnectionCandidate write) point pair)
        0 direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply
    (fixedP506L0P286CanonicalCandidate_curvature_differentiableAt write) pair
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] P286CoordinateCarrier =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

private theorem fixedP506L0P286CanonicalCandidate_curvature_fderiv_affine
    (write : P286GaugeOneForm) (direction : LorentzianIndex) :
    (fderiv ℝ
        (holonomicP286GaugeCurvatureCoordinate
          (fixedP506L0P286CanonicalConnectionCandidate write)) 0)
        (coordinateDirection direction) =
      (fderiv ℝ
          (holonomicP286GaugeCurvatureCoordinate
            (fixedP506L0P286CanonicalConnectionCandidate 0)) 0)
          (coordinateDirection direction) +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction := by
  funext pair
  calc
    ((fderiv ℝ
        (holonomicP286GaugeCurvatureCoordinate
          (fixedP506L0P286CanonicalConnectionCandidate write)) 0)
        (coordinateDirection direction)) pair =
      fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (fixedP506L0P286CanonicalConnectionCandidate write) point pair)
        0 direction :=
      fixedP506L0P286CanonicalCandidate_curvature_fderiv_apply
        write direction pair
    _ = fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate
              fixedP506L0P286CanonicalActionInput point pair)
          0 direction +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction pair := by
      change
        fieldDirectionalDerivative
            (fun point =>
              holonomicP286GaugeCurvatureCoordinate
                (installP286HolonomicConnectionSecondJet
                  fixedP506L0P286CanonicalActionInput
                  (p286CanonicalDiagonalResponseSecondJet write) 1)
                point pair)
            0 direction = _
      rw [
        installP286HolonomicConnectionSecondJet_curvatureDirectionalDerivative_origin
          fixedP506L0P286CanonicalActionInput
          (fixedP506L0FinalCommonActionActual_smooth 0)
          (p286CanonicalDiagonalResponseSecondJet write) 1 direction pair]
      simp
    _ = fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate
              (fixedP506L0P286CanonicalConnectionCandidate 0) point pair)
          0 direction +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction pair := by
      rw [fixedP506L0P286CanonicalConnectionCandidate_zero]
    _ = ((fderiv ℝ
          (holonomicP286GaugeCurvatureCoordinate
            (fixedP506L0P286CanonicalConnectionCandidate 0)) 0)
          (coordinateDirection direction)) pair +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction pair := by
      rw [fixedP506L0P286CanonicalCandidate_curvature_fderiv_apply]

private theorem fixedP506L0P286CanonicalJointInput_fderiv_affine
    (write : P286GaugeOneForm) (direction : LorentzianIndex) :
    (fderiv ℝ (fixedP506L0P286CanonicalJointInput write) 0)
        (coordinateDirection direction) =
      (fderiv ℝ (fixedP506L0P286CanonicalJointInput 0) 0)
          (coordinateDirection direction) +
        (0,
          p286HolonomicSecondJetCurvatureSymbol
            (p286CanonicalDiagonalResponseSecondJet write) direction) := by
  change
    (fderiv ℝ
        (fun point =>
          (fixedP506L0P286CanonicalActionInput.coframe point,
            holonomicP286GaugeCurvatureCoordinate
              (fixedP506L0P286CanonicalConnectionCandidate write) point)) 0)
        (coordinateDirection direction) =
      (fderiv ℝ
          (fun point =>
            (fixedP506L0P286CanonicalActionInput.coframe point,
              holonomicP286GaugeCurvatureCoordinate
                (fixedP506L0P286CanonicalConnectionCandidate 0) point)) 0)
          (coordinateDirection direction) +
        (0,
          p286HolonomicSecondJetCurvatureSymbol
            (p286CanonicalDiagonalResponseSecondJet write) direction)
  have writeProductDerivative :=
    fixedP506L0P286CanonicalInput_coframe_differentiableAt.fderiv_prodMk
      (fixedP506L0P286CanonicalCandidate_curvature_differentiableAt write)
  have zeroProductDerivative :=
    fixedP506L0P286CanonicalInput_coframe_differentiableAt.fderiv_prodMk
      (fixedP506L0P286CanonicalCandidate_curvature_differentiableAt 0)
  have writeProductDerivativeAt :
      (fderiv ℝ
          (fun point : BasePoint =>
            (fixedP506L0P286CanonicalActionInput.coframe point,
              holonomicP286GaugeCurvatureCoordinate
                (fixedP506L0P286CanonicalConnectionCandidate write) point)) 0)
          (coordinateDirection direction) =
        ((fderiv ℝ fixedP506L0P286CanonicalActionInput.coframe 0).prod
          (fderiv ℝ
            (holonomicP286GaugeCurvatureCoordinate
              (fixedP506L0P286CanonicalConnectionCandidate write)) 0))
          (coordinateDirection direction) :=
    congrArg
      (fun derivative : BasePoint →L[ℝ]
          (LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) =>
        derivative (coordinateDirection direction))
      writeProductDerivative
  have zeroProductDerivativeAt :
      (fderiv ℝ
          (fun point : BasePoint =>
            (fixedP506L0P286CanonicalActionInput.coframe point,
              holonomicP286GaugeCurvatureCoordinate
                (fixedP506L0P286CanonicalConnectionCandidate 0) point)) 0)
          (coordinateDirection direction) =
        ((fderiv ℝ fixedP506L0P286CanonicalActionInput.coframe 0).prod
          (fderiv ℝ
            (holonomicP286GaugeCurvatureCoordinate
              (fixedP506L0P286CanonicalConnectionCandidate 0)) 0))
          (coordinateDirection direction) :=
    congrArg
      (fun derivative : BasePoint →L[ℝ]
          (LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) =>
        derivative (coordinateDirection direction))
      zeroProductDerivative
  rw [writeProductDerivativeAt, zeroProductDerivativeAt]
  apply Prod.ext
  · simp
  · exact
      fixedP506L0P286CanonicalCandidate_curvature_fderiv_affine
        write direction

private theorem fixedP506L0P286CanonicalJointCandidate_auxiliary_fderiv
    (write : P286GaugeOneForm) :
    fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0P286CanonicalJointCandidate write)) 0 =
      (fderiv ℝ fixedP506L0P286CanonicalActionInverse
          (1,
            holonomicP286GaugeCurvatureCoordinate
              fixedP506L0P286CanonicalActionInput 0)).comp
        (fderiv ℝ (fixedP506L0P286CanonicalJointInput write) 0) := by
  have outerAtOrigin :
      HasFDerivAt fixedP506L0P286CanonicalActionInverse
        (fderiv ℝ fixedP506L0P286CanonicalActionInverse
          (1,
            holonomicP286GaugeCurvatureCoordinate
              fixedP506L0P286CanonicalActionInput 0))
        (fixedP506L0P286CanonicalJointInput write 0) := by
    simpa [fixedP506L0P286CanonicalJointInput_origin] using
      fixedP506L0P286CanonicalActionInverse_differentiableAt.hasFDerivAt
  have composed := outerAtOrigin.comp 0
    (fixedP506L0P286CanonicalJointInput_differentiableAt write).hasFDerivAt
  have auxiliaryFunction :
      holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0P286CanonicalJointCandidate write) =
        fixedP506L0P286CanonicalActionInverse ∘
          fixedP506L0P286CanonicalJointInput write := by
    funext point
    exact fixedP506L0P286CanonicalJointCandidate_auxiliaryCoordinate
      write point
  rw [auxiliaryFunction]
  exact composed.fderiv

private theorem colorCartanQuadraticResidualRepair_coframe_origin_local :
    colorCartanQuadraticResidualRepair.coframe 0 = 1 := by
  unfold colorCartanQuadraticResidualRepair
  rw [colorCartanQuadraticConstitutiveResponse_coframe]
  change positiveSmoothUnifiedSource.legacy.coframeAt 0 = 1
  exact positiveSmoothUnifiedSource.legacy.coframeAt_zero

theorem
    fixedP506L0P286CanonicalActionInverse_vertical_eq_secondJetResponse
    (jet : P286HolonomicConnectionSecondJet)
    (direction : LorentzianIndex) :
    fixedP506L0P286CanonicalActionInverse
        (1, p286HolonomicSecondJetCurvatureSymbol jet direction) =
      p286HolonomicSecondJetConstitutiveAuxiliaryResponse jet direction := by
  rw [fixedP506L0P286CanonicalActionInverse_one_eq_existing]
  unfold p286HolonomicSecondJetConstitutiveAuxiliaryResponse
  rw [colorCartanQuadraticResidualRepair_coframe_origin_local]

/-- Exact first-jet displacement of the live, post-connection constitutive
readout.  Both `A` and `B` belong to this one candidate actual. -/
theorem fixedP506L0P286CanonicalJointCandidate_auxiliaryDerivative_affine
    (write : P286GaugeOneForm) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        (fixedP506L0P286CanonicalJointCandidate write) 0 direction =
      p286GaugeAuxiliaryDirectionalDerivative
          (fixedP506L0P286CanonicalJointCandidate 0) 0 direction +
        p286HolonomicSecondJetConstitutiveAuxiliaryResponse
          (p286CanonicalDiagonalResponseSecondJet write) direction := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [fixedP506L0P286CanonicalJointCandidate_auxiliary_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fixedP506L0P286CanonicalJointInput_fderiv_affine,
    map_add,
    fixedP506L0P286CanonicalActionInverse_fderiv_vertical,
    fixedP506L0P286CanonicalActionInverse_vertical_eq_secondJetResponse]
  rw [fixedP506L0P286CanonicalJointCandidate_auxiliary_fderiv]
  simp only [ContinuousLinearMap.comp_apply]

theorem
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_add_local
    (first second : LorentzianIndex → P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative (first + second) =
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative first +
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative second := by
  funext triple
  simp [pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    orderedP286GaugeTwoFormComponent_add]
  abel

private theorem fixedP506L0P286CanonicalJointCandidate_exteriorDerivative_affine
    (write : P286GaugeOneForm) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
          (fixedP506L0P286CanonicalJointCandidate 0) 0 +
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (p286HolonomicSecondJetConstitutiveAuxiliaryResponse
            (p286CanonicalDiagonalResponseSecondJet write)) := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      p286GaugeAuxiliaryDirectionalDerivative
          (fixedP506L0P286CanonicalJointCandidate 0) 0 +
        p286HolonomicSecondJetConstitutiveAuxiliaryResponse
          (p286CanonicalDiagonalResponseSecondJet write) by
    funext direction
    exact
      fixedP506L0P286CanonicalJointCandidate_auxiliaryDerivative_affine
        write direction]
  exact
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_add_local _ _

private theorem fixedP506L0P286Canonical_liftGaugeTwoFormOperator_id
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (LinearMap.id : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) form = form := by
  funext output
  unfold liftGaugeTwoFormOperator gaugeOperatorCoefficient
  simp

private theorem fixedP506L0P286CanonicalIdentityHodgePairing_eq_neg_wedge
    (first second : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1 first second =
      -generatedTwoFormWedgeCoefficient p286CoordinateLiePairing first
        second := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
    generatedTwoFormWedgeCoefficient
  rw [coframeTwoFormLinear_one]
  simp_rw [fixedP506L0P286Canonical_liftGaugeTwoFormOperator_id]
  rw [Fin.sum_univ_six]
  simp [
    StageNineP286SourceAffineCurvatureJetNormalForm.liftGaugeTwoFormOperator_fixedHodge_apply_local,
    lorentzianTwoFormSign, minkowskiInternalSign, twoFormComplement,
    pairFirst, pairSecond, Fin.sum_univ_six]
  abel

private theorem
    p286HolonomicSecondJetBFDivergenceResponseTerm_eq_neg_wedge_local
    (jet : P286HolonomicConnectionSecondJet)
    (direction : P286GaugeOneForm)
    (derivativeDirection : LorentzianIndex) :
    p286HolonomicSecondJetBFDivergenceResponseTerm jet direction
        derivativeDirection =
      -p286GaugeExteriorPrincipalBilinear derivativeDirection
        (p286HolonomicSecondJetConstitutiveAuxiliaryResponse jet
          derivativeDirection)
        direction := by
  unfold p286HolonomicSecondJetBFDivergenceResponseTerm
    p286GaugeBFCurvatureIncrementDensity generatedVolumeDensity
  change
    |Matrix.det (colorCartanQuadraticResidualRepair.coframe 0)| * _ = _
  rw [colorCartanQuadraticResidualRepair_coframe_origin_local]
  simp only [Matrix.det_one, abs_one, one_mul]
  rw [← p286GaugeAuxiliaryHodgePairingPolynomial_eq
    (1 : LorentzianCoframe) (by norm_num)]
  rw [fixedP506L0P286CanonicalIdentityHodgePairing_eq_neg_wedge]
  unfold p286GaugeExteriorPrincipalBilinear
    StageNineP286GaugeConnectionPointwiseEquation.p286GaugeExteriorDerivativeDirection
    StageNineFormNativeP286GaugeDerivativeIntegrationByParts.p286GaugeExteriorDerivativeDirection
  rfl

/-- The form-native topological W13 convention is the negative of the
historical metric/Hodge response convention used to classify the canonical
diagonal Hessian.  This local sign seam is a readout, not a new gate. -/
theorem
    p286HolonomicSecondJetConstitutiveAuxiliaryResponse_w13
    (jet : P286HolonomicConnectionSecondJet) :
    p286GaugeThreeFormWedgeLinearDual
        (pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (p286HolonomicSecondJetConstitutiveAuxiliaryResponse jet)) =
      -p286HolonomicSecondJetEulerLagrangeResponse jet := by
  apply LinearMap.ext
  intro direction
  rw [p286GaugeThreeFormWedgeLinearDual_apply,
    ← p286GaugeExteriorPrincipalSum_eq_w13]
  simp only [LinearMap.neg_apply,
    p286HolonomicSecondJetEulerLagrangeResponse_apply]
  unfold p286HolonomicSecondJetBFDivergenceResponseValue
  simp_rw [
    p286HolonomicSecondJetBFDivergenceResponseTerm_eq_neg_wedge_local]
  simp only [neg_neg, Finset.sum_neg_distrib]

private theorem
    fixedP506L0P286CanonicalJointCandidate_connectionExteriorAction_origin
    (write : P286GaugeOneForm) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate
          (fixedP506L0P286CanonicalJointCandidate write) 0)
        (holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0P286CanonicalJointCandidate write) 0) =
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate
          (fixedP506L0P286CanonicalJointCandidate 0) 0)
        (holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0P286CanonicalJointCandidate 0) 0) := by
  have auxiliaryCoordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0P286CanonicalJointCandidate write) 0 =
        holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0P286CanonicalJointCandidate 0) 0 := by
    funext pair
    exact congrArg p286CoordinateEquiv
      (congrFun
        (fixedP506L0P286CanonicalJointCandidate_auxiliary_origin write)
        pair)
  rw [fixedP506L0P286CanonicalJointCandidate_connection_origin,
    fixedP506L0P286CanonicalJointCandidate_connection_origin,
    auxiliaryCoordinateEquality]

private theorem fixedP506L0P286CanonicalJointCandidate_chargedThreeForm_origin
    (write : P286GaugeOneForm) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (fixedP506L0P286CanonicalJointCandidate write) 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (fixedP506L0P286CanonicalJointCandidate 0) 0) := by
  rw [fixedP506L0P286CanonicalJointCandidate_pointField_origin write]

private theorem fixedP506L0P286CanonicalJointCandidate_eulerThreeForm_affine
    (write : P286GaugeOneForm) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        (fixedP506L0P286CanonicalJointCandidate write) 0 =
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
          (fixedP506L0P286CanonicalJointCandidate 0) 0 +
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (p286HolonomicSecondJetConstitutiveAuxiliaryResponse
            (p286CanonicalDiagonalResponseSecondJet write)) := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    fixedP506L0P286CanonicalJointCandidate_exteriorDerivative_affine,
    fixedP506L0P286CanonicalJointCandidate_connectionExteriorAction_origin,
    fixedP506L0P286CanonicalJointCandidate_chargedThreeForm_origin]
  abel

/-! ## Complete fixed-origin action covector -/

/-- The complete W13 covector of the actual candidate at the fixed origin.
It is obtained directly from the mother-action Euler three-form. -/
def fixedP506L0P286CanonicalOriginActionDual
    (write : P286GaugeOneForm) : Module.Dual ℝ P286GaugeOneForm :=
  p286GaugeThreeFormWedgeLinearDual
    (holonomicFormNativeP286GaugeEulerThreeForm
      positiveSmoothUnifiedSource 0
      (fixedP506L0P286CanonicalJointCandidate write) 0)

theorem p286GaugeThreeFormWedgeLinearDual_add_local
    (first second : P286GaugeThreeForm) :
    p286GaugeThreeFormWedgeLinearDual (first + second) =
      p286GaugeThreeFormWedgeLinearDual first +
        p286GaugeThreeFormWedgeLinearDual second := by
  apply LinearMap.ext
  intro direction
  exact
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right direction first second

/-- Authoritative action forcing read before any new connection Hessian is
installed. -/
def fixedP506L0P286CanonicalOriginActionForcing :
    Module.Dual ℝ P286GaugeOneForm :=
  fixedP506L0P286CanonicalOriginActionDual 0

/-- Complete action-first affine law on the one fixed P506/L0 candidate
family.  The minus sign is forced by the already proved identity-coframe
metric/Hodge-to-topological-W13 convention seam. -/
theorem fixedP506L0P286CanonicalOriginActionDual_eq_affine
    (write : P286GaugeOneForm) :
    fixedP506L0P286CanonicalOriginActionDual write =
      fixedP506L0P286CanonicalOriginActionForcing -
        p286GaugeOneFormPairingEquiv write := by
  unfold fixedP506L0P286CanonicalOriginActionDual
    fixedP506L0P286CanonicalOriginActionForcing
  rw [fixedP506L0P286CanonicalJointCandidate_eulerThreeForm_affine,
    p286GaugeThreeFormWedgeLinearDual_add_local,
    p286HolonomicSecondJetConstitutiveAuxiliaryResponse_w13]
  have canonicalResponse :
      p286HolonomicSecondJetEulerLagrangeResponse
          (p286CanonicalDiagonalResponseSecondJet write) =
        p286GaugeOneFormPairingEquiv write := by
    apply LinearMap.ext
    intro direction
    rw [p286CanonicalDiagonalResponseSecondJet_response,
      p286GaugeOneFormPairingEquiv_apply]
  rw [canonicalResponse]
  rfl

/-- The unique no-parameter connection coordinate selected by the
nondegenerate action pairing once the affine law is established. -/
def fixedP506L0P286CanonicalGeneratedWrite : P286GaugeOneForm :=
  p286GaugeOneFormPairingEquiv.symm
    fixedP506L0P286CanonicalOriginActionForcing

/-- One common post-connection/post-constitutive actual generated from the
fixed action forcing. -/
def fixedP506L0P286CanonicalGeneratedActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalJointCandidate
    fixedP506L0P286CanonicalGeneratedWrite

@[simp] theorem fixedP506L0P286CanonicalGeneratedActual_gaugeConnection :
    fixedP506L0P286CanonicalGeneratedActual.gaugeConnection =
      (fixedP506L0P286CanonicalConnectionCandidate
        fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliary
    (point : BasePoint) :
    fixedP506L0P286CanonicalGeneratedActual.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0P286CanonicalActionInput.coframe point)
        (holonomicGaugeCurvature
          (fixedP506L0P286CanonicalConnectionCandidate
            fixedP506L0P286CanonicalGeneratedWrite) point) :=
  rfl

/-! ## Generated zero fiber and uniqueness -/

theorem fixedP506L0P286CanonicalGeneratedWrite_actionDual_zero :
    fixedP506L0P286CanonicalOriginActionDual
        fixedP506L0P286CanonicalGeneratedWrite = 0 := by
  rw [fixedP506L0P286CanonicalOriginActionDual_eq_affine]
  unfold fixedP506L0P286CanonicalGeneratedWrite
  rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
  exact sub_self _

theorem fixedP506L0P286CanonicalOriginActionDual_eq_zero_iff
    (write : P286GaugeOneForm) :
    fixedP506L0P286CanonicalOriginActionDual write = 0 ↔
      write = fixedP506L0P286CanonicalGeneratedWrite := by
  rw [fixedP506L0P286CanonicalOriginActionDual_eq_affine]
  constructor
  · intro actionZero
    have pairingEquality :
        p286GaugeOneFormPairingEquiv write =
          fixedP506L0P286CanonicalOriginActionForcing :=
      (sub_eq_zero.mp actionZero).symm
    apply p286GaugeOneFormPairingEquiv.injective
    unfold fixedP506L0P286CanonicalGeneratedWrite
    rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
    exact pairingEquality
  · intro writeEquality
    rw [writeEquality]
    unfold fixedP506L0P286CanonicalGeneratedWrite
    rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
    exact sub_self _

theorem fixedP506L0P286CanonicalGeneratedActual_eulerThreeForm_origin_zero :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        fixedP506L0P286CanonicalGeneratedActual 0 = 0 := by
  apply (p286GaugeThreeFormWedgeLinearDual_eq_zero_iff _).1
  exact fixedP506L0P286CanonicalGeneratedWrite_actionDual_zero

/-- The generated common actual closes the authoritative form-native P286
connection equation at the fixed origin. -/
theorem fixedP506L0P286CanonicalGeneratedActual_connectionEquation_origin :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        fixedP506L0P286CanonicalGeneratedActual 0 =
      formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          fixedP506L0P286CanonicalGeneratedActual 0) :=
  (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
    positiveSmoothUnifiedSource 0
    fixedP506L0P286CanonicalGeneratedActual 0).1
      fixedP506L0P286CanonicalGeneratedActual_eulerThreeForm_origin_zero

theorem fixedP506L0P286CanonicalGeneratedActual_coframe_origin :
    fixedP506L0P286CanonicalGeneratedActual.coframe 0 = 1 :=
  by
    change fixedP506L0P286CanonicalActionInput.coframe 0 = 1
    exact fixedP506L0P286CanonicalActionInput_coframe_origin

/-- The same generated actual also obeys the algebraic auxiliary equation at
the origin.  Only the fixed point's nondegeneracy is used. -/
theorem fixedP506L0P286CanonicalGeneratedActual_auxiliaryEquation_origin :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      FixedP506L0P286CanonicalBoundary
      (toContinuumPointField fixedP506L0P286CanonicalGeneratedActual 0) := by
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      FixedP506L0P286CanonicalBoundary
      (toContinuumPointField fixedP506L0P286CanonicalGeneratedActual 0)
      (by
        change
          Matrix.det
            (fixedP506L0P286CanonicalGeneratedActual.coframe 0) ≠ 0
        rw [fixedP506L0P286CanonicalGeneratedActual_coframe_origin]
        norm_num)).2
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
