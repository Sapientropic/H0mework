import H0mework.Physics.Geometry.BiradialScalarOriginResponse
import H0mework.Physics.Geometry.CanonicalTimePrimitiveSegmentRegularity
import H0mework.Physics.TimePrimitive.DiagonalHessian
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorZeroSliceReduction
import H0mework.Physics.DualVariation.ScalarEulerLocalLinearity

/-!
# Scalar readback of the Lorentz-path action-selected joint successor

The fixed P506/L0 action-selected occurrence generates one scalar acceleration
profile from the scalar Euler covector of the same momentum-carry current.  Its
canonical time second primitive is then installed by the already authoritative
coupled temporal writer.  This module identifies that profile with the full
real action covector and computes the resulting diagonal Hessian on the whole
canonical zero slice.

No residual coordinate, support branch, target jet, zero-fiber receipt, or
completion payload enters the writer.  The final zero read is therefore
producer soundness of the existing source/current-only temporal action leg.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorScalarReadback

open ProofFreeRicherAnholonomicSource
open StageNineBiradialCoframeResponse
open StageNineBiradialScalarOriginResponse
open StageNineCanonicalCauchyState
open StageNineCanonicalTimePrimitiveSegmentRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveDiagonalHessian
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorZeroSliceReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeScalarEulerLocalLinearity
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance scalarReadbackP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance scalarReadbackP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance scalarReadbackP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance scalarReadbackP286CoordinateNormedAddCommGroup :
    NormedAddCommGroup P286CoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : P286CoordinateIndex => ℝ)

local instance scalarReadbackP286CoordinateNormedSpace :
    NormedSpace ℝ P286CoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : P286CoordinateIndex => ℝ)

local instance scalarReadbackBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance scalarReadbackBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

local instance scalarReadbackCoframeNormedAddCommGroup :
    NormedAddCommGroup LorentzianCoframe :=
  inferInstanceAs (NormedAddCommGroup (Fin 4 → Fin 4 → ℝ))

local instance scalarReadbackCoframeNormedSpace :
    NormedSpace ℝ LorentzianCoframe :=
  inferInstanceAs (NormedSpace ℝ (Fin 4 → Fin 4 → ℝ))

local instance scalarReadbackCoordinateNormedAddCommGroup :
    NormedAddCommGroup ScalarCoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : ScalarBasisIndex => ℂ)

local instance scalarReadbackCoordinateNormedSpace :
    NormedSpace ℝ ScalarCoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : ScalarBasisIndex => ℂ)

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

private abbrev Profile : BasePoint → ScalarCoordinateCarrier :=
  completeJointScalarAccelerationProfile Source Carry

private abbrev Primitive : BasePoint → ScalarCoordinateCarrier :=
  canonicalTimeSecondPrimitive Profile

private theorem carry_coframe_nondegenerate (point : BasePoint) :
    Matrix.det (Carry.coframe point) ≠ 0 := by
  rw [actionSelectedCarry_coframe_eq_one]
  norm_num

private theorem carry_coframe_contDiffAt (point : BasePoint) :
    ContDiffAt ℝ ∞ Carry.coframe point := by
  rw [actionSelectedCarry_coframe_eq_one]
  exact contDiffAt_const

private theorem profile_contDiff : ContDiff ℝ ∞ Profile := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact completeJointScalarAccelerationProfile_contDiffAt_of_local
    Source Carry point (carry_coframe_nondegenerate point)
    (carry_coframe_contDiffAt point)
    actionSelectedCarry_scalar_contDiff.contDiffAt
    actionSelectedCarry_matterCoordinates_contDiff.contDiffAt
    actionSelectedCarry_conjugateMatterCoordinates_contDiff.contDiffAt
    (fun direction =>
      (actionSelectedCarry_gaugeConnectionCoordinate_contDiff
        direction).contDiffAt)

private def carryScalarEulerDualAt
    (point : BasePoint) : Module.Dual ℝ ScalarCoordinateCarrier where
  toFun := fun direction =>
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Carry direction
      point
  map_add' := by
    intro first second
    exact diracDualScalarEulerLagrangeDirectionalCoefficient_add_of_local
      Source Carry point (carry_coframe_nondegenerate point)
      (carry_coframe_contDiffAt point)
      actionSelectedCarry_scalar_contDiff.contDiffAt
      (fun direction =>
        (actionSelectedCarry_gaugeConnectionCoordinate_contDiff
          direction).contDiffAt)
      first second
  map_smul' := by
    intro parameter direction
    simpa only [RingHom.id_apply, smul_eq_mul] using
      diracDualScalarEulerLagrangeDirectionalCoefficient_real_smul_of_local
        Source Carry point (carry_coframe_nondegenerate point)
        (carry_coframe_contDiffAt point)
        actionSelectedCarry_scalar_contDiff.contDiffAt
        (fun formDirection =>
          (actionSelectedCarry_gaugeConnectionCoordinate_contDiff
            formDirection).contDiffAt)
        parameter direction

/-- At every spacetime occurrence, the generated scalar acceleration profile
is exactly the negative real Riesz coordinate of the same `Carry` scalar
Euler covector. -/
theorem actionSelectedCarry_scalarAccelerationProfile_eq_neg_actionDual
    (point : BasePoint) :
    Profile point = -scalarActionRealDual (carryScalarEulerDualAt point) := by
  unfold Profile completeJointScalarAccelerationProfile
  change
    genericDiracDualScalarGeneratedAcceleration Source
        (completeJointRepairedConstitutiveCurrent Source
          (completeJointGeneratedProfileRestartCurrent Source Carry point)) =
      -scalarActionRealDual (carryScalarEulerDualAt point)
  unfold genericDiracDualScalarGeneratedAcceleration scalarActionRealDual
  congr 1
  apply PiLp.ext
  intro index
  change
    ((genericDiracDualScalarTemporalDemandDual Source
          (completeJointRepairedConstitutiveCurrent Source
            (completeJointGeneratedProfileRestartCurrent Source Carry point))
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarTemporalDemandDual Source
          (completeJointRepairedConstitutiveCurrent Source
            (completeJointGeneratedProfileRestartCurrent Source Carry point))
          (scalarImaginaryBasis index) : ℂ) * Complex.I) =
    (((carryScalarEulerDualAt point) (scalarRealBasis index) : ℂ) +
      ((carryScalarEulerDualAt point) (scalarImaginaryBasis index) : ℂ) *
        Complex.I)
  rw [genericDiracDualScalarTemporalDemandDual_realBasis,
    genericDiracDualScalarTemporalDemandDual_imaginaryBasis,
    completeJointScalarRawTemporalDemand_eq_currentScalarEuler,
    completeJointScalarRawTemporalDemand_eq_currentScalarEuler]
  rfl

/-- Pointwise action law for the fixed scalar momentum carry.  The profile is
generated from the complete scalar Euler covector, not merely its basis
coordinates. -/
theorem actionSelectedCarry_scalarEuler_eq_neg_profilePairing
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Carry direction
        point =
      -scalarCoordinatePairingRe direction (Profile point) := by
  rw [actionSelectedCarry_scalarAccelerationProfile_eq_neg_actionDual]
  rw [show
      scalarCoordinatePairingRe direction
          (-scalarActionRealDual (carryScalarEulerDualAt point)) =
        -scalarCoordinatePairingRe direction
          (scalarActionRealDual (carryScalarEulerDualAt point)) by
    change
      scalarCoordinatePairingReBilinear direction
          (-scalarActionRealDual (carryScalarEulerDualAt point)) =
        -scalarCoordinatePairingReBilinear direction
          (scalarActionRealDual (carryScalarEulerDualAt point))
    exact map_neg
      (scalarCoordinatePairingReBilinear direction)
      (scalarActionRealDual (carryScalarEulerDualAt point))]
  rw [neg_neg, scalarCoordinatePairingRe_actionRealDual]
  rfl

/-! ## Exact zero-slice scalar second jet -/

private theorem primitive_contDiff_two : ContDiff ℝ 2 Primitive :=
  canonicalTimeSecondPrimitive_contDiff_two_of_contDiff Profile profile_contDiff

private theorem primitive_contDiff : ContDiff ℝ ∞ Primitive := by
  rw [contDiff_infty]
  intro order
  rw [contDiff_iff_contDiffAt]
  intro point
  apply canonicalTimeSecondPrimitive_contDiffAt_of_contDiffOn_segment_finite
    order Profile Set.univ isOpen_univ
  · exact (profile_contDiff.of_le
      (show ((((order + 2 : ℕ) : ℕ∞)) : ℕ∞ω) ≤
          ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)).contDiffOn
  · simp

/-- The explicit coupled scalar whole field is globally `C²`: its supplied
carry is smooth and its action-generated second primitive is `C²`. -/
theorem actionSelectedCoupled_scalar_contDiff_two :
    ContDiff ℝ 2
      (completeJointActionSelectedCoupledTemporalActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual).scalar := by
  change ContDiff ℝ 2 (fun point => Carry.scalar point + Primitive point)
  exact (actionSelectedCarry_scalar_contDiff.of_le
      (show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)).add
    primitive_contDiff_two

/-- The fixed action-selected coupled scalar is globally smooth.  This is
the direct finite-order exhaustion of its smooth source-generated profile,
not a regularity premise supplied to the temporal writer. -/
theorem actionSelectedCoupled_scalar_contDiff :
    ContDiff ℝ ∞
      (completeJointActionSelectedCoupledTemporalActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual).scalar := by
  change ContDiff ℝ ∞ (fun point => Carry.scalar point + Primitive point)
  exact actionSelectedCarry_scalar_contDiff.add primitive_contDiff

private theorem carry_scalar_differentiableAt (point : BasePoint) :
    DifferentiableAt ℝ Carry.scalar point :=
  (actionSelectedCarry_scalar_contDiff.differentiable (by simp)).differentiableAt

private theorem primitive_differentiableAt (point : BasePoint) :
    DifferentiableAt ℝ Primitive point :=
  (primitive_contDiff_two.differentiable (by norm_num)).differentiableAt

private theorem coupled_scalar_differentiableAt (point : BasePoint) :
    DifferentiableAt ℝ Coupled.scalar point := by
  change DifferentiableAt ℝ
    (fun candidate => Carry.scalar candidate + Primitive candidate) point
  exact (carry_scalar_differentiableAt point).add
    (primitive_differentiableAt point)

/-- The explicit action-selected coupled scalar is differentiable at every
spacetime occurrence.  This is a regularity readout of the already generated
carry plus canonical second primitive, not a premise of either writer. -/
theorem actionSelectedCoupled_scalar_differentiableAt
    (point : BasePoint) :
    DifferentiableAt ℝ
      (completeJointActionSelectedCoupledTemporalActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual).scalar
      point := by
  simpa [Source, Current, Carry, Coupled] using
    coupled_scalar_differentiableAt point

private theorem primitive_value_zeroSlice (space : StageNineSpatialPoint) :
    Primitive (canonicalCauchySlicePoint 0 space) = 0 :=
  canonicalTimeSecondPrimitive_zeroSlice Profile space

private theorem primitive_directionalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative Primitive
        (canonicalCauchySlicePoint 0 space) direction = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have firstJet :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
      Source Carry space (carry_scalar_differentiableAt point)
      (coupled_scalar_differentiableAt point) direction
  unfold fieldDirectionalDerivative at firstJet ⊢
  change
    (fderiv ℝ (fun candidate =>
      Carry.scalar candidate + Primitive candidate) point)
        (coordinateDirection direction) =
      (fderiv ℝ Carry.scalar point) (coordinateDirection direction)
    at firstJet
  rw [fderiv_fun_add (carry_scalar_differentiableAt point)
    (primitive_differentiableAt point), add_apply] at firstJet
  exact (add_eq_left.mp firstJet)

private def carryGaugeCoordinate
    (formDirection : LorentzianIndex) : BasePoint → P286CoordinateCarrier :=
  fun point => p286CoordinateEquiv (Carry.gaugeConnection point formDirection)

private def scalarPrimitiveGaugeAction
    (formDirection : LorentzianIndex) : BasePoint → ScalarCoordinateCarrier :=
  fun point =>
    scalarP286ActionBilinear (carryGaugeCoordinate formDirection point)
      (Primitive point)

private theorem scalarPrimitiveGaugeAction_differentiableAt
    (point : BasePoint)
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ (scalarPrimitiveGaugeAction formDirection) point := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  exact (action.hasFDerivAt_of_bilinear
    ((actionSelectedCarry_gaugeConnectionCoordinate_contDiff formDirection
      ).differentiable (by simp) |>.differentiableAt |>.hasFDerivAt)
    (primitive_differentiableAt point).hasFDerivAt).differentiableAt

private theorem scalarPrimitiveGaugeAction_diagonalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (scalarPrimitiveGaugeAction direction)
        (canonicalCauchySlicePoint 0 space) direction = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  have gaugeDifferentiable : DifferentiableAt ℝ
      (carryGaugeCoordinate direction) point :=
    (actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction
      ).differentiable (by simp) |>.differentiableAt
  have primitiveDifferentiable : DifferentiableAt ℝ Primitive point :=
    primitive_differentiableAt point
  have totalDerivative :
      fderiv ℝ (scalarPrimitiveGaugeAction direction) point =
        action.precompR BasePoint (carryGaugeCoordinate direction point)
            (fderiv ℝ Primitive point) +
          action.precompL BasePoint
            (fderiv ℝ (carryGaugeCoordinate direction) point)
            (Primitive point) := by
    exact (action.hasFDerivAt_of_bilinear
      gaugeDifferentiable.hasFDerivAt
      primitiveDifferentiable.hasFDerivAt).fderiv
  unfold fieldDirectionalDerivative
  rw [totalDerivative]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply]
  change
    scalarP286ActionBilinear (carryGaugeCoordinate direction point)
        (fieldDirectionalDerivative Primitive point direction) +
      scalarP286ActionBilinear
          (fieldDirectionalDerivative (carryGaugeCoordinate direction)
            point direction)
          (Primitive point) = 0
  rw [primitive_directionalDerivative_zeroSlice space direction,
    primitive_value_zeroSlice space]
  simp

private def scalarCovariantIncrement
    (point : BasePoint)
    (formDirection : LorentzianIndex) : ScalarCoordinateCarrier :=
  fieldDirectionalDerivative Primitive point formDirection +
    scalarPrimitiveGaugeAction formDirection point

private theorem scalarCovariantIncrement_differentiableAt
    (point : BasePoint)
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate => scalarCovariantIncrement candidate formDirection)
      point := by
  have firstJetRegular : ContDiff ℝ 1 fun candidate =>
      fieldDirectionalDerivative Primitive candidate formDirection := by
    unfold fieldDirectionalDerivative
    exact ((primitive_contDiff_two.fderiv_right (m := 1) (by norm_num)
      ).clm_apply contDiff_const)
  exact
    ((firstJetRegular.differentiable (by norm_num)).differentiableAt).add
      (scalarPrimitiveGaugeAction_differentiableAt point formDirection)

private theorem scalarCovariantIncrement_diagonalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => scalarCovariantIncrement candidate direction)
        (canonicalCauchySlicePoint 0 space) direction =
      if direction = canonicalLorentzianTimeDirection then
        Profile (canonicalCauchySlicePoint 0 space)
      else 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have firstJetRegular : ContDiff ℝ 1 fun candidate =>
      fieldDirectionalDerivative Primitive candidate direction := by
    unfold fieldDirectionalDerivative
    exact ((primitive_contDiff_two.fderiv_right (m := 1) (by norm_num)
      ).clm_apply contDiff_const)
  unfold scalarCovariantIncrement
  change
    (fderiv ℝ
        (fun candidate =>
          fieldDirectionalDerivative Primitive candidate direction +
            scalarPrimitiveGaugeAction direction candidate)
        point) (coordinateDirection direction) = _
  rw [fderiv_fun_add
    ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
    (scalarPrimitiveGaugeAction_differentiableAt point direction), add_apply]
  change
    fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative Primitive candidate direction)
        point direction +
      fieldDirectionalDerivative (scalarPrimitiveGaugeAction direction)
        point direction = _
  rw [canonicalTimeSecondPrimitive_diagonalSecondDerivative_zeroSlice_of_contDiff
      Profile profile_contDiff space direction,
    scalarPrimitiveGaugeAction_diagonalDerivative_zeroSlice space direction,
    add_zero]

private theorem coupled_scalarCovariantDerivative_eq_carry_add_increment
    (point : BasePoint)
    (formDirection : LorentzianIndex) :
    holonomicScalarCovariantDerivative Coupled point formDirection =
      holonomicScalarCovariantDerivative Carry point formDirection +
        scalarCovariantIncrement point formDirection := by
  unfold holonomicScalarCovariantDerivative scalarCovariantIncrement
    scalarPrimitiveGaugeAction carryGaugeCoordinate
  change
    fieldDirectionalDerivative
        (fun candidate => Carry.scalar candidate + Primitive candidate)
        point formDirection +
      scalarMotherLieAction
          (p286LieBlockEmbed (Carry.gaugeConnection point formDirection))
          (Carry.scalar point + Primitive point) = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add (carry_scalar_differentiableAt point)
    (primitive_differentiableAt point), add_apply,
    scalarMotherLieAction_add_right]
  have actionEq :
      scalarP286ActionBilinear
          (p286CoordinateEquiv (Carry.gaugeConnection point formDirection))
          (Primitive point) =
        scalarMotherLieAction
          (p286LieBlockEmbed (Carry.gaugeConnection point formDirection))
          (Primitive point) := by
    change
      scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (Carry.gaugeConnection point formDirection))))
          (Primitive point) = _
    rw [p286CoordinateEquiv.symm_apply_apply]
  rw [actionEq]
  abel

private theorem carry_scalarCovariantDerivative_differentiableAt
    (point : BasePoint)
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate =>
        holonomicScalarCovariantDerivative Carry candidate formDirection)
      point :=
  (scalarCovariantDerivative_contDiffAt_of_local Carry point
    actionSelectedCarry_scalar_contDiff.contDiffAt
    (fun direction =>
      (actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction
        ).contDiffAt)
    formDirection).differentiableAt (by simp)

private theorem coupled_scalarCovariantDerivative_differentiableAt
    (point : BasePoint)
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate =>
        holonomicScalarCovariantDerivative Coupled candidate formDirection)
      point := by
  rw [show
      (fun candidate =>
        holonomicScalarCovariantDerivative Coupled candidate formDirection) =
        fun candidate =>
          holonomicScalarCovariantDerivative Carry candidate formDirection +
            scalarCovariantIncrement candidate formDirection by
    funext candidate
    exact coupled_scalarCovariantDerivative_eq_carry_add_increment
      candidate formDirection]
  exact (carry_scalarCovariantDerivative_differentiableAt point formDirection).add
    (scalarCovariantIncrement_differentiableAt point formDirection)

private theorem coupled_scalarCovariantDiagonalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          holonomicScalarCovariantDerivative Coupled candidate direction)
        (canonicalCauchySlicePoint 0 space) direction =
      fieldDirectionalDerivative
          (fun candidate =>
            holonomicScalarCovariantDerivative Carry candidate direction)
          (canonicalCauchySlicePoint 0 space) direction +
        if direction = canonicalLorentzianTimeDirection then
          Profile (canonicalCauchySlicePoint 0 space)
        else 0 := by
  let point := canonicalCauchySlicePoint 0 space
  rw [show
      (fun candidate =>
        holonomicScalarCovariantDerivative Coupled candidate direction) =
        fun candidate =>
          holonomicScalarCovariantDerivative Carry candidate direction +
            scalarCovariantIncrement candidate direction by
    funext candidate
    exact coupled_scalarCovariantDerivative_eq_carry_add_increment
      candidate direction]
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (carry_scalarCovariantDerivative_differentiableAt point direction)
    (scalarCovariantIncrement_differentiableAt point direction), add_apply]
  change
    fieldDirectionalDerivative
        (fun candidate =>
          holonomicScalarCovariantDerivative Carry candidate direction)
        point direction +
      fieldDirectionalDerivative
        (fun candidate => scalarCovariantIncrement candidate direction)
        point direction = _
  rw [scalarCovariantIncrement_diagonalDerivative_zeroSlice space direction]
  simp [point, fieldDirectionalDerivative]

/-! ## Momentum divergence and coupled scalar Euler closure -/

private theorem scalarCoordinatePairingRe_comm_local
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem carry_coframe_eq_biradial :
    Carry.coframe = fun _ => biradialCoframe 1 1 := by
  rw [actionSelectedCarry_coframe_eq_one]
  funext point
  exact biradialCoframe_one_one.symm

private theorem coupled_coframe_eq_biradial :
    Coupled.coframe = fun _ => biradialCoframe 1 1 := by
  exact
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
      Source Carry).trans carry_coframe_eq_biradial

private theorem coupled_scalarMomentum_diagonalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum Source Coupled direction
          derivativeDirection)
        (canonicalCauchySlicePoint 0 space) derivativeDirection =
      fieldDirectionalDerivative
          (scalarDifferentialMomentum Source Carry direction
            derivativeDirection)
          (canonicalCauchySlicePoint 0 space) derivativeDirection +
        if derivativeDirection = canonicalLorentzianTimeDirection then
          -scalarCoordinatePairingRe direction
            (Profile (canonicalCauchySlicePoint 0 space))
        else 0 := by
  let point := canonicalCauchySlicePoint 0 space
  rw [scalarDifferentialMomentum_eq_biradialNormalForm Source Coupled
      (a := 1) (b := 1) (by positivity) (by positivity)
      coupled_coframe_eq_biradial direction derivativeDirection,
    scalarDifferentialMomentum_eq_biradialNormalForm Source Carry
      (a := 1) (b := 1) (by positivity) (by positivity)
      carry_coframe_eq_biradial direction derivativeDirection]
  rw [biradialScalarDifferentialMomentumNormalForm_diagonalDerivative
      1 1 (holonomicScalarCovariantDerivative Coupled) point
      (fun formDirection =>
        coupled_scalarCovariantDerivative_differentiableAt point formDirection)
      direction derivativeDirection,
    biradialScalarDifferentialMomentumNormalForm_diagonalDerivative
      1 1 (holonomicScalarCovariantDerivative Carry) point
      (fun formDirection =>
        carry_scalarCovariantDerivative_differentiableAt point formDirection)
      direction derivativeDirection,
    coupled_scalarCovariantDiagonalDerivative_zeroSlice space
      derivativeDirection]
  fin_cases derivativeDirection <;>
    simp [point, biradialScalarMomentumWeight,
      canonicalLorentzianTimeDirection,
      scalarCoordinatePairingRe_add_right,
      scalarCoordinatePairingRe_comm_local];
    ring

private theorem coupled_scalarMomentumDivergence_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source Coupled direction
        (canonicalCauchySlicePoint 0 space) =
      scalarDifferentialMomentumDivergence Source Carry direction
          (canonicalCauchySlicePoint 0 space) -
        scalarCoordinatePairingRe direction
          (Profile (canonicalCauchySlicePoint 0 space)) := by
  unfold scalarDifferentialMomentumDivergence
  rw [Fin.sum_univ_four,
    coupled_scalarMomentum_diagonalDerivative_zeroSlice space direction 0,
    coupled_scalarMomentum_diagonalDerivative_zeroSlice space direction 1,
    coupled_scalarMomentum_diagonalDerivative_zeroSlice space direction 2,
    coupled_scalarMomentum_diagonalDerivative_zeroSlice space direction 3]
  simp [canonicalLorentzianTimeDirection, Fin.sum_univ_four]
  ring

private theorem coupled_scalarAlgebraic_zeroSlice_eq_carry
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient Source Coupled direction
        (canonicalCauchySlicePoint 0 space) =
      diracDualScalarAlgebraicDirectionalCoefficient Source Carry direction
        (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeEq : Coupled.coframe point = Carry.coframe point :=
    congrFun
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
        Source Carry) point
  have gaugeConnectionEq :
      Coupled.gaugeConnection point = Carry.gaugeConnection point := by
    rfl
  have scalarEq : Coupled.scalar point = Carry.scalar point := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source Carry).scalar point = Carry.scalar point
    simpa only [point] using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        Source Carry space
  have matterEq : Coupled.matter point = Carry.matter point := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source Carry).matter point = Carry.matter point
    simpa only [point] using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        Source Carry space
  have conjugateMatterEq :
      Coupled.conjugateMatter point = Carry.conjugateMatter point := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source Carry).conjugateMatter point = Carry.conjugateMatter point
    simpa only [point] using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        Source Carry space
  have scalarCovariantEq :
      holonomicScalarCovariantDerivative Coupled point =
        holonomicScalarCovariantDerivative Carry point := by
    simpa [point] using coupled_scalarCovariantDerivative_zeroSlice_eq_carry
      space
  have variationEq :
      holonomicScalarVariationAlgebraicDirection Coupled direction point =
        holonomicScalarVariationAlgebraicDirection Carry direction point := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [gaugeConnectionEq]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coframeEq, scalarEq, scalarCovariantEq, matterEq,
    conjugateMatterEq, variationEq]

/-- The existing coupled temporal action producer settles its scalar Euler
read on every point of the canonical zero slice. -/
theorem actionSelectedCoupled_scalarEuler_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Coupled direction
        (canonicalCauchySlicePoint 0 space) = 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [coupled_scalarAlgebraic_zeroSlice_eq_carry space direction,
    coupled_scalarMomentumDivergence_zeroSlice space direction]
  have actionLaw :=
    actionSelectedCarry_scalarEuler_eq_neg_profilePairing direction
      (canonicalCauchySlicePoint 0 space)
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient at actionLaw
  linarith

/-! ## Five-leg suffix custody and final successor readback -/

private theorem successor_coframe_eq_coupled :
    Successor.coframe = Coupled.coframe := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Coupled).coframe = Coupled.coframe
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source Coupled

private theorem successor_gaugeConnection_eq_coupled :
    Successor.gaugeConnection = Coupled.gaugeConnection := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Coupled).gaugeConnection = Coupled.gaugeConnection
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection
      Source Coupled

private theorem successor_scalar_eq_coupled :
    Successor.scalar = Coupled.scalar := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Coupled).scalar = Coupled.scalar
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source Coupled

private theorem successor_matter_eq_coupled :
    Successor.matter = Coupled.matter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Coupled).matter = Coupled.matter
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
      Source Coupled

private theorem successor_conjugateMatter_eq_coupled :
    Successor.conjugateMatter = Coupled.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Coupled).conjugateMatter = Coupled.conjugateMatter
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
      Source Coupled

private theorem successor_scalarCovariantDerivative_eq_coupled :
    holonomicScalarCovariantDerivative Successor =
      holonomicScalarCovariantDerivative Coupled := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [successor_scalar_eq_coupled, successor_gaugeConnection_eq_coupled]

private theorem successor_scalarDifferentialMomentum_eq_coupled
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source Successor direction
        derivativeDirection =
      scalarDifferentialMomentum Source Coupled direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [successor_coframe_eq_coupled,
    successor_scalarCovariantDerivative_eq_coupled]

private theorem successor_scalarMomentumDivergence_eq_coupled
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source Successor direction =
      scalarDifferentialMomentumDivergence Source Coupled direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [successor_scalarDifferentialMomentum_eq_coupled direction]

private theorem successor_scalarAlgebraic_eq_coupled
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarAlgebraicDirectionalCoefficient Source Successor direction
        point =
      diracDualScalarAlgebraicDirectionalCoefficient Source Coupled direction
        point := by
  have variationEq :
      holonomicScalarVariationAlgebraicDirection Successor direction point =
        holonomicScalarVariationAlgebraicDirection Coupled direction point := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [successor_gaugeConnection_eq_coupled]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [successor_coframe_eq_coupled, successor_scalar_eq_coupled,
    successor_scalarCovariantDerivative_eq_coupled,
    successor_matter_eq_coupled, successor_conjugateMatter_eq_coupled,
    variationEq]

private theorem successor_scalarEuler_eq_coupled
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Successor
        direction point =
      diracDualScalarEulerLagrangeDirectionalCoefficient Source Coupled
        direction point := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [successor_scalarAlgebraic_eq_coupled,
    congrFun (successor_scalarMomentumDivergence_eq_coupled direction) point]

/-- The scalar projection of the one action-selected common successor's
joint residual vanishes on the entire canonical zero slice. -/
theorem successor_scalarResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Successor
      (canonicalCauchySlicePoint 0 space)).scalar = 0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Successor
        direction (canonicalCauchySlicePoint 0 space) = 0
  rw [successor_scalarEuler_eq_coupled]
  exact actionSelectedCoupled_scalarEuler_zeroSlice space direction

/-- After the temporal action law is read back, the same-successor zero-fiber
gate no longer contains a scalar premise.  The complete P286 three-form was
already closed by the action-selected radial/constitutive write, so gravity
and coframe are the two remaining exact projections of this occurrence. -/
theorem
    successor_zeroSlice_residual_eq_zero_iff_remainingGravityCoframeRelations
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual Source Successor
        (canonicalCauchySlicePoint 0 space) = 0 ↔
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
            (completeJointActionSelectedCoupledTemporalActual Source Current))
          (canonicalCauchySlicePoint 0 space) =
        sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget Source
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
            Source
            (fullyRecenterHolonomicConfiguration
              (completeJointActionSelectedCoupledTemporalActual Source Current)
              (canonicalCauchySlicePoint 0 space))) ∧
      (diracDualFormNativePointwiseJointResidual Source Successor
        (canonicalCauchySlicePoint 0 space)).coframe = 0 := by
  rw [successor_zeroSlice_residual_eq_zero_iff_remainingActionRelations]
  simp only [successor_scalarResidual_zeroSlice, true_and]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorScalarReadback
