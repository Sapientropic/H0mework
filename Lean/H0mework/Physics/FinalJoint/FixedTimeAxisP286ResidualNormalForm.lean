import H0mework.Physics.FinalJoint.FixedP286AffineIdentification
import H0mework.Physics.FinalJoint.FixedTimeAxisCoframe
import H0mework.Physics.DualVariation.ECConstraintSurfaceInitialLocalActualLift
import H0mework.Physics.MatterCurrent.P286CompleteResponseLocalActualLiftRegression

/-!
# Fixed P506/L0 final-common time-axis P286 residual normal form

The literal final-common actual is kept fixed at the selected P506/L0
occurrence.  This module computes its complete P286 auxiliary residual along
the canonical time axis from the already generated curvature, auxiliary and
coframe fields.  The result is a whole-channel action readout; no residual
coordinate, support choice or target field enters a producer.

The coframe block is also reduced to the exact action-generated lower-order
Einstein--Cartan rows.  This keeps the remaining live-Hodge calculation on
the same source/current lineage instead of replacing the actual by a free
constant-coefficient ansatz.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286ResidualNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLiftRegression

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private theorem fixedSource_blockwiseCoupling_same
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

private theorem fixedSource_blockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        form =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form := by
  have weakEq :
      ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  have hyperchargeEq :
      ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  rw [weakEq, hyperchargeEq,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum,
    liftGaugeTwoFormOperator_smul_operator_p286]
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  simp_rw [fixedSource_blockwiseCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

theorem finalCommon_p286AuxiliaryResidualCoordinate_timeAxis_eq_hodgeDefect
    (time : ℝ) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0FinalCommonActionActual 0)
        (canonicalCauchySlicePoint time 0) =
      fixedP506FormNativeJointActionSolvedP286CoframeHodgeDefectNormalForm
        (canonicalCauchySlicePoint time 0) := by
  rw [
    fixedP506L0FinalCommonActionActual_p286AuxiliaryResidualCoordinate_eq_solved,
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidual_eq_coframeHodgeDefect]

abbrev fixedP506L0ContactAccelerationRows : LorentzianCoframe :=
  sourceActionGeneratedIdentityECCoframeAccelerationRows
    positiveSmoothUnifiedSource (fixedCartanReactionContact 0)

abbrev fixedP506L0ContactLowerOrderRows : LorentzianCoframe :=
  sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    positiveSmoothUnifiedSource (fixedCartanReactionContact 0)

def fixedP506L0ContactSpatialAccelerationRowsNormalForm :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![-fixedP506L0ContactLowerOrderRows 1 1,
      -(fixedP506L0ContactLowerOrderRows 1 2 +
          fixedP506L0ContactLowerOrderRows 2 1) / 2,
      -(fixedP506L0ContactLowerOrderRows 1 3 +
          fixedP506L0ContactLowerOrderRows 3 1) / 2;
    -(fixedP506L0ContactLowerOrderRows 2 1 +
        fixedP506L0ContactLowerOrderRows 1 2) / 2,
      -fixedP506L0ContactLowerOrderRows 2 2,
      -(fixedP506L0ContactLowerOrderRows 2 3 +
          fixedP506L0ContactLowerOrderRows 3 2) / 2;
    -(fixedP506L0ContactLowerOrderRows 3 1 +
        fixedP506L0ContactLowerOrderRows 1 3) / 2,
      -(fixedP506L0ContactLowerOrderRows 3 2 +
          fixedP506L0ContactLowerOrderRows 2 3) / 2,
      -fixedP506L0ContactLowerOrderRows 3 3]

private theorem etaProjectedNegative_coordinate_normalForm
    (lowerOrder : LorentzianCoframe) (row column : LorentzianIndex) :
    (identityECEtaCompatibleProjection (-lowerOrder)).1 row column =
      -(lowerOrder row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            lowerOrder column row) / 2 := by
  change
    (1 / 2 : ℝ) *
        (-lowerOrder row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            (-lowerOrder column row)) = _
  ring

theorem fixedAccelerationRows_coordinate_normalForm
    (row column : LorentzianIndex) :
    fixedP506L0ContactAccelerationRows row column =
      -(fixedP506L0ContactLowerOrderRows row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            fixedP506L0ContactLowerOrderRows column row) / 2 := by
  exact etaProjectedNegative_coordinate_normalForm
    fixedP506L0ContactLowerOrderRows row column

theorem fixedAccelerationRows_spatial_normalForm :
    (fun internal column : Fin 3 =>
      fixedP506L0ContactAccelerationRows internal.succ column.succ) =
      fixedP506L0ContactSpatialAccelerationRowsNormalForm := by
  change
    (fun internal column : Fin 3 =>
      identityECEtaSymmetricPart (-fixedP506L0ContactLowerOrderRows)
        internal.succ column.succ) =
      fixedP506L0ContactSpatialAccelerationRowsNormalForm
  unfold fixedP506L0ContactSpatialAccelerationRowsNormalForm
  generalize fixedP506L0ContactLowerOrderRows = lowerOrder
  funext internal column
  fin_cases internal <;> fin_cases column <;>
    simp [identityECEtaSymmetricPart,
      identityECEtaAdjoint, minkowskiInternalSign] <;>
    ring

def fixedP506L0ContactTimeTimeSpatialHessianNormalForm :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![
    fixedP506L0ContactAccelerationRows 0 0 / 18 +
      fixedP506L0ContactAccelerationRows 1 1 / 18 -
      fixedP506L0ContactAccelerationRows 2 2 / 9 -
      fixedP506L0ContactAccelerationRows 3 3 / 9,
    (fixedP506L0ContactAccelerationRows 1 2 +
      fixedP506L0ContactAccelerationRows 2 1) / 12,
    (fixedP506L0ContactAccelerationRows 1 3 +
      fixedP506L0ContactAccelerationRows 3 1) / 12;
    (fixedP506L0ContactAccelerationRows 2 1 +
      fixedP506L0ContactAccelerationRows 1 2) / 12,
    fixedP506L0ContactAccelerationRows 0 0 / 18 +
      fixedP506L0ContactAccelerationRows 2 2 / 18 -
      fixedP506L0ContactAccelerationRows 1 1 / 9 -
      fixedP506L0ContactAccelerationRows 3 3 / 9,
    (fixedP506L0ContactAccelerationRows 2 3 +
      fixedP506L0ContactAccelerationRows 3 2) / 12;
    (fixedP506L0ContactAccelerationRows 3 1 +
      fixedP506L0ContactAccelerationRows 1 3) / 12,
    (fixedP506L0ContactAccelerationRows 3 2 +
      fixedP506L0ContactAccelerationRows 2 3) / 12,
    fixedP506L0ContactAccelerationRows 0 0 / 18 +
      fixedP506L0ContactAccelerationRows 3 3 / 18 -
      fixedP506L0ContactAccelerationRows 1 1 / 9 -
      fixedP506L0ContactAccelerationRows 2 2 / 9]

theorem fixedP506L0ContactCoframeHessian_timeTime_spatial_normalForm :
    (fun internal column : Fin 3 =>
      (fixedP506L0ContactCoframeHessian 0).1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal.succ column.succ) =
      fixedP506L0ContactTimeTimeSpatialHessianNormalForm := by
  change
    (fun internal column : Fin 3 =>
      (identityECHolonomicCoframeHessianSection
        fixedP506L0ContactAccelerationRows).1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal.succ column.succ) =
      fixedP506L0ContactTimeTimeSpatialHessianNormalForm
  funext internal column
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  fin_cases internal <;> fin_cases column <;>
    simp [identityECNormalCoframeHessianCoordinate,
      identityECNormalMetricHessianCoordinate,
      identityECWeylZeroRiemannCoordinate,
      identityECRicciTensorCoordinate,
      identityECEinsteinTensorCoordinate,
      identityECEinsteinTrace,
      identityECScalarCurvature,
      identityECMinkowskiMetricCoordinate,
      identityECEtaSymmetricPart,
      identityECEtaAdjoint,
      minkowskiInternalSign, canonicalLorentzianTimeDirection,
      fixedP506L0ContactTimeTimeSpatialHessianNormalForm,
      Fin.sum_univ_four] <;>
    ring

/-! ## Matching mother-action curvature defect -/

/-- At an identity contact, the live intrinsic-plus-non-gravity load is the
negative observation of the curvature section generated from that same
source/current stress.  The variance normalization is owned by the action
section; no historical raised-curvature convention is imported here. -/
theorem diracDualFormNativeIdentityECLoad_eq_neg_actionSectionObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeIdentityECLoad source current =
      -identityDiracDualECCurvatureObservation
        (identityDiracDualECConstraintActionSection
          (diracDualFormNativeECLiveNonGravityCoframeStress source current)) := by
  apply ContinuousLinearMap.ext
  intro variation
  have balance :=
    identityDiracDualECConstraintActionSection_balance_apply
      (diracDualFormNativeECLiveNonGravityCoframeStress source current)
      variation
  unfold diracDualFormNativeIdentityECLoad
    diracDualFormNativeECLiveNonGravityCoframeStress at balance ⊢
  unfold identityDiracDualECIntrinsicIIPlusObservation at balance
  simp only [add_apply, neg_apply] at balance ⊢
  linarith

abbrev fixedP506L0ContactLiveNonGravityCoframeStress :
    LorentzianCoframe →L[ℝ] ℝ :=
  diracDualFormNativeECLiveNonGravityCoframeStress
    positiveSmoothUnifiedSource (fixedCartanReactionContact 0)

abbrev fixedP506L0ContactActionCurvatureSection : PhysicalBivector :=
  identityDiracDualECConstraintActionSection
    fixedP506L0ContactLiveNonGravityCoframeStress

abbrev fixedP506L0ContactCurvatureActionDefectRows : LorentzianCoframe :=
  coframeCovectorCoordinates
    (identityDiracDualECCurvatureObservation
      (holonomicGravityCurvature (fixedCartanReactionContact 0) 0 -
        fixedP506L0ContactActionCurvatureSection))

/-- The Hessian input is exactly the observed difference between the actual
Cartan curvature and the curvature generated by the matching live action
section.  It is not a freely supplied matrix or an old-formulation stress. -/
theorem
    fixedP506L0ContactLowerOrderRows_eq_curvatureActionSectionDefect :
    fixedP506L0ContactLowerOrderRows =
      fixedP506L0ContactCurvatureActionDefectRows := by
  unfold fixedP506L0ContactLowerOrderRows
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    fixedP506L0ContactCurvatureActionDefectRows
  rw [identityDiracDualECCurvatureObservation_sub,
    diracDualFormNativeIdentityECLoad_eq_neg_actionSectionObservation]
  rfl

def fixedP506L0ContactCurvatureActionDefectTimeTimeSpatialHessian :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![-fixedP506L0ContactCurvatureActionDefectRows 0 0 / 18 -
        fixedP506L0ContactCurvatureActionDefectRows 1 1 / 18 +
        fixedP506L0ContactCurvatureActionDefectRows 2 2 / 9 +
        fixedP506L0ContactCurvatureActionDefectRows 3 3 / 9,
      -(fixedP506L0ContactCurvatureActionDefectRows 1 2 +
          fixedP506L0ContactCurvatureActionDefectRows 2 1) / 12,
      -(fixedP506L0ContactCurvatureActionDefectRows 1 3 +
          fixedP506L0ContactCurvatureActionDefectRows 3 1) / 12;
    -(fixedP506L0ContactCurvatureActionDefectRows 2 1 +
        fixedP506L0ContactCurvatureActionDefectRows 1 2) / 12,
      -fixedP506L0ContactCurvatureActionDefectRows 0 0 / 18 -
        fixedP506L0ContactCurvatureActionDefectRows 2 2 / 18 +
        fixedP506L0ContactCurvatureActionDefectRows 1 1 / 9 +
        fixedP506L0ContactCurvatureActionDefectRows 3 3 / 9,
      -(fixedP506L0ContactCurvatureActionDefectRows 2 3 +
          fixedP506L0ContactCurvatureActionDefectRows 3 2) / 12;
    -(fixedP506L0ContactCurvatureActionDefectRows 3 1 +
        fixedP506L0ContactCurvatureActionDefectRows 1 3) / 12,
      -(fixedP506L0ContactCurvatureActionDefectRows 3 2 +
          fixedP506L0ContactCurvatureActionDefectRows 2 3) / 12,
      -fixedP506L0ContactCurvatureActionDefectRows 0 0 / 18 -
        fixedP506L0ContactCurvatureActionDefectRows 3 3 / 18 +
        fixedP506L0ContactCurvatureActionDefectRows 1 1 / 9 +
        fixedP506L0ContactCurvatureActionDefectRows 2 2 / 9]

theorem
    fixedP506L0ContactCoframeHessian_timeTime_spatial_eq_curvatureActionDefect :
    (fun internal column : Fin 3 =>
      (fixedP506L0ContactCoframeHessian 0).1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal.succ column.succ) =
      fixedP506L0ContactCurvatureActionDefectTimeTimeSpatialHessian := by
  change
    (fun internal column : Fin 3 =>
      (identityECHolonomicCoframeHessianSection
        (sourceActionGeneratedIdentityECCoframeAccelerationRows
          positiveSmoothUnifiedSource (fixedCartanReactionContact 0))).1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal.succ column.succ) =
      fixedP506L0ContactCurvatureActionDefectTimeTimeSpatialHessian
  unfold sourceActionGeneratedIdentityECCoframeAccelerationRows
  rw [show
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource (fixedCartanReactionContact 0) =
      fixedP506L0ContactCurvatureActionDefectRows by
    exact
      fixedP506L0ContactLowerOrderRows_eq_curvatureActionSectionDefect]
  funext internal column
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  fin_cases internal <;> fin_cases column <;>
    simp [identityECNormalCoframeHessianCoordinate,
      identityECNormalMetricHessianCoordinate,
      identityECWeylZeroRiemannCoordinate,
      identityECRicciTensorCoordinate,
      identityECEinsteinTensorCoordinate,
      identityECEinsteinTrace,
      identityECScalarCurvature,
      identityECMinkowskiMetricCoordinate,
      identityECEtaSymmetricPart,
      identityECEtaCompatibleProjection,
      identityECEtaAdjoint,
      minkowskiInternalSign, canonicalLorentzianTimeDirection,
      fixedP506L0ContactCurvatureActionDefectTimeTimeSpatialHessian,
      Fin.sum_univ_four] <;>
    ring

/-- The literal final-common time-axis coframe is identity plus the quadratic
realization of the matching curvature/action-section defect. -/
theorem
    fixedP506L0FinalCommonTimeAxisSpatialCoframe_eq_curvatureActionDefect
    (time : ℝ) :
    fixedP506L0FinalCommonTimeAxisSpatialCoframe 0 time =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) +
        (time ^ 2 / 2) •
          fixedP506L0ContactCurvatureActionDefectTimeTimeSpatialHessian := by
  ext internal column
  rw [fixedP506L0FinalCommonTimeAxisSpatialCoframe_normalForm]
  have hessianCoordinate := congrFun
    (congrFun
      fixedP506L0ContactCoframeHessian_timeTime_spatial_eq_curvatureActionDefect
      internal) column
  rw [hessianCoordinate]
  rfl

theorem c3h181FullCurvatureCoordinateNormalForm_negative_timeAxis
    (time : ℝ) :
    c3h181FullCurvatureCoordinateNormalForm
        (-canonicalCauchySlicePoint time 0) =
      ![(c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0,
        (c3h181StrongCouplingSquared * time) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0, 0] := by
  funext pair
  fin_cases pair <;>
    simp [c3h181FullCurvatureCoordinateNormalForm,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem c3h181FullAuxiliaryCoordinateNormalForm_negative_timeAxis
    (time : ℝ) :
    c3h181FullAuxiliaryCoordinateNormalForm
        (-canonicalCauchySlicePoint time 0) =
      ![0, 0, 0,
        (1 / 3 : ℝ) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0,
        time • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge] := by
  funext pair
  fin_cases pair <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem finalCommon_p286AuxiliaryResidualCoordinate_timeAxis_normalForm
    (time : ℝ) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0FinalCommonActionActual 0)
        (canonicalCauchySlicePoint time 0) =
      ![(c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0,
        (c3h181StrongCouplingSquared * time) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0, 0] -
      formNativeP286CoordinateBlockwiseConstitutive
        ((fixedP506L0FinalCommonActionActual 0).coframe
          (canonicalCauchySlicePoint time 0))
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        ![0, 0, 0,
          (1 / 3 : ℝ) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
          0,
          time • positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge] := by
  rw [
    fixedP506L0FinalCommonActionActual_p286AuxiliaryResidualCoordinate_eq_solved]
  unfold
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
  rw [
    ← congrFun fixedP506L0FinalCommonActionActual_coframe_eq_solved
      (canonicalCauchySlicePoint time 0),
    c3h181FullCurvatureCoordinateNormalForm_negative_timeAxis,
    c3h181FullAuxiliaryCoordinateNormalForm_negative_timeAxis]

theorem finalCommon_p286AuxiliaryResidualCoordinate_timeOne_pairZero_reduction :
    (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (fixedP506L0FinalCommonActionActual 0)
      (canonicalCauchySlicePoint 1 0)) 0 =
      (c3h181StrongCouplingSquared / 3) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge -
        liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear
              ((fixedP506L0FinalCommonActionActual 0).coframe
                (canonicalCauchySlicePoint 1 0)))
          ![0, 0, 0,
            (1 / 3 : ℝ) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
            0,
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge] 0 := by
  have whole := congrFun
    (finalCommon_p286AuxiliaryResidualCoordinate_timeAxis_normalForm 1) 0
  rw [fixedSource_blockwiseConstitutive_eq_unified] at whole
  simpa only [Pi.sub_apply, Matrix.cons_val_zero, one_smul, mul_one] using whole

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286ResidualNormalForm
