import H0mework.Physics.CartanAction.CartanPointCoframeRegularity
import H0mework.Physics.IdentityHessian.CartanECNormalFixedMatterJointRegularity

/-!
# Fixed P506/L0 joint Cartan regularity

This module computes the KIN-6 Cartan response only for the fixed P506/L0
whole-slice current.  The primitive coframe is literally one, so both Cartan
inverse maps are fixed finite-dimensional linear equivalences; no generic
coframe atlas or arbitrary-current regularity receipt is introduced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedCartanJointRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

local instance fixedMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance fixedCartanTorsionNormedAddCommGroup :
    NormedAddCommGroup PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.normedAddCommGroup

local instance fixedCartanTorsionNormedSpace :
    NormedSpace ℝ PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.normedSpace ℝ

private def fixedCartanTorsionCoordinateLinearEquiv :
    PointwiseCartanTorsionTwoForm ≃ₗ[ℝ]
      (Fin 6 → LorentzianIndex → ℝ) where
  toFun := PointwiseCartanTorsionTwoForm.component
  invFun := PointwiseCartanTorsionTwoForm.mk
  left_inv torsion := by cases torsion; rfl
  right_inv _ := rfl
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar torsion; rfl

local instance fixedCartanTorsionFiniteDimensional :
    FiniteDimensional ℝ PointwiseCartanTorsionTwoForm :=
  FiniteDimensional.of_injective
    fixedCartanTorsionCoordinateLinearEquiv.toLinearMap
    fixedCartanTorsionCoordinateLinearEquiv.injective

private def fixedLorentzBivectorOneFormConnectionLinearMap :
    LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun := lorentzSkewConnectionOfBivectorOneForm
  map_add' := lorentzSkewConnectionOfBivectorOneForm_add
  map_smul' := lorentzSkewConnectionOfBivectorOneForm_smul

theorem fixedCurrent_coframe_one
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentFullSynchronizedCauchyState.coframe space = 1 := by
  change
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
        (canonicalCauchySlicePoint 0 space) = 1
  exact
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
      (canonicalCauchySlicePoint 0 space)

private def fixedJointBase
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
    positiveP506MatterCurrentFullSynchronizedCauchyState space

@[simp] theorem fixedJointBase_coframe_one
    (space : StageNineSpatialPoint) (point : BasePoint) :
    (fixedJointBase space).coframe point = 1 := by
  exact fixedCurrent_coframe_one space

private def fixedLorentzVariationVector
    (direction : LorentzBivectorOneForm)
    (joint : StageNineSpatialPoint × BasePoint) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ formDirection : LorentzianIndex,
      diracMatrixMatterAction
        (inverseCoframeDiracGamma
          { coframe := 1, derivative := 0 } formDirection)
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm direction)
            formDirection)
          ((fixedJointBase joint.1).matter joint.2))

private theorem fixedLorentzVariationVector_coordinates_contDiff
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv (fixedLorentzVariationVector direction joint) := by
  have matterSmooth := fixedJointMatterCoordinates_contDiff
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm direction)
              formDirection)
            ((fixedJointBase joint.1).matter joint.2)) := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_const : ContDiff ℝ ∞ fun _ :
          StageNineSpatialPoint × BasePoint =>
            diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm direction)
              formDirection)).clm_apply matterSmooth
    change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm direction)
            formDirection)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              ((fixedJointBase joint.1).matter joint.2)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := 1, derivative := 0 } formDirection)
            (diracMatrixMatterAction
              (diracSpinConnectionLift
                (lorentzSkewConnectionOfBivectorOneForm direction)
                formDirection)
              ((fixedJointBase joint.1).matter joint.2))) := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        (contDiff_const : ContDiff ℝ ∞ fun _ :
          StageNineSpatialPoint × BasePoint =>
            inverseCoframeDiracGamma
              { coframe := 1, derivative := 0 } formDirection)).clm_apply
        (variationSmooth formDirection)
    change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := 1, derivative := 0 } formDirection)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (diracMatrixMatterAction
                (diracSpinConnectionLift
                  (lorentzSkewConnectionOfBivectorOneForm direction)
                  formDirection)
                ((fixedJointBase joint.1).matter joint.2))))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have sumSmooth : ContDiff ℝ ∞ fun joint :
      StageNineSpatialPoint × BasePoint =>
        ∑ formDirection : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := 1, derivative := 0 } formDirection)
              (diracMatrixMatterAction
                (diracSpinConnectionLift
                  (lorentzSkewConnectionOfBivectorOneForm direction)
                  formDirection)
                ((fixedJointBase joint.1).matter joint.2))) := by
    exact ContDiff.sum fun formDirection _ => kineticSmooth formDirection
  have phasedSmooth :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        Complex.I •
          ∑ formDirection : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := 1, derivative := 0 } formDirection)
                (diracMatrixMatterAction
                  (diracSpinConnectionLift
                    (lorentzSkewConnectionOfBivectorOneForm direction)
                    formDirection)
                  ((fixedJointBase joint.1).matter joint.2))) :=
    (contDiff_const : ContDiff ℝ ∞ fun _ :
      StageNineSpatialPoint × BasePoint => Complex.I).smul sumSmooth
  unfold fixedLorentzVariationVector
  simpa only [map_smul, map_sum] using phasedSmooth

private theorem fixedLorentzPairingSum_contDiff
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (fixedLorentzVariationVector direction joint) index *
          (fixedJointBase joint.1).conjugateMatter joint.2
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
  apply ContDiff.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have vectorEntrySmooth : ContDiff ℝ ∞ fun joint :
      StageNineSpatialPoint × BasePoint =>
        matterCoordinateEquiv
            (fixedLorentzVariationVector direction joint) index :=
    (projection.restrictScalars ℝ).contDiff.comp
      (fixedLorentzVariationVector_coordinates_contDiff direction)
  have dualEntrySmooth : ContDiff ℝ ∞ fun joint :
      StageNineSpatialPoint × BasePoint =>
        (fixedJointBase joint.1).conjugateMatter joint.2
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) := by
    simpa only [fixedJointBase] using
      fixedJointConjugateMatter_apply_contDiff
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))
  exact vectorEntrySmooth.mul dualEntrySmooth

private theorem fixedLorentzDualPairing_contDiff
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedJointBase joint.1).conjugateMatter joint.2
        (fixedLorentzVariationVector direction joint) := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedJointBase joint.1).conjugateMatter joint.2
        (fixedLorentzVariationVector direction joint)) =
    fun joint =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (fixedLorentzVariationVector direction joint) index *
          (fixedJointBase joint.1).conjugateMatter joint.2
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
    funext joint
    simpa only [matterCoordinateEquiv.symm_apply_apply] using
      coframeMatterDual_coordinate_expansion
        ((fixedJointBase joint.1).conjugateMatter joint.2)
        (matterCoordinateEquiv
          (fixedLorentzVariationVector direction joint))]
  exact fixedLorentzPairingSum_contDiff direction

private theorem fixedLorentzMatterFirstCoefficient_eq
    (direction : LorentzBivectorOneForm)
    (joint : StageNineSpatialPoint × BasePoint) :
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        joint.2 (toContinuumPointField (fixedJointBase joint.1) joint.2)
        direction =
      ((fixedJointBase joint.1).conjugateMatter joint.2
        (fixedLorentzVariationVector direction joint)).re := by
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
    fixedLorentzVariationVector
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart_local,
    matterDerivativeFrameRelative_zeroChart, fixedJointBase_coframe_one,
    Matrix.det_one, abs_one, one_mul]

private theorem fixedLorentzMatterFirstCoefficient_contDiff
    (direction : LorentzBivectorOneForm) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        joint.2 (toContinuumPointField (fixedJointBase joint.1) joint.2)
        direction := by
  have realPairingSmooth : ContDiff ℝ ∞ fun joint :
      StageNineSpatialPoint × BasePoint =>
        ((fixedJointBase joint.1).conjugateMatter joint.2
          (fixedLorentzVariationVector direction joint)).re :=
    Complex.reCLM.contDiff.comp
      (fixedLorentzDualPairing_contDiff direction)
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        joint.2 (toContinuumPointField (fixedJointBase joint.1) joint.2)
        direction) =
      fun joint =>
        ((fixedJointBase joint.1).conjugateMatter joint.2
          (fixedLorentzVariationVector direction joint)).re by
    funext joint
    exact fixedLorentzMatterFirstCoefficient_eq direction joint]
  exact realPairingSmooth

theorem fixedJointSpinResponse_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2 := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro triple
  let direction :=
    loweredLorentzBivectorOneFormCoordinate
      (missingTripleOfOneForm triple) internalPair
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        joint.2 (toContinuumPointField (fixedJointBase joint.1) joint.2)
        direction)
  exact
    (contDiff_const.mul
      (fixedLorentzMatterFirstCoefficient_contDiff direction)).neg

private theorem fixedJointTorsion_eq
    (joint : StageNineSpatialPoint × BasePoint) :
    diracDualFormNativeActionCartanTorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2 =
      cartanTorsionOfThreeForm (1 : LorentzianCoframe)
        (diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          (fixedJointBase joint.1) joint.2) := by
  unfold diracDualFormNativeActionCartanTorsionAt
  rw [fixedJointBase_coframe_one]

theorem fixedJointTorsion_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      diracDualFormNativeActionCartanTorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2 := by
  have inverseSmooth :=
    (cartanTorsionThreeFormLinearEquiv (1 : LorentzianCoframe) (by simp))
      |>.symm.toContinuousLinearEquiv.contDiff.comp
        fixedJointSpinResponse_contDiff
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    (cartanTorsionThreeFormLinearEquiv
      (1 : LorentzianCoframe) (by simp)).symm
      (diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2) at inverseSmooth
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      diracDualFormNativeActionCartanTorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2) =
    fun joint =>
      cartanTorsionOfThreeForm (1 : LorentzianCoframe)
        (diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          (fixedJointBase joint.1) joint.2) by
    funext joint
    exact fixedJointTorsion_eq joint]
  simpa only [cartanTorsionThreeFormLinearEquiv_symm_apply] using
    inverseSmooth

private theorem fixedJointContorsion_eq
    (joint : StageNineSpatialPoint × BasePoint) :
    diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2 =
      contorsionOfCartanTorsion (1 : LorentzianCoframe)
        (diracDualFormNativeActionCartanTorsionAt positiveSmoothUnifiedSource
          (fixedJointBase joint.1) joint.2) := by
  unfold diracDualFormNativeActionCartanContorsionAt
  rw [fixedJointBase_coframe_one]

theorem fixedJointContorsion_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2 := by
  have inverseSmooth :=
    (cartanContorsionTorsionLinearEquiv
      (1 : LorentzianCoframe) (by simp))
      |>.symm.toContinuousLinearEquiv.contDiff.comp
        fixedJointTorsion_contDiff
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    (cartanContorsionTorsionLinearEquiv
      (1 : LorentzianCoframe) (by simp)).symm
      (diracDualFormNativeActionCartanTorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2) at inverseSmooth
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      diracDualFormNativeActionCartanContorsionAt positiveSmoothUnifiedSource
        (fixedJointBase joint.1) joint.2) =
    fun joint =>
      contorsionOfCartanTorsion (1 : LorentzianCoframe)
        (diracDualFormNativeActionCartanTorsionAt positiveSmoothUnifiedSource
          (fixedJointBase joint.1) joint.2) by
    funext joint
    exact fixedJointContorsion_eq joint]
  simpa only [cartanContorsionTorsionLinearEquiv_symm_apply] using
    inverseSmooth

private theorem fixedJointCartanConnection_eq
    (joint : StageNineSpatialPoint × BasePoint) :
    sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1 joint.2 =
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
          PointwiseLorentzianCoframeJet).lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource (fixedJointBase joint.1) joint.2) := by
  unfold sourceActionGeneratedDiracDualCartanConnectionField
    diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection
  rw [sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt,
    fixedCurrent_coframe_one]
  rfl

theorem fixedJointCartanConnection_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1 joint.2 := by
  have liftedSmooth :=
    fixedLorentzBivectorOneFormConnectionLinearMap.toContinuousLinearMap
      |>.contDiff.comp fixedJointContorsion_contDiff
  change ContDiff ℝ ∞
    (fun joint : StageNineSpatialPoint × BasePoint =>
      lorentzSkewConnectionOfBivectorOneForm
        (diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource (fixedJointBase joint.1) joint.2)) at liftedSmooth
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1 joint.2) =
    fun joint =>
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
          PointwiseLorentzianCoframeJet).lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource (fixedJointBase joint.1) joint.2) by
    funext joint
    exact fixedJointCartanConnection_eq joint]
  exact contDiff_const.add liftedSmooth

theorem fixedJointCartanConnection_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        joint.1 joint.2 formDirection internalOut internalIn :=
  contDiff_pi.mp
    (contDiff_pi.mp
      (contDiff_pi.mp fixedJointCartanConnection_contDiff formDirection)
    internalOut)
    internalIn

theorem fixedJointCartanConnection_origin_contDiff :
    ContDiff ℝ ∞ fun space =>
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space 0 := by
  simpa [Function.comp_def, ContinuousLinearMap.inl_apply] using
    fixedJointCartanConnection_contDiff.comp_continuousLinearMap
      (g := ContinuousLinearMap.inl ℝ StageNineSpatialPoint BasePoint)

theorem fixedJointCartanConnection_origin_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space 0 formDirection internalOut internalIn := by
  simpa [Function.comp_def, ContinuousLinearMap.inl_apply] using
    (fixedJointCartanConnection_component_contDiff
      formDirection internalOut internalIn).comp_continuousLinearMap
      (g := ContinuousLinearMap.inl ℝ StageNineSpatialPoint BasePoint)

/-- At the fixed P506/L0 contact, the Cartan origin value is independent of
the spatial contact label.  This is not inferred from smoothness: the three
fields consumed by W13 are recomputed at both contacts and identified using
their explicit fixed-current normal forms. -/
theorem fixedJointCartanConnection_origin_eq
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        space 0 =
      sourceActionGeneratedDiracDualCartanConnectionField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState
        0 0 := by
  let first :=
    sourceActionGeneratedJointLocalActualLift
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      space
  let second :=
    sourceActionGeneratedJointLocalActualLift
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState
      0
  have coframeEq : first.coframe 0 = second.coframe 0 := by
    change (fixedJointBase space).coframe 0 =
      (fixedJointBase 0).coframe 0
    rw [fixedJointBase_coframe_one, fixedJointBase_coframe_one]
  have matterEq : first.matter 0 = second.matter 0 := by
    apply matterCoordinateEquiv.injective
    rw [fixedJointMatterCoordinates_normalForm,
      fixedJointMatterCoordinates_normalForm]
    simp
  have conjugateMatterEq :
      first.conjugateMatter 0 = second.conjugateMatter 0 := by
    apply LinearMap.ext
    intro matter
    rw [fixedJointConjugateMatter_apply_normalForm,
      fixedJointConjugateMatter_apply_normalForm]
    simp
  have response :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      positiveSmoothUnifiedSource first second 0 0
      coframeEq matterEq conjugateMatterEq
  unfold sourceActionGeneratedDiracDualCartanConnectionField
    diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  change
    diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource first 0 =
      diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource second 0 at response
  rw [sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt,
    sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt]
  rw [sourceActionGeneratedJointLocalActualLift_coframe_at,
    sourceActionGeneratedJointLocalActualLift_coframe_at, response]
  rw [fixedCurrent_coframe_one, fixedCurrent_coframe_one]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedCartanJointRegularity
