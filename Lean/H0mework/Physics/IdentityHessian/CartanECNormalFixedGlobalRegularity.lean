import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity
import H0mework.Physics.IdentityHessian.CartanECNormalFixedContactRegularity
import H0mework.Physics.Gauge.GaugeAuxiliaryIntegratedVariation

/-!
# Fixed P506/L0 KIN-16 global regularity

This module computes the one fixed P506/L0 contact family directly.  Its
purpose is the positive KIN-16 bundle:

* the exact-lineage contact data vary smoothly in the spatial contact;
* the action-generated Hessian, Cartan restart, and EC-normal write therefore
  give one explicit smooth nine-field diagonal actual;
* its complete time-zero Cauchy restriction is the KIN-15 whole-slice current.

No arbitrary-current regularity theory, atlas, gluing witness, residual
inverse, supplied response, or branch choice is introduced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineConjugateMatterActionTimeVelocity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalJointLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedCartanJointRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedMatterJointRegularity
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarLocalSpinDensity
open StageNineTopologicalFourFormPairing
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance fixedGlobalP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity.fixedP286CoordinateIndexFintype

local instance fixedGlobalP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity.fixedP286CoordinateIsTopologicalAddGroup

local instance fixedGlobalMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Fixed live contact point field -/

def fixedECContactField
    (space : StageNineSpatialPoint) : StageNineContinuumPointField :=
  diracDualFormNativeECNormalContactField
    (fixedCartanReactionContact space)

@[simp] theorem fixedECContactField_coframe
    (space : StageNineSpatialPoint) :
    (fixedECContactField space).coframe = 1 := by
  change (fixedCartanReactionContact space).coframe 0 = 1
  exact fixedCartanReactionContact_coframe_one space 0

theorem fixedECContactField_gaugeConnectionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv
        ((fixedCartanReactionContact space).gaugeConnection 0 direction) := by
  simpa only [fixedCartanReactionContact_gaugeConnection_origin] using
    fixedCurrent_gaugeConnectionCoordinate_contDiff direction

theorem fixedECContactField_gaugeAuxiliaryCoordinate_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv ((fixedECContactField space).gaugeAuxiliary pair) := by
  change ContDiff ℝ ∞ fun space =>
    p286CoordinateEquiv
      ((fixedCartanReactionContact space).gaugeAuxiliary 0 pair)
  simpa only [fixedCartanReactionContact_gaugeAuxiliary_origin] using
    fixedCurrent_gaugeAuxiliaryCoordinate_contDiff pair

theorem fixedCartanReactionGaugeConnectionDerivativeCoordinate_contDiff
    (derivativeDirection formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv
        (p286ConnectionDerivative (fixedCartanReactionContact space) 0
          derivativeDirection formDirection) := by
  have jointSmooth :
      ContDiff ℝ ∞
        (Function.uncurry fun space : StageNineSpatialPoint =>
          fun point : BasePoint =>
            p286CoordinateEquiv
              ((fixedCartanReactionContact space).gaugeConnection
                point formDirection)) := by
    change ContDiff ℝ ∞ fun joint :
        StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((fixedCartanReactionContact joint.1).gaugeConnection
          joint.2 formDirection)
    exact
      fixedCartanReactionGaugeConnectionCoordinate_contDiff formDirection
  have derivativeSmooth :=
    jointSmooth.fderiv_apply
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint => (0 : BasePoint))
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
          coordinateDirection derivativeDirection)
      (by simp)
  simpa only [p286ConnectionDerivative, fieldDirectionalDerivative,
    p286CoordinateEquiv.apply_symm_apply] using derivativeSmooth

theorem fixedECContactField_gaugeCurvatureCoordinate_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      p286CoordinateEquiv ((fixedECContactField space).gaugeCurvature pair) := by
  have bracketSmooth :
      ContDiff ℝ ∞ fun space =>
        p286CoordinateLieBracket
          (p286CoordinateEquiv
            (positiveP506MatterCurrentFullSynchronizedCauchyState
              |>.gaugeConnection space (pairFirst pair)))
          (p286CoordinateEquiv
            (positiveP506MatterCurrentFullSynchronizedCauchyState
              |>.gaugeConnection space (pairSecond pair))) := by
    exact
      (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
        (fixedCurrent_gaugeConnectionCoordinate_contDiff
          (pairFirst pair))).clm_apply
        (fixedCurrent_gaugeConnectionCoordinate_contDiff
          (pairSecond pair))
  rw [show
    (fun space =>
      p286CoordinateEquiv ((fixedECContactField space).gaugeCurvature pair)) =
      fun space =>
        p286CoordinateEquiv
            (p286ConnectionDerivative (fixedCartanReactionContact space) 0
              (pairFirst pair) (pairSecond pair)) -
          p286CoordinateEquiv
            (p286ConnectionDerivative (fixedCartanReactionContact space) 0
              (pairSecond pair) (pairFirst pair)) +
          p286CoordinateLieBracket
            (p286CoordinateEquiv
              (positiveP506MatterCurrentFullSynchronizedCauchyState
                |>.gaugeConnection space (pairFirst pair)))
            (p286CoordinateEquiv
              (positiveP506MatterCurrentFullSynchronizedCauchyState
                |>.gaugeConnection space (pairSecond pair))) by
    funext space
    unfold fixedECContactField diracDualFormNativeECNormalContactField
      diracDualFormNativeECNormalPreparedActual
      restrictContinuumPointFieldToIIPlus toContinuumPointField
      holonomicGaugeCurvature
    simp only [map_add, map_sub]
    congr 1
    unfold p286CoordinateLieBracket
    simp only [p286CoordinateEquiv.symm_apply_apply]
    apply congrArg p286CoordinateEquiv
    change
      p286LieBracket
          ((fixedCartanReactionContact space).gaugeConnection
            0 (pairFirst pair))
          ((fixedCartanReactionContact space).gaugeConnection
            0 (pairSecond pair)) =
        p286LieBracket
          (positiveP506MatterCurrentFullSynchronizedCauchyState
            |>.gaugeConnection space (pairFirst pair))
          (positiveP506MatterCurrentFullSynchronizedCauchyState
            |>.gaugeConnection space (pairSecond pair))
    rw [fixedCartanReactionContact_gaugeConnection_origin,
      fixedCartanReactionContact_gaugeConnection_origin]]
  exact
    ((fixedCartanReactionGaugeConnectionDerivativeCoordinate_contDiff
      (pairFirst pair) (pairSecond pair)).sub
      (fixedCartanReactionGaugeConnectionDerivativeCoordinate_contDiff
        (pairSecond pair) (pairFirst pair))).add bracketSmooth

@[simp] theorem fixedECContactField_scalar
    (space : StageNineSpatialPoint) :
    (fixedECContactField space).scalar =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    (fixedCartanReactionContact space).scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  exact fixedCartanReactionContact_scalar space 0

@[simp] theorem fixedECContactField_matter
    (space : StageNineSpatialPoint) :
    (fixedECContactField space).matter = diracSpinTwoMatterProbe := by
  change (fixedCartanReactionContact space).matter 0 =
    diracSpinTwoMatterProbe
  exact fixedCartanReactionContact_matter_origin space

@[simp] theorem fixedECContactField_conjugateMatter
    (space : StageNineSpatialPoint) :
    (fixedECContactField space).conjugateMatter =
      diracSpinZeroMatterCoordinate := by
  change (fixedCartanReactionContact space).conjugateMatter 0 =
    diracSpinZeroMatterCoordinate
  exact fixedCartanReactionContact_conjugateMatter_origin space

/-! ## Fixed scalar and matter first jets -/

theorem fixedMatterOrdinaryDerivativeCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((fixedCartanReactionContact space).matter point))
        0 direction := by
  have jointSmooth :
      ContDiff ℝ ∞
        (Function.uncurry fun space : StageNineSpatialPoint =>
          fun point : BasePoint =>
            matterCoordinateEquiv
              ((fixedCartanReactionContact space).matter point)) := by
    change ContDiff ℝ ∞ fun joint :
        StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        ((fixedCartanReactionContact joint.1).matter joint.2)
    simpa only [fixedCartanReactionContact,
      sourceActionGeneratedDiracDualCartanReactionLocalActualLift_matter,
      sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_matter]
      using fixedJointMatterCoordinates_contDiff
  simpa only [fieldDirectionalDerivative] using
    jointSmooth.fderiv_apply
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint => (0 : BasePoint))
      (contDiff_const :
        ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
          coordinateDirection direction)
      (by simp)

private theorem fixedMatterCartanActionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (sourceActionGeneratedDiracDualCartanConnectionField
              positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedCauchyState
              space 0)
            direction)
          diracSpinTwoMatterProbe) := by
  have matrixSmooth :
      ContDiff ℝ ∞ fun space =>
        diracSpinConnectionLift
          (sourceActionGeneratedDiracDualCartanConnectionField
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState
          space 0)
            direction := by
    change ContDiff ℝ ∞ fun space =>
      diracSpinConnectionLiftLinear direction
        (sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space 0)
    change ContDiff ℝ ∞
      ((diracSpinConnectionLiftLinear direction).toContinuousLinearMap ∘
        fun space =>
          sourceActionGeneratedDiracDualCartanConnectionField
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState
            space 0)
    exact
      (diracSpinConnectionLiftLinear direction).toContinuousLinearMap.contDiff.comp
        fixedJointCartanConnection_origin_contDiff
  have actionSmooth :=
    (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
      matrixSmooth).clm_apply
        (contDiff_const :
          ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
            matterCoordinateEquiv diracSpinTwoMatterProbe)
  change ContDiff ℝ ∞ fun space =>
    matterCoordinateEquiv
      (diracMatrixMatterAction
        (diracSpinConnectionLift
          (sourceActionGeneratedDiracDualCartanConnectionField
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState
            space 0)
          direction)
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv diracSpinTwoMatterProbe))) at actionSmooth
  simpa only [matterCoordinateEquiv.symm_apply_apply] using actionSmooth

private theorem fixedMatterGaugeActionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            ((fixedCartanReactionContact space).gaugeConnection 0 direction))
          diracSpinTwoMatterProbe) := by
  have actionSmooth :=
    (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff.comp
      (fixedECContactField_gaugeConnectionCoordinate_contDiff direction))
      |>.clm_apply
        (contDiff_const :
          ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
            matterCoordinateEquiv diracSpinTwoMatterProbe)
  change ContDiff ℝ ∞ fun space =>
    matterCoordinateEquiv
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              ((fixedCartanReactionContact space).gaugeConnection
                0 direction))))
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv diracSpinTwoMatterProbe))) at actionSmooth
  simpa only [p286CoordinateEquiv.symm_apply_apply,
    matterCoordinateEquiv.symm_apply_apply] using actionSmooth

theorem fixedECContactField_matterCovariantDerivative_coordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      matterCoordinateEquiv
        ((fixedECContactField space).matterCovariantDerivative direction) := by
  change ContDiff ℝ ∞ fun space =>
    matterCoordinateEquiv
      (holonomicMatterCovariantDerivative
        (fixedCartanReactionContact space) 0 direction)
  simp only [holonomicMatterCovariantDerivative,
    fixedCartanReactionContact_matter_origin, map_add,
    matterCoordinateEquiv.apply_symm_apply]
  exact
    (fixedMatterOrdinaryDerivativeCoordinate_contDiff direction).add
      (fixedMatterCartanActionCoordinate_contDiff direction)
      |>.add (fixedMatterGaugeActionCoordinate_contDiff direction)

theorem fixedECContactField_scalarCovariantDerivative_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      (fixedECContactField space).scalarCovariantDerivative direction := by
  have gaugeActionSmooth :=
    (scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.comp
      (fixedECContactField_gaugeConnectionCoordinate_contDiff direction))
      |>.clm_apply
        (contDiff_const :
          ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
            sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  change ContDiff ℝ ∞ fun space =>
    holonomicScalarCovariantDerivative
      (fixedCartanReactionContact space) 0 direction
  rw [show
    (fun space =>
      holonomicScalarCovariantDerivative
        (fixedCartanReactionContact space) 0 direction) =
      fun space =>
        scalarMotherLieAction
          (p286LieBlockEmbed
            ((fixedCartanReactionContact space).gaugeConnection 0 direction))
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext space
    unfold holonomicScalarCovariantDerivative
    have scalarConstant :
        (fixedCartanReactionContact space).scalar =
          fun _ => sourceGeneratedVacuumCoordinates
            positiveSmoothUnifiedSource := by
      funext point
      exact fixedCartanReactionContact_scalar space point
    rw [scalarConstant]
    simp [fieldDirectionalDerivative]]
  change ContDiff ℝ ∞ fun space =>
    scalarMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          (p286CoordinateEquiv
            ((fixedCartanReactionContact space).gaugeConnection 0 direction))))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) at gaugeActionSmooth
  simpa only [p286CoordinateEquiv.symm_apply_apply] using gaugeActionSmooth

/-! ## Fixed gauge density and coframe derivative -/

private def fixedECGaugeAuxiliaryCoordinates
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear
    (fixedECContactField space).gaugeAuxiliary

private def fixedECGaugeCurvatureCoordinates
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear
    (fixedECContactField space).gaugeCurvature

private theorem fixedECGaugeAuxiliaryCoordinates_contDiff :
    ContDiff ℝ ∞ fixedECGaugeAuxiliaryCoordinates := by
  apply contDiff_pi'
  intro pair
  exact fixedECContactField_gaugeAuxiliaryCoordinate_contDiff pair

private theorem fixedECGaugeCurvatureCoordinates_contDiff :
    ContDiff ℝ ∞ fixedECGaugeCurvatureCoordinates := by
  apply contDiff_pi'
  intro pair
  exact fixedECContactField_gaugeCurvatureCoordinate_contDiff pair

private theorem fixedP286CoordinateWedge_joint_contDiffAt
    (center : StageNineSpatialPoint × LorentzianCoframe)
    (first second :
      StageNineSpatialPoint × LorentzianCoframe →
        FormNativeP286GaugeCoordinateTwoForm)
    (firstSmooth : ∀ pair,
      ContDiffAt ℝ ∞ (fun joint => first joint pair) center)
    (secondSmooth : ∀ pair,
      ContDiffAt ℝ ∞ (fun joint => second joint pair) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      formNativeP286GaugeCoordinateWedgeCoefficient
        (first joint) (second joint)) center := by
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro pair _
  exact
    (formNativeP286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.contDiff.contDiffAt.comp center (firstSmooth pair)).clm_apply
      (secondSmooth (twoFormComplement pair))

private theorem fixedECGaugeConstitutiveCoordinates_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        formNativeP286CoordinateBlockwiseConstitutive joint.2
          ((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings
            positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
          (fixedECGaugeAuxiliaryCoordinates joint.1))
      (space, 1) := by
  apply contDiffAt_pi'
  intro output
  rw [show
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      formNativeP286CoordinateBlockwiseConstitutive joint.2
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        (fixedECGaugeAuxiliaryCoordinates joint.1) output) =
      fun joint =>
        ∑ input : Fin 6,
          gaugeOperatorCoefficient
              (coframeGaugeSpacetimeHodgeLinear joint.2) output input •
            formNativeP286BlockwiseCouplingCoordinateLinear
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
              (fixedECGaugeAuxiliaryCoordinates joint.1 input) by
    funext joint
    exact congrFun
      (formNativeP286CoordinateBlockwiseConstitutive_eq_sum joint.2
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        (fixedECGaugeAuxiliaryCoordinates joint.1))
      output]
  apply ContDiffAt.sum
  intro input _
  have coefficientSmooth :
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          gaugeOperatorCoefficient
            (coframeGaugeSpacetimeHodgeLinear joint.2) output input)
        (space, 1) := by
    exact
      (coframeHodgeOperatorCoefficient_contDiffAt
        (1 : LorentzianCoframe) (by norm_num) output input).comp
        (space, 1) contDiffAt_snd
  have inputSmooth :
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          fixedECGaugeAuxiliaryCoordinates joint.1 input)
        (space, 1) :=
    ((contDiff_pi.mp fixedECGaugeAuxiliaryCoordinates_contDiff input).comp
      contDiff_fst).contDiffAt
  have coupledInputSmooth :
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          formNativeP286BlockwiseCouplingCoordinateLinear
            ((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
            ((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
            ((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
            (fixedECGaugeAuxiliaryCoordinates joint.1 input))
        (space, 1) := by
    exact
      (formNativeP286BlockwiseCouplingCoordinateLinear
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ))
        |>.toContinuousLinearMap.contDiff.contDiffAt.comp
          (space, 1) inputSmooth
  exact coefficientSmooth.smul coupledInputSmooth

theorem fixedECGaugeDensity_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (Function.uncurry fun space : StageNineSpatialPoint =>
        fun candidate : LorentzianCoframe =>
          diracDualFormNativeCoframeGaugeDensity
            positiveSmoothUnifiedSource
            (fixedECContactField space) candidate)
      (space, 1) := by
  change ContDiffAt ℝ ∞
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      diracDualFormNativeCoframeGaugeDensity
        positiveSmoothUnifiedSource
        (fixedECContactField joint.1) joint.2)
    (space, 1)
  rw [show
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      diracDualFormNativeCoframeGaugeDensity
        positiveSmoothUnifiedSource
        (fixedECContactField joint.1) joint.2) =
      fun joint =>
        formNativeP286GaugeCoordinateWedgeCoefficient
            (fixedECGaugeAuxiliaryCoordinates joint.1)
            (fixedECGaugeCurvatureCoordinates joint.1) -
          (1 / 2 : ℝ) *
            formNativeP286GaugeCoordinateWedgeCoefficient
              (fixedECGaugeAuxiliaryCoordinates joint.1)
              (formNativeP286CoordinateBlockwiseConstitutive joint.2
                ((sourceGeneratedUnifiedCouplings
                  positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
                ((sourceGeneratedUnifiedCouplings
                  positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
                ((sourceGeneratedUnifiedCouplings
                  positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
                (fixedECGaugeAuxiliaryCoordinates joint.1)) by
    funext joint
    unfold diracDualFormNativeCoframeGaugeDensity
    rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286,
      formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual,
      formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
    simp [fixedECGaugeAuxiliaryCoordinates,
      fixedECGaugeCurvatureCoordinates,
      formNativeP286CoordinateBlockwiseConstitutive, withCoframe]]
  have auxiliarySmooth : ∀ pair,
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          fixedECGaugeAuxiliaryCoordinates joint.1 pair)
        (space, 1) :=
    fun pair =>
      ((contDiff_pi.mp fixedECGaugeAuxiliaryCoordinates_contDiff pair).comp
        contDiff_fst).contDiffAt
  have curvatureSmooth : ∀ pair,
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          fixedECGaugeCurvatureCoordinates joint.1 pair)
        (space, 1) :=
    fun pair =>
      ((contDiff_pi.mp fixedECGaugeCurvatureCoordinates_contDiff pair).comp
        contDiff_fst).contDiffAt
  have constitutiveSmooth : ∀ pair,
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          formNativeP286CoordinateBlockwiseConstitutive joint.2
            ((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
            ((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
            ((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
            (fixedECGaugeAuxiliaryCoordinates joint.1) pair)
        (space, 1) :=
    fun pair =>
      contDiffAt_pi.mp
        (fixedECGaugeConstitutiveCoordinates_contDiffAt space) pair
  exact
    (fixedP286CoordinateWedge_joint_contDiffAt (space, 1)
      (fun joint => fixedECGaugeAuxiliaryCoordinates joint.1)
      (fun joint => fixedECGaugeCurvatureCoordinates joint.1)
      auxiliarySmooth curvatureSmooth).sub
      (contDiffAt_const.mul
        (fixedP286CoordinateWedge_joint_contDiffAt (space, 1)
          (fun joint => fixedECGaugeAuxiliaryCoordinates joint.1)
          (fun joint =>
            formNativeP286CoordinateBlockwiseConstitutive joint.2
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
              (fixedECGaugeAuxiliaryCoordinates joint.1))
          auxiliarySmooth constitutiveSmooth))

theorem fixedECGaugeEuler_apply_contDiff
    (variation : LorentzianCoframe) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource
        (fixedECContactField space) variation := by
  rw [contDiff_iff_contDiffAt]
  intro space
  have derivativeSmooth :=
    (fixedECGaugeDensity_joint_contDiffAt space).fderiv
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : StageNineSpatialPoint => (1 : LorentzianCoframe)) space)
      (by simp)
  have appliedSmooth :=
    derivativeSmooth.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : StageNineSpatialPoint => variation) space)
  change ContDiffAt ℝ ∞
    (fun space =>
      fderiv ℝ
        (diracDualFormNativeCoframeGaugeDensity
          positiveSmoothUnifiedSource (fixedECContactField space))
        (1 : LorentzianCoframe) variation)
    space at appliedSmooth
  simpa only [diracDualFormNativeCoframeGaugeEulerCovector,
    fixedECContactField_coframe] using appliedSmooth

theorem fixedECGaugeEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource
        (fixedECContactField space)
        (coframeCoordinateDirection row column) :=
  fixedECGaugeEuler_apply_contDiff
    (coframeCoordinateDirection row column)

/-! ## Fixed matter density and coframe derivative -/

private theorem fixedECMatterKineticVector_coordinate_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumMatterKineticVector
            positiveSmoothUnifiedSource 0 0
            (withCoframe (fixedECContactField joint.1) joint.2)))
      (space, 1) := by
  have gammaSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := joint.2, derivative := 0 } direction)
        (space, 1) := by
    intro direction
    have outer : ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := candidate, derivative := 0 } direction)
        (1 : LorentzianCoframe) :=
      inverseCoframeDiracGamma_contDiffAt
        (1 : LorentzianCoframe) (by norm_num) direction
    rw [show
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := joint.2, derivative := 0 } direction) =
      (fun candidate : LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := candidate, derivative := 0 } direction) ∘
        (fun joint : StageNineSpatialPoint × LorentzianCoframe => joint.2) by
      rfl]
    exact outer.comp (space, 1) contDiffAt_snd
  have derivativeSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          matterCoordinateEquiv
            ((fixedECContactField joint.1).matterCovariantDerivative
              direction)) := by
    intro direction
    exact
      (fixedECContactField_matterCovariantDerivative_coordinate_contDiff
        direction).comp contDiff_fst
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 } direction)
              ((fixedECContactField joint.1).matterCovariantDerivative
                direction)))
        (space, 1) := by
    intro direction
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap
        |>.contDiff.contDiffAt.comp
          (space, 1) (gammaSmooth direction)).clm_apply
        ((derivativeSmooth direction).contDiffAt)
    change ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := joint.2, derivative := 0 } direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                ((fixedECContactField joint.1).matterCovariantDerivative
                  direction)))))
      (space, 1) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  simp only [generatedContinuumMatterKineticVector,
    matterCovariantDerivativeVariationVector,
    matterCovariantDerivativeKineticSum,
    matterDerivativeFrameRelative, matterFrameRelative_zeroChart_local,
    withCoframe]
  simp only [map_smul, map_sum]
  exact
    (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : StageNineSpatialPoint × LorentzianCoframe =>
        (Complex.I : ℂ)) (space, 1)).smul
      (ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction)

private theorem fixedECMatterYukawaVector_coordinate_joint_contDiff :
    ContDiff ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumDiracDualYukawaVector
            positiveSmoothUnifiedSource 0 0
            (withCoframe (fixedECContactField joint.1) joint.2))) := by
  simp only [generatedContinuumDiracDualYukawaVector,
    scalarFrameRelativeCoordinates_zeroChart_local,
    matterFrameRelative_zeroChart_local, withCoframe,
    fixedECContactField_scalar, fixedECContactField_matter]
  exact contDiff_const

private theorem fixedECMatterVector_coordinate_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (withCoframe (fixedECContactField joint.1) joint.2)))
      (space, 1) := by
  unfold generatedContinuumDiracDualMatterVector
  simp only [map_add]
  exact
    (fixedECMatterKineticVector_coordinate_joint_contDiffAt space).add
      fixedECMatterYukawaVector_coordinate_joint_contDiff.contDiffAt

private theorem fixedECVolumeDensity_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        generatedVolumeDensity
          (withCoframe (fixedECContactField joint.1) joint.2))
      (space, 1) := by
  change ContDiffAt ℝ ∞
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      abs (Matrix.det joint.2)) (space, 1)
  exact
    (coframe_volume_contDiffAt
      (1 : LorentzianCoframe) (by norm_num)).comp
        (space, 1) contDiffAt_snd

private theorem fixedECMatterDualPairing_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        (fixedECContactField joint.1).conjugateMatter
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (withCoframe (fixedECContactField joint.1) joint.2)))
      (space, 1) := by
  rw [show
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      (fixedECContactField joint.1).conjugateMatter
        (generatedContinuumDiracDualMatterVector
          positiveSmoothUnifiedSource 0 0
          (withCoframe (fixedECContactField joint.1) joint.2))) =
    fun joint =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (generatedContinuumDiracDualMatterVector
              positiveSmoothUnifiedSource 0 0
              (withCoframe (fixedECContactField joint.1) joint.2)) index *
          (fixedECContactField joint.1).conjugateMatter
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
    funext joint
    simpa only [matterCoordinateEquiv.symm_apply_apply] using
      coframeMatterDual_coordinate_expansion
        (fixedECContactField joint.1).conjugateMatter
        (matterCoordinateEquiv
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (withCoframe (fixedECContactField joint.1) joint.2)))]
  apply ContDiffAt.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (PiLp.projₗ (𝕜 := ℂ) 2
      (fun _ : MatterCoordinateIndex => ℂ) index).toContinuousLinearMap
  have vectorEntrySmooth : ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        matterCoordinateEquiv
            (generatedContinuumDiracDualMatterVector
              positiveSmoothUnifiedSource 0 0
              (withCoframe (fixedECContactField joint.1) joint.2)) index)
      (space, 1) := by
    change ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        (projection.restrictScalars ℝ)
          (matterCoordinateEquiv
            (generatedContinuumDiracDualMatterVector
              positiveSmoothUnifiedSource 0 0
              (withCoframe (fixedECContactField joint.1) joint.2))))
      (space, 1)
    exact
      (projection.restrictScalars ℝ).contDiff.contDiffAt.comp
        (space, 1) (fixedECMatterVector_coordinate_joint_contDiffAt space)
  have dualEntrySmooth : ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        (fixedECContactField joint.1).conjugateMatter
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      (space, 1) := by
    simp only [fixedECContactField_conjugateMatter]
    exact contDiffAt_const
  exact vectorEntrySmooth.mul dualEntrySmooth

private theorem fixedECDensitizedDiracMatterDensity_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        generatedDensitizedContinuumDiracDualMatterDensity
          positiveSmoothUnifiedSource 0 0
          (withCoframe (fixedECContactField joint.1) joint.2))
      (space, 1) := by
  rw [show
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      generatedDensitizedContinuumDiracDualMatterDensity
        positiveSmoothUnifiedSource 0 0
        (withCoframe (fixedECContactField joint.1) joint.2)) =
    fun joint =>
      generatedVolumeDensity
          (withCoframe (fixedECContactField joint.1) joint.2) *
        ((fixedECContactField joint.1).conjugateMatter
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (withCoframe (fixedECContactField joint.1) joint.2))).re by
    funext joint
    rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing]
    simp only [matterDualFrameRelative_zeroChart_local, withCoframe]]
  exact
    (fixedECVolumeDensity_joint_contDiffAt space).mul
      (Complex.reCLM.contDiff.contDiffAt.comp
        (space, 1) (fixedECMatterDualPairing_joint_contDiffAt space))

private theorem fixedECScalarKineticDensity_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        generatedScalarKineticDensity positiveSmoothUnifiedSource 0 0
          (withCoframe (fixedECContactField joint.1) joint.2))
      (space, 1) := by
  have metricInverseSmooth : ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe joint.2)⁻¹)
      (space, 1) := by
    have outer : ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          (lorentzianMetricOfCoframe candidate)⁻¹)
        (1 : LorentzianCoframe) :=
      lorentzianMetric_inv_contDiffAt
        (1 : LorentzianCoframe) (by norm_num)
    rw [show
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe joint.2)⁻¹) =
      (fun candidate : LorentzianCoframe =>
        (lorentzianMetricOfCoframe candidate)⁻¹) ∘
        (fun joint : StageNineSpatialPoint × LorentzianCoframe => joint.2) by
      rfl]
    exact outer.comp (space, 1) contDiffAt_snd
  have derivativeSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞
        (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
          (fixedECContactField joint.1).scalarCovariantDerivative
            direction) := by
    intro direction
    exact
      (fixedECContactField_scalarCovariantDerivative_contDiff direction).comp
        contDiff_fst
  simp only [generatedScalarKineticDensity,
    scalarFrameRelativeCovariantDerivative,
    scalarFrameRelativeCoordinates_zeroChart_local, withCoframe]
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  exact
    (contDiffAt_pi.mp
      (contDiffAt_pi.mp metricInverseSmooth first) second).mul
    ((scalarCoordinatePairingRe_joint_contDiff_local _ _
      (derivativeSmooth first) (derivativeSmooth second)).contDiffAt)

private theorem fixedECScalarPotential_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        generatedScalarPotential positiveSmoothUnifiedSource 0 0
          (withCoframe (fixedECContactField joint.1) joint.2).scalar)
      (space, 1) := by
  rw [show
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      generatedScalarPotential positiveSmoothUnifiedSource 0 0
        (withCoframe (fixedECContactField joint.1) joint.2).scalar) =
    fun _ => (0 : ℝ) by
    funext joint
    simp [generatedScalarPotential, scalarCoordinateSquaredNorm,
      withCoframe, fixedECContactField_scalar]]
  exact contDiffAt_const

private theorem fixedECDensitizedScalarDensity_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
        generatedDensitizedContinuumScalarDensity
          positiveSmoothUnifiedSource 0 0
          (withCoframe (fixedECContactField joint.1) joint.2))
      (space, 1) := by
  unfold generatedDensitizedContinuumScalarDensity
  exact
    (fixedECVolumeDensity_joint_contDiffAt space).mul
      ((fixedECScalarKineticDensity_joint_contDiffAt space).sub
        (fixedECScalarPotential_joint_contDiffAt space))

theorem fixedECMatterDensity_joint_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (Function.uncurry fun space : StageNineSpatialPoint =>
        fun candidate : LorentzianCoframe =>
          diracDualFormNativeCoframeMatterDensity
            positiveSmoothUnifiedSource 0
            (fixedECContactField space) candidate)
      (space, 1) := by
  change ContDiffAt ℝ ∞
    (fun joint : StageNineSpatialPoint × LorentzianCoframe =>
      diracDualFormNativeCoframeMatterDensity
        positiveSmoothUnifiedSource 0
        (fixedECContactField joint.1) joint.2)
    (space, 1)
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  exact
    (fixedECDensitizedScalarDensity_joint_contDiffAt space).add
      (fixedECDensitizedDiracMatterDensity_joint_contDiffAt space)

theorem fixedECMatterEuler_apply_contDiff
    (variation : LorentzianCoframe) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0
        (fixedECContactField space) variation := by
  rw [contDiff_iff_contDiffAt]
  intro space
  have derivativeSmooth :=
    (fixedECMatterDensity_joint_contDiffAt space).fderiv
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : StageNineSpatialPoint => (1 : LorentzianCoframe)) space)
      (by simp)
  have appliedSmooth :=
    derivativeSmooth.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : StageNineSpatialPoint => variation) space)
  change ContDiffAt ℝ ∞
    (fun space =>
      fderiv ℝ
        (diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 (fixedECContactField space))
        (1 : LorentzianCoframe) variation)
    space at appliedSmooth
  simpa only [diracDualFormNativeCoframeMatterEulerCovector,
    fixedECContactField_coframe] using appliedSmooth

theorem fixedECMatterEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0
        (fixedECContactField space)
        (coframeCoordinateDirection row column) :=
  fixedECMatterEuler_apply_contDiff
    (coframeCoordinateDirection row column)

/-! ## Fixed EC load and generated Hessian write -/

private def fixedECCurvatureObservationCoordinateLinear
    (row column : LorentzianIndex) :
    PhysicalBivector →ₗ[ℝ] ℝ where
  toFun := fun rawCurvature =>
    identityDiracDualECCurvatureObservation rawCurvature
      (coframeCoordinateDirection row column)
  map_add' := by
    intro first second
    rw [identityDiracDualECCurvatureObservation_add]
    rfl
  map_smul' := by
    intro parameter rawCurvature
    unfold identityDiracDualECCurvatureObservation
    change
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
            (coframeCoordinateDirection row column))
          (gravityInternalPairVarianceNormalization
            (parameter • rawCurvature)) =
        parameter *
          gravityTopologicalWedgeCoefficient
            (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
              (coframeCoordinateDirection row column))
            (gravityInternalPairVarianceNormalization rawCurvature)
    rw [map_smul, gravityTopologicalWedgeCoefficient_smul_right]

private theorem fixedCartanCurvature_contDiff :
    ContDiff ℝ ∞ fun space =>
      holonomicGravityCurvature (fixedCartanReactionContact space) 0 := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro spacetime
  exact
    fixedCartanReactionGravityCurvature_component_contDiff
      internal spacetime

private theorem fixedCartanCurvatureObservation_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature
          (fixedCartanReactionContact space) 0)
        (coframeCoordinateDirection row column) := by
  change ContDiff ℝ ∞
    ((fixedECCurvatureObservationCoordinateLinear row column) ∘
      fun space =>
        holonomicGravityCurvature (fixedCartanReactionContact space) 0)
  exact
    (fixedECCurvatureObservationCoordinateLinear row column)
      |>.toContinuousLinearMap.contDiff.comp fixedCartanCurvature_contDiff

private theorem fixedIdentityECLoad_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedCartanReactionContact space)
        (coframeCoordinateDirection row column) := by
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  exact
    (contDiff_const.add
      (fixedECGaugeEuler_coordinate_contDiff row column)).add
      (fixedECMatterEuler_coordinate_contDiff row column)

theorem fixedIdentityECCoframeLowerOrderCoordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) row column := by
  unfold sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    coframeCovectorCoordinates
  simp only [add_apply]
  exact
    (fixedCartanCurvatureObservation_coordinate_contDiff row column).add
      (fixedIdentityECLoad_coordinate_contDiff row column)

private theorem fixedIdentityECCoframeLowerOrderCoordinates_contDiff :
    ContDiff ℝ ∞ fun space =>
      sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact fixedIdentityECCoframeLowerOrderCoordinate_contDiff row column

theorem fixedIdentityECCoframeAccelerationRow_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      (sourceActionGeneratedIdentityECCoframeAccelerationRows
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) : LorentzianCoframe) row column := by
  have lowerSmooth :=
    fixedIdentityECCoframeLowerOrderCoordinates_contDiff
  have directSmooth : ContDiff ℝ ∞ fun space =>
      -sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) row column :=
    (contDiff_pi.mp (contDiff_pi.mp lowerSmooth row) column).neg
  have transposeSmooth : ContDiff ℝ ∞ fun space =>
      -sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) column row :=
    (contDiff_pi.mp (contDiff_pi.mp lowerSmooth column) row).neg
  have signedTransposeSmooth : ContDiff ℝ ∞ fun space =>
      minkowskiInternalSign row * minkowskiInternalSign column *
        (-sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
          positiveSmoothUnifiedSource
          (fixedCartanReactionContact space) column row) :=
    (contDiff_const : ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
      minkowskiInternalSign row *
        minkowskiInternalSign column).mul transposeSmooth
  have averagedSmooth : ContDiff ℝ ∞ fun space =>
      (1 / 2 : ℝ) *
        (-sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
            positiveSmoothUnifiedSource
            (fixedCartanReactionContact space) row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            (-sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
              positiveSmoothUnifiedSource
              (fixedCartanReactionContact space) column row)) :=
    contDiff_const.mul (directSmooth.add signedTransposeSmooth)
  rw [show
    (fun space =>
      (sourceActionGeneratedIdentityECCoframeAccelerationRows
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) : LorentzianCoframe) row column) =
    fun space =>
      (1 / 2 : ℝ) *
        (-sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
            positiveSmoothUnifiedSource
            (fixedCartanReactionContact space) row column +
          minkowskiInternalSign row * minkowskiInternalSign column *
            (-sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
              positiveSmoothUnifiedSource
              (fixedCartanReactionContact space) column row)) by
    funext space
    unfold sourceActionGeneratedIdentityECCoframeAccelerationRows
      identityECEtaCompatibleProjection identityECEtaSymmetricPart
      identityECEtaAdjoint
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, smul_eq_mul]]
  exact averagedSmooth

private theorem fixedIdentityECCoframeAccelerationRows_contDiff :
    ContDiff ℝ ∞ fun space =>
      (sourceActionGeneratedIdentityECCoframeAccelerationRows
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) : LorentzianCoframe) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact fixedIdentityECCoframeAccelerationRow_contDiff row column

theorem fixedIdentityECHessianIncrement_coordinate_contDiff
    (first second internal column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space)).1
          (coordinateDirection first) (coordinateDirection second)
          internal column := by
  rw [show
    (fun space =>
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space)).1
          (coordinateDirection first) (coordinateDirection second)
          internal column) =
    fun space =>
      identityECNormalCoframeHessianCoordinate
        (sourceActionGeneratedIdentityECCoframeAccelerationRows
          positiveSmoothUnifiedSource
          (fixedCartanReactionContact space) : LorentzianCoframe)
        first second internal column by
    funext space
    simp [sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement,
      identityECTypedHolonomicCoframeHessianSection]]
  have coordinatesSmooth :=
    fixedIdentityECCoframeAccelerationRows_contDiff
  unfold identityECNormalCoframeHessianCoordinate
    identityECNormalMetricHessianCoordinate
    identityECWeylZeroRiemannCoordinate
    identityECScalarCurvature identityECRicciTensorCoordinate
    identityECEinsteinTensorCoordinate identityECEinsteinTrace
  simp_rw [identityECEtaSymmetricPart_apply]
  fun_prop

private def fixedIdentityECHessianActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
    positiveSmoothUnifiedSource (fixedCartanReactionContact space)

private def fixedIdentityECHessianCartanCurrent
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeIdentityECHessianCartanCurrent
    positiveSmoothUnifiedSource (fixedCartanReactionContact space)

def fixedIdentityECHessianCartanECNormalContactActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift
    positiveSmoothUnifiedSource (fixedCartanReactionContact space)

/-- Opaque fixed-lineage bridge to the public KIN-14 contact producer.  The
bridge prevents downstream diagonal regularity proofs from repeatedly
unfolding the complete source/action constructor. -/
theorem fixedIdentityECHessianCartanECNormalContactActual_eq_generated
    (space : StageNineSpatialPoint) :
    fixedIdentityECHessianCartanECNormalContactActual space =
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space :=
  rfl

private theorem fixedCartanReactionContact_coframe_eq_one
    (space : StageNineSpatialPoint) :
    (fixedCartanReactionContact space).coframe = fun _ => 1 := by
  funext point
  exact fixedCartanReactionContact_coframe_one space point

/-- The fixed contact's generated Hessian changes its second jet but preserves
the complete identity/zero first jet.  This is the temporal jet used by the
global diagonal; spatial derivatives of that diagonal are computed
separately from its whole-slice restriction. -/
theorem
    fixedIdentityECHessianCartanECNormalContactActual_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedIdentityECHessianCartanECNormalContactActual space).coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  let identityZeroJet : PointwiseLorentzianCoframeJet :=
    { coframe := 1, derivative := 0 }
  let increment :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
      positiveSmoothUnifiedSource
      (fixedCartanReactionContact space)
  have coframeEquality :
      (fixedIdentityECHessianCartanECNormalContactActual space).coframe =
        coframeFieldOfFirstAndSecondJet identityZeroJet increment := by
    funext point internal coordinate
    change
      (fixedCartanReactionContact space).coframe point internal coordinate +
          coframeHolonomicSecondJetQuadraticRealization increment point
            internal coordinate =
        affineCoframeFieldOfJet identityZeroJet point internal coordinate +
          coframeHolonomicSecondJetQuadraticRealization increment point
            internal coordinate
    rw [fixedCartanReactionContact_coframe_one]
    simp [identityZeroJet, affineCoframeFieldOfJet,
      coframeJetAffineComponentLinear]
  rw [coframeEquality]
  exact
    holonomicCoframeFirstJetAt_firstAndSecondJet_origin
      identityZeroJet increment

private theorem fixedCartanReactionContact_connection_eq_actionNative
    (space : StageNineSpatialPoint) :
    (fixedCartanReactionContact space).gravityConnection =
      fun point =>
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          (fixedCartanReactionContact space) point := by
  funext point
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection_selfGenerated
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState space point

private theorem fixedCartanReactionContact_smooth
    (space : StageNineSpatialPoint) :
    (fixedCartanReactionContact space).Smooth := by
  unfold fixedCartanReactionContact
  apply
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_smooth
  rw [fixedCurrent_coframe_one]
  norm_num

private theorem
    fixedIdentityECLeviCivitaCurvatureIncrement_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      identityECLeviCivitaCurvatureOfCoframeHessian
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
          positiveSmoothUnifiedSource
          (fixedCartanReactionContact space))
        internal spacetime := by
  have hessianCoordinateSmooth :=
    fixedIdentityECHessianIncrement_coordinate_contDiff
  unfold identityECLeviCivitaCurvatureOfCoframeHessian
    identityECLeviCivitaSpinConnectionFirstJet
    identityECCoframeMetricHessian
  fun_prop

private theorem fixedIdentityECHessianActual_curvature_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      holonomicGravityCurvature
        (fixedIdentityECHessianActual space) 0 internal spacetime := by
  rw [show
    (fun space =>
      holonomicGravityCurvature
        (fixedIdentityECHessianActual space) 0 internal spacetime) =
    fun space =>
      holonomicGravityCurvature
          (fixedCartanReactionContact space) 0 internal spacetime +
        identityECLeviCivitaCurvatureOfCoframeHessian
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            positiveSmoothUnifiedSource
            (fixedCartanReactionContact space))
          internal spacetime by
    funext space
    have actual :=
      sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_curvature_origin
        positiveSmoothUnifiedSource (fixedCartanReactionContact space)
        (fixedCartanReactionContact_smooth space)
    exact congrFun (congrFun actual internal) spacetime]
  exact
    (fixedCartanReactionGravityCurvature_component_contDiff
      internal spacetime).add
      (fixedIdentityECLeviCivitaCurvatureIncrement_component_contDiff
        internal spacetime)

private theorem
    fixedIdentityECHessianCartanCurrent_curvature_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      holonomicGravityCurvature
        (fixedIdentityECHessianCartanCurrent space) 0 internal spacetime := by
  rw [show
    (fun space =>
      holonomicGravityCurvature
        (fixedIdentityECHessianCartanCurrent space) 0 internal spacetime) =
    fun space =>
      holonomicGravityCurvature
        (fixedIdentityECHessianActual space) 0 internal spacetime by
    funext space
    have actual :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_curvature_origin
        positiveSmoothUnifiedSource
        (fixedCartanReactionContact space)
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
          positiveSmoothUnifiedSource
          (fixedCartanReactionContact space))
        (fixedCartanReactionContact_coframe_eq_one space)
        (fixedCartanReactionContact_smooth space)
        (fixedCartanReactionContact_connection_eq_actionNative space)
    exact congrFun (congrFun actual internal) spacetime]
  exact
    fixedIdentityECHessianActual_curvature_component_contDiff
      internal spacetime

private theorem fixedIdentityECHessianCartanCurrent_connection_origin
    (space : StageNineSpatialPoint) :
    (fixedIdentityECHessianCartanCurrent space).gravityConnection 0 =
      (fixedCartanReactionContact space).gravityConnection 0 := by
  unfold fixedIdentityECHessianCartanCurrent
    diracDualFormNativeIdentityECHessianCartanCurrent
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
      positiveSmoothUnifiedSource
      (fixedCartanReactionContact space)
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource (fixedCartanReactionContact space))
      (fixedCartanReactionContact_coframe_eq_one space)
      (fixedCartanReactionContact_connection_eq_actionNative space),
    identityECHolonomicCoframeHessianIncrementLocalActualLift_connection_origin]

/-- The final KIN-14 contact family has one spatially constant connection
origin.  The equality follows from the fixed P506/L0 W13 fields and the
origin-preservation of the Hessian, Cartan restart, and EC-normal writes; no
curvature or derivative receipt is transported. -/
theorem
    fixedIdentityECHessianCartanECNormalContactActual_connection_origin_eq
    (space : StageNineSpatialPoint) :
    (fixedIdentityECHessianCartanECNormalContactActual space).gravityConnection
        0 =
      (fixedIdentityECHessianCartanECNormalContactActual 0).gravityConnection
        0 := by
  calc
    (fixedIdentityECHessianCartanECNormalContactActual space).gravityConnection
          0 =
        (fixedIdentityECHessianCartanCurrent space).gravityConnection 0 := by
      exact
        sourceActionGeneratedDiracDualECNormalLocalActualLift_connection_zero
          positiveSmoothUnifiedSource
          (fixedIdentityECHessianCartanCurrent space)
    _ = (fixedCartanReactionContact space).gravityConnection 0 :=
      fixedIdentityECHessianCartanCurrent_connection_origin space
    _ =
        sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          space 0 := rfl
    _ =
        sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState
          0 0 :=
      fixedJointCartanConnection_origin_eq space
    _ = (fixedCartanReactionContact 0).gravityConnection 0 := rfl
    _ = (fixedIdentityECHessianCartanCurrent 0).gravityConnection 0 :=
      (fixedIdentityECHessianCartanCurrent_connection_origin 0).symm
    _ =
        (fixedIdentityECHessianCartanECNormalContactActual 0).gravityConnection
          0 := by
      exact
        (sourceActionGeneratedDiracDualECNormalLocalActualLift_connection_zero
          positiveSmoothUnifiedSource
          (fixedIdentityECHessianCartanCurrent 0)).symm

private theorem
    fixedIdentityECHessianCartanCurrent_connection_origin_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      (fixedIdentityECHessianCartanCurrent space).gravityConnection 0
        formDirection internalOut internalIn := by
  rw [show
    (fun space =>
      (fixedIdentityECHessianCartanCurrent space).gravityConnection 0
        formDirection internalOut internalIn) =
    fun space =>
      (fixedCartanReactionContact space).gravityConnection 0
        formDirection internalOut internalIn by
    funext space
    exact congrFun
      (congrFun
        (congrFun
          (fixedIdentityECHessianCartanCurrent_connection_origin space)
          formDirection)
        internalOut)
      internalIn]
  simpa only [fixedCartanReactionContact,
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection,
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection]
    using fixedJointCartanConnection_origin_component_contDiff
      formDirection internalOut internalIn

private theorem fixedIdentityECHessianCartan_nonGravityProjection_eq
    (space : StageNineSpatialPoint) :
    identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField
          (fixedIdentityECHessianCartanCurrent space)) =
      identityECNonGravityContactProjection
        (fixedECContactField space) := by
  have cartanPrepared :
      diracDualFormNativeECNormalPreparedActual
          (fixedIdentityECHessianCartanCurrent space) =
        fixedIdentityECHessianCartanCurrent space :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        positiveSmoothUnifiedSource (fixedIdentityECHessianActual space))
  have basePrepared :
      diracDualFormNativeECNormalPreparedActual
          (fixedCartanReactionContact space) =
        fixedCartanReactionContact space :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift_simplicity
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState space)
  unfold fixedECContactField diracDualFormNativeECNormalContactField
  rw [cartanPrepared, basePrepared]
  apply StageNineContinuumPointField.ext
  · change
      (fixedIdentityECHessianCartanCurrent space).coframe 0 =
        (fixedCartanReactionContact space).coframe 0
    unfold fixedIdentityECHessianCartanCurrent
      diracDualFormNativeIdentityECHessianCartanCurrent
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
    unfold sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
    exact
      identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin
        (fixedCartanReactionContact space)
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
          positiveSmoothUnifiedSource (fixedCartanReactionContact space))
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    change
      holonomicMatterCovariantDerivative
          (fixedIdentityECHessianCartanCurrent space) 0 direction =
        holonomicMatterCovariantDerivative
          (fixedCartanReactionContact space) 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [fixedIdentityECHessianCartanCurrent_connection_origin]
    rfl
  · rfl

private theorem fixedIdentityECHessianCartan_gaugeEuler_eq
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource
        (diracDualFormNativeECNormalContactField
          (fixedIdentityECHessianCartanCurrent space)) =
      diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource (fixedECContactField space) := by
  let nextField :=
    diracDualFormNativeECNormalContactField
      (fixedIdentityECHessianCartanCurrent space)
  let baseField := fixedECContactField space
  have projected :
      identityECNonGravityContactProjection nextField =
        identityECNonGravityContactProjection baseField :=
    fixedIdentityECHessianCartan_nonGravityProjection_eq space
  have densityEquality :
      diracDualFormNativeCoframeGaugeDensity
          positiveSmoothUnifiedSource nextField =
        diracDualFormNativeCoframeGaugeDensity
          positiveSmoothUnifiedSource baseField := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        positiveSmoothUnifiedSource nextField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        positiveSmoothUnifiedSource baseField]
  have coframeEquality : nextField.coframe = baseField.coframe := by
    simpa [identityECNonGravityContactProjection] using
      congrArg (fun field : StageNineContinuumPointField => field.coframe)
        projected
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  change
    fderiv ℝ
        (diracDualFormNativeCoframeGaugeDensity
          positiveSmoothUnifiedSource nextField)
        nextField.coframe =
      fderiv ℝ
        (diracDualFormNativeCoframeGaugeDensity
          positiveSmoothUnifiedSource baseField)
        baseField.coframe
  rw [densityEquality, coframeEquality]

private theorem fixedIdentityECHessianCartan_matterEuler_eq
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0
        (diracDualFormNativeECNormalContactField
          (fixedIdentityECHessianCartanCurrent space)) =
      diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0 (fixedECContactField space) := by
  let nextField :=
    diracDualFormNativeECNormalContactField
      (fixedIdentityECHessianCartanCurrent space)
  let baseField := fixedECContactField space
  have projected :
      identityECNonGravityContactProjection nextField =
        identityECNonGravityContactProjection baseField :=
    fixedIdentityECHessianCartan_nonGravityProjection_eq space
  have densityEquality :
      diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 nextField =
        diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 baseField := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        positiveSmoothUnifiedSource 0 nextField,
      projected,
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        positiveSmoothUnifiedSource 0 baseField]
  have coframeEquality : nextField.coframe = baseField.coframe := by
    simpa [identityECNonGravityContactProjection] using
      congrArg (fun field : StageNineContinuumPointField => field.coframe)
        projected
  unfold diracDualFormNativeCoframeMatterEulerCovector
  change
    fderiv ℝ
        (diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 nextField)
        nextField.coframe =
      fderiv ℝ
        (diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 baseField)
        baseField.coframe
  rw [densityEquality, coframeEquality]

private theorem fixedIdentityECHessianCartan_load_eq
    (space : StageNineSpatialPoint) :
    diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedIdentityECHessianCartanCurrent space) =
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedCartanReactionContact space) := by
  unfold diracDualFormNativeIdentityECLoad
  rw [fixedIdentityECHessianCartan_gaugeEuler_eq,
    fixedIdentityECHessianCartan_matterEuler_eq]
  rfl

private theorem fixedIdentityECHessianCartan_load_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedIdentityECHessianCartanCurrent space)
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun space =>
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedIdentityECHessianCartanCurrent space)
        (coframeCoordinateDirection row column)) =
    fun space =>
      diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        (fixedCartanReactionContact space)
        (coframeCoordinateDirection row column) by
    funext space
    rw [fixedIdentityECHessianCartan_load_eq]]
  exact fixedIdentityECLoad_coordinate_contDiff row column

private theorem fixedIdentityECHessianCartan_prepared_eq
    (space : StageNineSpatialPoint) :
    diracDualFormNativeECNormalPreparedActual
        (fixedIdentityECHessianCartanCurrent space) =
      fixedIdentityECHessianCartanCurrent space :=
  (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
    _).2
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
      positiveSmoothUnifiedSource (fixedIdentityECHessianActual space))

private def fixedIdentityECHessianCartanCurvatureObservationCoordinates
    (space : StageNineSpatialPoint) : LorentzianCoframe :=
  coframeCovectorCoordinates
    (identityDiracDualECCurvatureObservation
      (holonomicGravityCurvature
        (fixedIdentityECHessianCartanCurrent space) 0))

private theorem
    fixedIdentityECHessianCartanCurvatureObservationCoordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ fun space =>
      fixedIdentityECHessianCartanCurvatureObservationCoordinates
        space row column := by
  unfold fixedIdentityECHessianCartanCurvatureObservationCoordinates
    coframeCovectorCoordinates
  have curvatureSmooth : ContDiff ℝ ∞ fun space =>
      holonomicGravityCurvature
        (fixedIdentityECHessianCartanCurrent space) 0 := by
    apply contDiff_pi'
    intro internal
    apply contDiff_pi'
    intro spacetime
    exact
      fixedIdentityECHessianCartanCurrent_curvature_component_contDiff
        internal spacetime
  change ContDiff ℝ ∞
    ((fixedECCurvatureObservationCoordinateLinear row column) ∘
      fun space =>
        holonomicGravityCurvature
          (fixedIdentityECHessianCartanCurrent space) 0)
  exact
    (fixedECCurvatureObservationCoordinateLinear row column)
      |>.toContinuousLinearMap.contDiff.comp curvatureSmooth

private theorem
    fixedIdentityECHessianCartanCurvatureObservationCoordinates_contDiff :
    ContDiff ℝ ∞
      fixedIdentityECHessianCartanCurvatureObservationCoordinates := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact
    fixedIdentityECHessianCartanCurvatureObservationCoordinate_contDiff
      row column

private def fixedIdentityECHessianCartanLoadCoordinates
    (space : StageNineSpatialPoint) : LorentzianCoframe :=
  coframeCovectorCoordinates
    (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
      (fixedIdentityECHessianCartanCurrent space))

private theorem fixedIdentityECHessianCartanLoadCoordinates_contDiff :
    ContDiff ℝ ∞ fixedIdentityECHessianCartanLoadCoordinates := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact
    fixedIdentityECHessianCartan_load_coordinate_contDiff row column

private def identityECNormalSectionOfCoordinates
    (coordinates : LorentzianCoframe) : PhysicalBivector :=
  gravityInternalPairVarianceNormalization
    (linearPlebanskiMultiplierOfCoframeResponse
      (linearPlebanskiTraceReverse coordinates))

private theorem identityECNormalSectionOfCoordinates_component_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (coordinates : E → LorentzianCoframe)
    (coordinatesSmooth : ContDiff ℝ ∞ coordinates)
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      identityECNormalSectionOfCoordinates (coordinates point)
        internal spacetime := by
  simp only [identityECNormalSectionOfCoordinates,
    gravityInternalPairVarianceNormalization_apply]
  unfold
    linearPlebanskiMultiplierOfCoframeResponse
    linearPlebanskiTraceReverse
    physicalIIPlusCoframeTangent coframeWedgeTangent
  simp only [Matrix.of_apply]
  fin_cases internal <;>
    simp [internalBivectorDual, lorentzianCoframeHodge] <;>
    fun_prop

private theorem fixedECNormalCurvatureTarget_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun space =>
      diracDualFormNativeECNormalCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedIdentityECHessianCartanCurrent space)
        internal spacetime := by
  rw [show
    (fun space =>
      diracDualFormNativeECNormalCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedIdentityECHessianCartanCurrent space)
        internal spacetime) =
    fun space =>
      holonomicGravityCurvature
          (fixedIdentityECHessianCartanCurrent space) 0
          internal spacetime -
        identityECNormalSectionOfCoordinates
            (-fixedIdentityECHessianCartanCurvatureObservationCoordinates
              space) internal spacetime +
        identityECNormalSectionOfCoordinates
            (fixedIdentityECHessianCartanLoadCoordinates space)
          internal spacetime by
    funext space
    unfold diracDualFormNativeECNormalCurvatureTarget
      identityDiracDualECCurvatureTarget
      identityDiracDualECCurvatureKernelPart
      identityDiracDualECCurvatureNormalSection
      identityECNormalSectionOfCoordinates
      linearPlebanskiCoframeResponseOfStress
      fixedIdentityECHessianCartanCurvatureObservationCoordinates
      fixedIdentityECHessianCartanLoadCoordinates
    rw [fixedIdentityECHessianCartan_prepared_eq]
    simp [coframeCovectorCoordinates_neg]]
  exact
    (fixedIdentityECHessianCartanCurrent_curvature_component_contDiff
      internal spacetime).sub
      (identityECNormalSectionOfCoordinates_component_contDiff
        (fun space =>
          -fixedIdentityECHessianCartanCurvatureObservationCoordinates space)
        fixedIdentityECHessianCartanCurvatureObservationCoordinates_contDiff.neg
        internal spacetime)
      |>.add
        (identityECNormalSectionOfCoordinates_component_contDiff
          fixedIdentityECHessianCartanLoadCoordinates
          fixedIdentityECHessianCartanLoadCoordinates_contDiff
          internal spacetime)

/-! ## Explicit joint normal form of the final contact family -/

private theorem fixedBasePoint_eq_sum_coordinateDirections
    (point : BasePoint) :
    point =
      ∑ direction : LorentzianIndex,
        point direction • coordinateDirection direction := by
  ext coordinate
  fin_cases coordinate <;>
    simp [coordinateDirection, Fin.sum_univ_four]

private theorem fixedCoframeHessian_expand_first
    (hessian : CoframeHolonomicSecondJet)
    (point second : BasePoint)
    (internal coordinate : LorentzianIndex) :
    hessian.1 point second internal coordinate =
      ∑ direction : LorentzianIndex,
        point direction *
          hessian.1 (coordinateDirection direction) second
            internal coordinate := by
  conv_lhs => rw [fixedBasePoint_eq_sum_coordinateDirections point]
  rw [map_sum]
  simp_rw [ContinuousLinearMap.map_smul, sum_apply, smul_apply]
  rfl

private theorem fixedCoframeHessian_expand_second
    (hessian : CoframeHolonomicSecondJet)
    (first point : BasePoint)
    (internal coordinate : LorentzianIndex) :
    hessian.1 first point internal coordinate =
      ∑ direction : LorentzianIndex,
        point direction *
          hessian.1 first (coordinateDirection direction)
            internal coordinate := by
  conv_lhs => rw [fixedBasePoint_eq_sum_coordinateDirections point]
  rw [map_sum]
  simp_rw [ContinuousLinearMap.map_smul]
  change
    ((∑ direction : LorentzianIndex,
        point direction •
          hessian.1 first (coordinateDirection direction)) :
        LorentzianCoframe) internal coordinate =
      ∑ direction : LorentzianIndex,
        point direction *
          hessian.1 first (coordinateDirection direction)
            internal coordinate
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

private theorem fixedCoframeHessian_expand_both
    (hessian : CoframeHolonomicSecondJet)
    (point : BasePoint)
    (internal coordinate : LorentzianIndex) :
    hessian.1 point point internal coordinate =
      ∑ first : LorentzianIndex,
        point first *
          ∑ second : LorentzianIndex,
            point second *
              hessian.1 (coordinateDirection first)
                (coordinateDirection second) internal coordinate := by
  rw [fixedCoframeHessian_expand_first]
  apply Finset.sum_congr rfl
  intro first _
  rw [fixedCoframeHessian_expand_second]

private theorem fixedIdentityECHessianQuadratic_coordinate_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      coframeHolonomicSecondJetQuadraticRealization
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            positiveSmoothUnifiedSource
            (fixedCartanReactionContact joint.1))
          joint.2 internal coordinate := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      coframeHolonomicSecondJetQuadraticRealization
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            positiveSmoothUnifiedSource
            (fixedCartanReactionContact joint.1))
          joint.2 internal coordinate) =
    fun joint =>
      (1 / 2 : ℝ) *
        ∑ first : LorentzianIndex,
          joint.2 first *
            ∑ second : LorentzianIndex,
              joint.2 second *
                (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
                  positiveSmoothUnifiedSource
                  (fixedCartanReactionContact joint.1)).1
                    (coordinateDirection first)
                    (coordinateDirection second)
                    internal coordinate by
    funext joint
    simp only [coframeHolonomicSecondJetQuadraticRealization_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [fixedCoframeHessian_expand_both]]
  apply contDiff_const.mul
  apply ContDiff.sum
  intro first _
  have firstCoordinateSmooth :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        joint.2 first := by
    fun_prop
  apply firstCoordinateSmooth.mul
  apply ContDiff.sum
  intro second _
  have secondCoordinateSmooth :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        joint.2 second := by
    fun_prop
  exact secondCoordinateSmooth.mul
    ((fixedIdentityECHessianIncrement_coordinate_contDiff
      first second internal coordinate).comp contDiff_fst)

theorem
    fixedIdentityECHessianCartanECNormalContactActual_coframe_component_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1).coframe
        joint.2 internal coordinate := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1).coframe
        joint.2 internal coordinate) =
    fun joint =>
      (fixedCartanReactionContact joint.1).coframe joint.2
          internal coordinate +
        coframeHolonomicSecondJetQuadraticRealization
            (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
              positiveSmoothUnifiedSource
              (fixedCartanReactionContact joint.1))
            joint.2 internal coordinate by
    funext joint
    rfl]
  exact
    (fixedCartanReactionCoframeCoordinate_contDiff internal coordinate).add
      (fixedIdentityECHessianQuadratic_coordinate_contDiff
        internal coordinate)

theorem
    fixedIdentityECHessianCartanECNormalContactActual_coframe_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1).coframe
        joint.2 := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact
    fixedIdentityECHessianCartanECNormalContactActual_coframe_component_contDiff
      internal coordinate

theorem
    fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.gravityConnection joint.2 formDirection internalOut internalIn := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.gravityConnection joint.2 formDirection internalOut internalIn) =
    fun joint =>
      normalizedAffineLorentzConnectionField
          ((fixedIdentityECHessianCartanCurrent joint.1).gravityConnection 0)
          (diracDualFormNativeECNormalCurvatureTarget
            positiveSmoothUnifiedSource
            (fixedIdentityECHessianCartanCurrent joint.1))
          joint.2 formDirection internalOut internalIn by
    funext joint
    rfl]
  have originSmooth :
      ∀ direction out inn,
        ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
          (fixedIdentityECHessianCartanCurrent joint.1).gravityConnection 0
            direction out inn := by
    intro direction out inn
    exact
      (fixedIdentityECHessianCartanCurrent_connection_origin_component_contDiff
        direction out inn).comp contDiff_fst
  have targetSmooth :
      ∀ internal spacetime,
        ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
          diracDualFormNativeECNormalCurvatureTarget
              positiveSmoothUnifiedSource
              (fixedIdentityECHessianCartanCurrent joint.1)
              internal spacetime := by
    intro internal spacetime
    exact
      (fixedECNormalCurvatureTarget_component_contDiff
        internal spacetime).comp contDiff_fst
  unfold normalizedAffineLorentzConnectionField
    lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
    normalizedAffineBivectorOneForm
    normalizedAffineBivectorComponentLinear
    normalizedDerivativeBivector
    originLorentzBracketCurvature
  fun_prop

theorem
    fixedIdentityECHessianCartanECNormalContactActual_auxiliary_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.gravityAuxiliary joint.2 := by
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    physicalIIPlusBivector
      ((fixedIdentityECHessianCartanECNormalContactActual joint.1).coframe
        joint.2)
  exact
    StageNineIIPlusRestriction.physicalIIPlusBivector_contDiff.comp
      fixedIdentityECHessianCartanECNormalContactActual_coframe_contDiff

private theorem
    fixedIdentityECHessianCartanECNormalContactActual_connectionDerivative_contDiff
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      gravityConnectionDerivative
        (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        joint.2 derivativeDirection formDirection internalOut internalIn := by
  let coordinate : StageNineSpatialPoint → BasePoint → ℝ :=
    fun space point =>
      (fixedIdentityECHessianCartanECNormalContactActual space)
        |>.gravityConnection point formDirection internalOut internalIn
  have coordinateJointSmooth :
      ContDiff ℝ ∞ (Function.uncurry coordinate) := by
    exact
      fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
        formDirection internalOut internalIn
  have extendedFamilySmooth :
      ContDiff ℝ ∞
        (Function.uncurry fun joint : StageNineSpatialPoint × BasePoint =>
          fun point : BasePoint => coordinate joint.1 point) := by
    change ContDiff ℝ ∞ fun pair :
        (StageNineSpatialPoint × BasePoint) × BasePoint =>
      coordinate pair.1.1 pair.2
    exact coordinateJointSmooth.comp
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have derivativeSmooth :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        fderiv ℝ (coordinate joint.1) joint.2 := by
    simpa only [Function.uncurry_apply_pair] using
      extendedFamilySmooth.fderiv contDiff_snd (by simp)
  unfold gravityConnectionDerivative
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    fderiv ℝ (coordinate joint.1) joint.2
      (coordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

private theorem
    fixedIdentityECHessianCartanECNormalContactActual_curvature_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      holonomicGravityCurvature
        (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        joint.2 internal spacetime := by
  unfold holonomicGravityCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact
        fixedIdentityECHessianCartanECNormalContactActual_connectionDerivative_contDiff
          (pairFirst spacetime) (pairSecond spacetime)
          (pairFirst internal) (pairSecond internal)
    · exact
        fixedIdentityECHessianCartanECNormalContactActual_connectionDerivative_contDiff
          (pairSecond spacetime) (pairFirst spacetime)
          (pairFirst internal) (pairSecond internal)
  · apply ContDiff.sum
    intro middle _
    exact
      ((fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
          (pairFirst spacetime) (pairFirst internal) middle).mul
        (fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
          (pairSecond spacetime) middle (pairSecond internal))).sub
      ((fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
          (pairSecond spacetime) (pairFirst internal) middle).mul
        (fixedIdentityECHessianCartanECNormalContactActual_connection_component_contDiff
          (pairFirst spacetime) middle (pairSecond internal)))

theorem
    fixedIdentityECHessianCartanECNormalContactActual_multiplier_component_contDiff
    (internal spacetime : Fin 6) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.gravitySimplicityMultiplier joint.2 internal spacetime := by
  rw [show
    (fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.gravitySimplicityMultiplier joint.2 internal spacetime) =
    fun joint =>
      gravityInternalDualEquiv
          ((fixedIdentityECHessianCartanECNormalContactActual joint.1)
            |>.gravityAuxiliary joint.2) internal spacetime -
        holonomicContravariantGravityCurvature
            (fixedIdentityECHessianCartanECNormalContactActual joint.1)
            joint.2 internal spacetime by
    funext joint
    rfl]
  have dualSmooth :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        gravityInternalDualEquiv
          ((fixedIdentityECHessianCartanECNormalContactActual joint.1)
            |>.gravityAuxiliary joint.2) := by
    change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      gravityInternalDualLinear
        ((fixedIdentityECHessianCartanECNormalContactActual joint.1)
          |>.gravityAuxiliary joint.2)
    exact
      gravityInternalDualLinear.toContinuousLinearMap.contDiff.comp
        fixedIdentityECHessianCartanECNormalContactActual_auxiliary_contDiff
  have curvatureSmooth :
      ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
        holonomicContravariantGravityCurvature
            (fixedIdentityECHessianCartanECNormalContactActual joint.1)
            joint.2 internal spacetime := by
    exact contDiff_const.mul
      (fixedIdentityECHessianCartanECNormalContactActual_curvature_component_contDiff
        internal spacetime)
  exact
    (contDiff_pi.mp (contDiff_pi.mp dualSmooth internal) spacetime).sub
      curvatureSmooth

theorem
    fixedIdentityECHessianCartanECNormalContactActual_gaugeConnection_contDiff
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((fixedIdentityECHessianCartanECNormalContactActual joint.1)
          |>.gaugeConnection joint.2 formDirection) := by
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    p286CoordinateEquiv
      ((fixedCartanReactionContact joint.1).gaugeConnection
        joint.2 formDirection)
  exact fixedCartanReactionGaugeConnectionCoordinate_contDiff formDirection

theorem
    fixedIdentityECHessianCartanECNormalContactActual_gaugeAuxiliary_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      p286CoordinateEquiv
        ((fixedIdentityECHessianCartanECNormalContactActual joint.1)
          |>.gaugeAuxiliary joint.2 pair) := by
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    p286CoordinateEquiv
      ((fixedCartanReactionContact joint.1).gaugeAuxiliary joint.2 pair)
  exact fixedCartanReactionGaugeAuxiliaryCoordinate_contDiff pair

theorem
    fixedIdentityECHessianCartanECNormalContactActual_scalar_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.scalar joint.2 := by
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    (fixedCartanReactionContact joint.1).scalar joint.2
  exact fixedCartanReactionScalar_contDiff

/-- The final gravity writes definitionally retain the fixed source-generated
vacuum scalar.  This point-free form is the derivative authority used by the
complete Cauchy readout. -/
theorem fixedIdentityECHessianCartanECNormalContactActual_scalar_vacuum
    (space : StageNineSpatialPoint) :
    (fixedIdentityECHessianCartanECNormalContactActual space).scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  change
    (fixedCartanReactionContact space).scalar point =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  exact fixedCartanReactionContact_scalar space point

theorem
    fixedIdentityECHessianCartanECNormalContactActual_matter_contDiff :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      matterCoordinateEquiv
        ((fixedIdentityECHessianCartanECNormalContactActual joint.1)
          |>.matter joint.2) := by
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    matterCoordinateEquiv
      ((fixedCartanReactionContact joint.1).matter joint.2)
  exact fixedCartanReactionMatterCoordinates_contDiff

theorem
    fixedIdentityECHessianCartanECNormalContactActual_conjugateMatter_contDiff
    (matter : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
      (fixedIdentityECHessianCartanECNormalContactActual joint.1)
        |>.conjugateMatter joint.2 matter := by
  change ContDiff ℝ ∞ fun joint : StageNineSpatialPoint × BasePoint =>
    (fixedCartanReactionContact joint.1).conjugateMatter joint.2 matter
  exact fixedCartanReactionConjugateMatter_apply_contDiff matter

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
