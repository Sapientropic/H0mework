import H0mework.Physics.JointVariation.GeneratedProfilesFixedRegularity
import H0mework.Physics.JointVariation.P286RequiredExteriorProfileNaturality
import H0mework.Physics.GaugeAction.P286GaugeConnectionAlgebraicCurrentRegularity
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Fixed P506/L0 required P286 exterior-derivative spatial regularity

The complete P286 action writer reads one required exterior derivative from
each spatially recentered fixed P506/L0 contact.  This module proves that
fixed-lineage profile smooth by reducing its charged-current coordinate to
the existing action-sector regularity and its connection action to the
already generated origin auxiliary.

No arbitrary current, residual coordinate, target field, equation receipt,
branch, or zero-fiber certificate is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286RequiredExteriorDerivativeSpatialRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeScalarMatterRegularity
open StageNineConnectionSectorSourceBalance
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open
  StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance requiredExteriorRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance requiredExteriorRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance requiredExteriorRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- A globally nondegenerate comparison carrier for the fixed zero-slice
charged current.  Only its coframe is replaced by the already proved
zero-slice value `1`; every action field read by the current remains the
fixed P506/L0 field. -/
private def fixedP506L0RequiredExteriorChargedComparison :
    StageNineHolonomicConfiguration :=
  { FixedInput with coframe := fun _ => 1 }

private theorem fixedP506L0RequiredExteriorChargedComparison_smooth :
    fixedP506L0RequiredExteriorChargedComparison.Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact contDiff_const
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.1
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
  · exact
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
  · exact
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.2

private theorem fixedP506L0RequiredExteriorChargedComparison_nondegenerate :
    fixedP506L0RequiredExteriorChargedComparison.Nondegenerate := by
  intro point
  change Matrix.det (1 : LorentzianCoframe) ≠ 0
  norm_num

private theorem fixedP506L0RequiredExteriorChargedCoefficient_contDiff
    (direction : P286GaugeOneForm) :
    ContDiff ℝ ∞ fun point =>
      formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
        point
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison point)
        direction := by
  rw [show
    (fun point =>
      formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
        point
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison point)
        direction) =
      fun point =>
        p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
            fixedP506L0RequiredExteriorChargedComparison direction point +
          p286MatterCurrentCoefficient positiveSmoothUnifiedSource
            fixedP506L0RequiredExteriorChargedComparison direction point by
    funext point
    unfold formNativeChargedGaugeFirstCoefficient
      p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
    rw [← pointwiseScalarP286GaugeConnectionVariation_actual
      fixedP506L0RequiredExteriorChargedComparison (fun _ => direction) point,
      ← pointwiseMatterP286GaugeConnectionVariation_actual
        fixedP506L0RequiredExteriorChargedComparison
        (fun _ => direction) point]
    ring]
  exact
    (p286ScalarCurrentCoefficient_contDiff positiveSmoothUnifiedSource
      fixedP506L0RequiredExteriorChargedComparison
      fixedP506L0RequiredExteriorChargedComparison_smooth
      fixedP506L0RequiredExteriorChargedComparison_nondegenerate
      direction).add
      (p286MatterCurrentCoefficient_contDiff positiveSmoothUnifiedSource
        fixedP506L0RequiredExteriorChargedComparison
        fixedP506L0RequiredExteriorChargedComparison_smooth
        fixedP506L0RequiredExteriorChargedComparison_nondegenerate
        direction)

private theorem fixedP506L0RequiredExteriorChargedThreeForm_contDiff :
    ContDiff ℝ ∞ fun point =>
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison point) := by
  let basis := Module.finBasis ℝ P286GaugeOneForm
  let coordinates := fun point =>
    basis.dualBasis.equivFun
      (formNativeChargedGaugeFirstLinearMap positiveSmoothUnifiedSource 0
        point
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison point))
  have coordinatesSmooth : ContDiff ℝ ∞ coordinates := by
    apply contDiff_pi'
    intro index
    rw [show (fun point => coordinates point index) =
      fun point =>
        formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (toContinuumPointField
            fixedP506L0RequiredExteriorChargedComparison point)
          (basis index) by
      funext point
      exact basis.dualBasis_equivFun _ index]
    exact fixedP506L0RequiredExteriorChargedCoefficient_contDiff (basis index)
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286GaugeThreeFormWedgeEquiv.symm
  let reconstructCLM :
      (Fin (Module.finrank ℝ P286GaugeOneForm) → ℝ) →L[ℝ]
        P286GaugeThreeForm :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  have reconstructedSmooth : ContDiff ℝ ∞ fun point =>
      reconstructCLM (coordinates point) :=
    reconstructCLM.contDiff.comp coordinatesSmooth
  rw [show
    (fun point => reconstructCLM (coordinates point)) =
      fun point =>
        p286GaugeThreeFormWedgeEquiv.symm
          (formNativeChargedGaugeFirstLinearMap positiveSmoothUnifiedSource 0
            point
            (toContinuumPointField
              fixedP506L0RequiredExteriorChargedComparison point)) by
    funext point
    change reconstruct (coordinates point) =
      p286GaugeThreeFormWedgeEquiv.symm
        (formNativeChargedGaugeFirstLinearMap positiveSmoothUnifiedSource 0
          point
          (toContinuumPointField
            fixedP506L0RequiredExteriorChargedComparison point))
    unfold reconstruct coordinates
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]] at reconstructedSmooth
  exact reconstructedSmooth

private theorem
    fixedP506L0RequiredExteriorPhysicalChargedThreeForm_contDiff :
    ContDiff ℝ ∞ fun point =>
      formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 point
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison point) := by
  unfold formNativePhysicalChargedGaugeCurrentThreeForm
  exact fixedP506L0RequiredExteriorChargedThreeForm_contDiff.neg

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold canonicalSpatialContactTranslation
  exact add_zero _

private theorem
    fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation_local
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ field
      (canonicalSpatialContactTranslation space point)) :
    fieldDirectionalDerivative
        (field ∘ canonicalSpatialContactTranslation space) point direction =
      fieldDirectionalDerivative field
        (canonicalSpatialContactTranslation space point) direction := by
  have translation :
      HasFDerivAt (canonicalSpatialContactTranslation space)
        (ContinuousLinearMap.id ℝ BasePoint) point := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have composed := differentiable.hasFDerivAt.comp point translation
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  simp

private theorem fixedP506L0RequiredExterior_coframe_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedScalarSecondJetActual space).coframe 0 =
      fixedP506L0RequiredExteriorChargedComparison.coframe
        (canonicalCauchySlicePoint 0 space) := by
  change
    (recenteredCartanRepairedScalarSecondJetActual space).coframe 0 = 1
  unfold recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_coframe]
  exact recenteredCartanRepairedConstitutiveCurrent_coframe_origin space

private theorem fixedP506L0RequiredExterior_scalar_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedScalarSecondJetActual space).scalar 0 =
      fixedP506L0RequiredExteriorChargedComparison.scalar
        (canonicalCauchySlicePoint 0 space) := by
  unfold recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_scalar_origin,
    recenteredCartanRepairedConstitutiveCurrent_scalar]
  change
    FixedInput.scalar (canonicalSpatialContactTranslation space 0) =
      FixedInput.scalar (canonicalCauchySlicePoint 0 space)
  rw [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedP506L0RequiredExterior_scalarCovariantDerivative_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        (recenteredCartanRepairedScalarSecondJetActual space) 0 =
      holonomicScalarCovariantDerivative
        fixedP506L0RequiredExteriorChargedComparison
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicScalarCovariantDerivative
          (recenteredCartanRepairedScalarSecondJetActual space) 0 =
        holonomicScalarCovariantDerivative
          (recenteredCartanRepairedConstitutiveCurrent space) 0 := by
      exact congrArg StageNineContinuumPointField.scalarCovariantDerivative
        (recenteredCartanRepairedScalarSecondJetActual_pointField_origin space)
    _ = holonomicScalarCovariantDerivative
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space) := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [recenteredCartanRepairedConstitutiveCurrent_scalar,
        recenteredCartanRepairedConstitutiveCurrent_gaugeConnection]
      change
        fieldDirectionalDerivative
              (FixedInput.scalar ∘
                canonicalSpatialContactTranslation space)
              0 direction +
            scalarMotherLieAction
              (p286LieBlockEmbed
                (FixedInput.gaugeConnection
                  (canonicalSpatialContactTranslation space 0) direction))
              (FixedInput.scalar
                (canonicalSpatialContactTranslation space 0)) =
          fieldDirectionalDerivative FixedInput.scalar
              (canonicalCauchySlicePoint 0 space) direction +
            scalarMotherLieAction
              (p286LieBlockEmbed
                (FixedInput.gaugeConnection
                  (canonicalCauchySlicePoint 0 space) direction))
              (FixedInput.scalar (canonicalCauchySlicePoint 0 space))
      rw [
        fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation_local
        FixedInput.scalar space 0 direction]
      · rw [canonicalSpatialContactTranslation_zero_local]
      · exact
          (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
            |>.differentiable (by simp)).differentiableAt

private theorem fixedP506L0RequiredExterior_matter_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedScalarSecondJetActual space).matter 0 =
      fixedP506L0RequiredExteriorChargedComparison.matter
        (canonicalCauchySlicePoint 0 space) := by
  calc
    (recenteredCartanRepairedScalarSecondJetActual space).matter 0 =
        (recenteredCartanRepairedConstitutiveCurrent space).matter 0 := by
      unfold recenteredCartanRepairedScalarSecondJetActual
      rw [installScalarQuadraticTimeCorrection_matter]
    _ = (fixedP506L0CartanRestartActual space).matter 0 :=
      recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan space
    _ = fixedP506L0RequiredExteriorChargedComparison.matter
          (canonicalCauchySlicePoint 0 space) := by
      unfold fixedP506L0CartanRestartActual fixedP506L0RecenteredInput
        fixedP506L0RequiredExteriorChargedComparison
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
      change
        FixedInput.matter (canonicalSpatialContactTranslation space 0) =
          FixedInput.matter (canonicalCauchySlicePoint 0 space)
      rw [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedP506L0RequiredExterior_conjugateMatter_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedScalarSecondJetActual space).conjugateMatter 0 =
      fixedP506L0RequiredExteriorChargedComparison.conjugateMatter
        (canonicalCauchySlicePoint 0 space) := by
  calc
    (recenteredCartanRepairedScalarSecondJetActual space).conjugateMatter 0 =
        (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter
          0 := by
      unfold recenteredCartanRepairedScalarSecondJetActual
      rw [installScalarQuadraticTimeCorrection_conjugateMatter]
    _ = (fixedP506L0CartanRestartActual space).conjugateMatter 0 :=
      recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan
        space
    _ = fixedP506L0RequiredExteriorChargedComparison.conjugateMatter
          (canonicalCauchySlicePoint 0 space) := by
      unfold fixedP506L0CartanRestartActual fixedP506L0RecenteredInput
        fixedP506L0RequiredExteriorChargedComparison
      rw [
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
      change
        FixedInput.conjugateMatter
            (canonicalSpatialContactTranslation space 0) =
          FixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space)
      rw [canonicalSpatialContactTranslation_zero_local]

private theorem fixedP506L0RequiredExterior_volume_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    generatedVolumeDensity
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0) =
      generatedVolumeDensity
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space)) := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fixedP506L0RequiredExterior_coframe_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_scalarGaugeKinetic_origin_eq_comparison
    (space : StageNineSpatialPoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0)
        variation =
      scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space))
        variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart_local]
  rw [fixedP506L0RequiredExterior_coframe_origin_eq_comparison,
    fixedP506L0RequiredExterior_scalarCovariantDerivative_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_pointwiseScalarGaugeVariation_origin_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0)
        direction =
      pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space))
        direction := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [fixedP506L0RequiredExterior_scalar_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_pointwiseMatterGaugeVariation_origin_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0)
        direction =
      pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space))
        direction := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [fixedP506L0RequiredExterior_matter_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_matterGaugeKinetic_origin_eq_comparison
    (space : StageNineSpatialPoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0)
        variation =
      matterGaugeConnectionFirstVariationDensity
        positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space))
        variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    matterDerivativeFrameRelative
  simp only [toContinuumPointField, matterFrameRelative_zeroChart_local,
    matterDualFrameRelative_zeroChart_local]
  rw [fixedP506L0RequiredExterior_coframe_origin_eq_comparison,
    fixedP506L0RequiredExterior_conjugateMatter_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_chargedGaugeThreeForm_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space)) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  simp only [formNativeChargedGaugeFirstLinearMap_apply]
  unfold formNativeChargedGaugeFirstCoefficient
  rw [fixedP506L0RequiredExterior_volume_origin_eq_comparison,
    fixedP506L0RequiredExterior_pointwiseScalarGaugeVariation_origin_eq_comparison,
    fixedP506L0RequiredExterior_pointwiseMatterGaugeVariation_origin_eq_comparison,
    fixedP506L0RequiredExterior_scalarGaugeKinetic_origin_eq_comparison,
    fixedP506L0RequiredExterior_matterGaugeKinetic_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_physicalChargedGaugeCurrent_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual space) 0) =
      formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space)) := by
  unfold formNativePhysicalChargedGaugeCurrentThreeForm
  rw [
    fixedP506L0RequiredExterior_chargedGaugeThreeForm_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_gaugeConnection_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedScalarSecondJetActual space).gaugeConnection 0 =
      fixedP506L0RequiredExteriorChargedComparison.gaugeConnection
        (canonicalCauchySlicePoint 0 space) := by
  unfold recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_gaugeConnection,
    recenteredCartanRepairedConstitutiveCurrent_gaugeConnection]
  unfold recenteredContactActual
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]
  change
    FixedInput.gaugeConnection
        (canonicalSpatialContactTranslation space 0) =
      FixedInput.gaugeConnection (canonicalCauchySlicePoint 0 space)
  rw [canonicalSpatialContactTranslation_zero_local]

private theorem
    fixedP506L0RequiredExterior_gaugeConnectionCoordinate_origin_eq_comparison
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeConnectionCoordinate
        (recenteredCartanRepairedScalarSecondJetActual space) 0 =
      holonomicP286GaugeConnectionCoordinate
        fixedP506L0RequiredExteriorChargedComparison
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [fixedP506L0RequiredExterior_gaugeConnection_origin_eq_comparison]

private theorem
    fixedP506L0RequiredExterior_comparisonGaugeConnection_contDiff :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      holonomicP286GaugeConnectionCoordinate
        fixedP506L0RequiredExteriorChargedComparison
        (canonicalCauchySlicePoint 0 space) := by
  exact
    (holonomicP286GaugeConnectionCoordinate_contDiff
      fixedP506L0RequiredExteriorChargedComparison
      fixedP506L0RequiredExteriorChargedComparison_smooth).comp
      canonicalZeroSlice_contDiff

private theorem fixedP506L0RequiredExterior_originAuxiliary_contDiff :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      currentP286OriginAuxiliaryCoordinate
        (recenteredCartanRepairedScalarSecondJetActual space) := by
  apply contDiff_pi'
  intro pair
  exact
    fixedP506L0CompleteJointP286OriginAuxiliary_component_contDiff pair

private theorem fixedP506L0RequiredExterior_adjoint_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      p286GaugeTwoFormAdjoint
        (holonomicP286GaugeConnectionCoordinate
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space) direction)
        (currentP286OriginAuxiliaryCoordinate
          (recenteredCartanRepairedScalarSecondJetActual space)) := by
  apply contDiff_pi'
  intro pair
  exact
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
      (contDiff_pi.mp
        fixedP506L0RequiredExterior_comparisonGaugeConnection_contDiff
        direction)).clm_apply
      (contDiff_pi.mp
        fixedP506L0RequiredExterior_originAuxiliary_contDiff pair)

private theorem fixedP506L0RequiredExterior_orderedAdjoint_contDiff
    (direction first second : LorentzianIndex) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      orderedP286GaugeTwoFormComponent
        (p286GaugeTwoFormAdjoint
          (holonomicP286GaugeConnectionCoordinate
            fixedP506L0RequiredExteriorChargedComparison
            (canonicalCauchySlicePoint 0 space) direction)
          (currentP286OriginAuxiliaryCoordinate
            (recenteredCartanRepairedScalarSecondJetActual space)))
        first second := by
  unfold orderedP286GaugeTwoFormComponent
  apply ContDiff.sum
  intro pair _
  exact
    (contDiff_const : ContDiff ℝ ∞ fun _ : StageNineSpatialPoint =>
      (orientedLorentzBivectorBasisCoefficient pair first second : ℝ)).smul
      (contDiff_pi.mp
        (fixedP506L0RequiredExterior_adjoint_contDiff direction) pair)

private theorem
    fixedP506L0RequiredExterior_connectionExteriorAction_component_contDiff
    (triple : Fin 4) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space))
        (currentP286OriginAuxiliaryCoordinate
          (recenteredCartanRepairedScalarSecondJetActual space)) triple := by
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [Pi.zero_apply, zero_add]
  exact
    ((fixedP506L0RequiredExterior_orderedAdjoint_contDiff
      (threeFormFirst triple) (threeFormSecond triple)
      (threeFormThird triple)).add
      (fixedP506L0RequiredExterior_orderedAdjoint_contDiff
        (threeFormSecond triple) (threeFormThird triple)
        (threeFormFirst triple))).add
      (fixedP506L0RequiredExterior_orderedAdjoint_contDiff
        (threeFormThird triple) (threeFormFirst triple)
        (threeFormSecond triple))

/-- The source/current origin profile consumed by the whole-section P286
write is exactly the solved input auxiliary on the matching Cauchy
occurrence.  This is a producer-field identification, not a residual
equation. -/
theorem fixedP506L0RequiredExterior_originAuxiliary_eq_fixedInput
    (space : StageNineSpatialPoint) :
    currentP286OriginAuxiliaryCoordinate
        (recenteredCartanRepairedScalarSecondJetActual space) =
      holonomicP286GaugeAuxiliaryCoordinate FixedInput
        (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0CompleteJointP286OriginAuxiliary_normalForm,
    ← fixedP506FormNativeConstitutiveAuxiliaryCoordinate_zeroSlice]
  unfold fixedP506FormNativeConstitutiveAuxiliaryCoordinate
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    holonomicP286GaugeCurvatureCoordinate
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
  apply congrArg formNativeP286GaugeActualToCoordinateLinear
  apply congrArg
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 1)
  change
    formNativeP286GaugeCoordinateToActualLinear
        (formNativeP286GaugeActualToCoordinateLinear
          (holonomicGaugeCurvature FixedInput
            (canonicalCauchySlicePoint 0 space))) =
      holonomicGaugeCurvature FixedInput
        (canonicalCauchySlicePoint 0 space)
  exact formNativeP286GaugeActual_coordinate_actual _

/-- The exact fixed-lineage contact target is the direct mother-action read
of the original solved current on the matching zero-slice occurrence. -/
theorem
    fixedP506L0RecenteredCartanRequiredExteriorDerivative_eq_fixedInputDirect_zeroSlice
    (space : StageNineSpatialPoint) :
    formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space) =
      pointwiseDirectP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource FixedInput
        (canonicalCauchySlicePoint 0 space) := by
  unfold formNativeCurrentP286RequiredExteriorDerivative
    pointwiseDirectP286RequiredExteriorDerivative
  rw [
    fixedP506L0RequiredExterior_physicalChargedGaugeCurrent_origin_eq_comparison,
    fixedP506L0RequiredExterior_gaugeConnectionCoordinate_origin_eq_comparison]
  have comparisonPhysical :
      formNativePhysicalChargedGaugeCurrentThreeForm
          positiveSmoothUnifiedSource 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField
            fixedP506L0RequiredExteriorChargedComparison
            (canonicalCauchySlicePoint 0 space)) =
        formNativePhysicalChargedGaugeCurrentThreeForm
          positiveSmoothUnifiedSource 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField FixedInput
            (canonicalCauchySlicePoint 0 space)) := by
    unfold formNativePhysicalChargedGaugeCurrentThreeForm
    congr 1
    apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
    · exact
        (fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
          space).symm
    · rfl
    · rfl
    · rfl
    · rfl
  have comparisonConnection :
      holonomicP286GaugeConnectionCoordinate
          fixedP506L0RequiredExteriorChargedComparison
          (canonicalCauchySlicePoint 0 space) =
        holonomicP286GaugeConnectionCoordinate FixedInput
          (canonicalCauchySlicePoint 0 space) := by
    rfl
  rw [comparisonPhysical, comparisonConnection]
  change
    formNativePhysicalChargedGaugeCurrentThreeForm
          positiveSmoothUnifiedSource 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField FixedInput
            (canonicalCauchySlicePoint 0 space)) -
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate FixedInput
            (canonicalCauchySlicePoint 0 space))
          (currentP286OriginAuxiliaryCoordinate
            (recenteredCartanRepairedScalarSecondJetActual space)) =
      formNativePhysicalChargedGaugeCurrentThreeForm
          positiveSmoothUnifiedSource 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField FixedInput
            (canonicalCauchySlicePoint 0 space)) -
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate FixedInput
            (canonicalCauchySlicePoint 0 space))
          (holonomicP286GaugeAuxiliaryCoordinate FixedInput
            (canonicalCauchySlicePoint 0 space))
  rw [fixedP506L0RequiredExterior_originAuxiliary_eq_fixedInput]

/-- Each component of the fixed P506/L0 exterior derivative required by the
complete P286 action writer is smooth across the source-owned spatial
occurrence. -/
theorem
    fixedP506L0RecenteredCartanRequiredExteriorDerivative_component_contDiff
    (triple : Fin 4) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space) triple := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space) triple) =
      fun space =>
        (formNativePhysicalChargedGaugeCurrentThreeForm
            positiveSmoothUnifiedSource 0
            (canonicalCauchySlicePoint 0 space)
            (toContinuumPointField
              fixedP506L0RequiredExteriorChargedComparison
              (canonicalCauchySlicePoint 0 space)) -
          pointwiseP286GaugeTwoFormConnectionExteriorAction
            (holonomicP286GaugeConnectionCoordinate
              fixedP506L0RequiredExteriorChargedComparison
              (canonicalCauchySlicePoint 0 space))
            (currentP286OriginAuxiliaryCoordinate
              (recenteredCartanRepairedScalarSecondJetActual space))) triple by
    funext space
    unfold formNativeCurrentP286RequiredExteriorDerivative
    rw [
      fixedP506L0RequiredExterior_physicalChargedGaugeCurrent_origin_eq_comparison,
      fixedP506L0RequiredExterior_gaugeConnectionCoordinate_origin_eq_comparison]
    rfl]
  exact
    (contDiff_pi.mp
      (fixedP506L0RequiredExteriorPhysicalChargedThreeForm_contDiff.comp
        canonicalZeroSlice_contDiff) triple).sub
      (fixedP506L0RequiredExterior_connectionExteriorAction_component_contDiff
        triple)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286RequiredExteriorDerivativeSpatialRegularity
