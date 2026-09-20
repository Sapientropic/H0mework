import H0mework.Physics.DualVariation.PointwiseActionJetCarrier
import H0mework.Physics.Coframe.CoframeLocalDifferentiability
import H0mework.Physics.FixedJoint.FixedConstitutiveFirstJet
import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterComparison
import H0mework.Physics.RepairedAction.ActionSpatialSectionRecenterPointFieldNaturality
import H0mework.Physics.RepairedAction.ActionSpatialSectionResidual

/-!
# Recentered action-jet naturality of the repaired spatial section

For the fixed P506/L0 source, this module compares the complete pointwise
action jet of the generated four-dimensional section at `(0, space)` with the
jet of the matching source/action-generated contact at its origin.  The
comparison is made before the nine residual coordinates are assembled.

No residual coordinate, support branch, zero-fiber witness, or candidate
correction enters either action-jet constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterActionJetNaturality

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineCoframeHolonomicRegularity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineMatterPointwiseEquation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000

local instance repairedRecenterActionJetP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance repairedRecenterActionJetP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance repairedRecenterActionJetP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private abbrev InputActual :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev SectionActual :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private theorem sectionCoframe_eq_input :
    SectionActual.coframe = InputActual.coframe :=
  diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
    positiveSmoothUnifiedSource InputActual

private theorem sectionGaugeConnection_eq_input :
    SectionActual.gaugeConnection = InputActual.gaugeConnection :=
  diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
    positiveSmoothUnifiedSource InputActual

private theorem sectionScalar_eq_input :
    SectionActual.scalar = InputActual.scalar :=
  diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
    positiveSmoothUnifiedSource InputActual

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  simpa only [canonicalCauchySlicePoint_zero_zero_local] using
    canonicalSpatialContactTranslation_timeAxis space 0

private theorem fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
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
  rfl

def sectionActionJet
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet
    positiveSmoothUnifiedSource SectionActual
    (canonicalCauchySlicePoint 0 space)

def recenteredContactActionJet
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet
    positiveSmoothUnifiedSource (recenteredContactActual space) 0

/-- The contact action jet with the already-classified derived gravity
curvature assembly seam installed in its point-field slot.  All remaining
slots still come literally from the matching contact action jet. -/
def recenteredContactActionJetWithGravitySeam
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  { recenteredContactActionJet space with
    pointField := recenteredContactPointFieldWithGravitySeam space }

private theorem sectionGravityConnection_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    SectionActual.gravityConnection (canonicalCauchySlicePoint 0 space) =
      (recenteredContactActual space).gravityConnection 0 := by
  change
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource InputActual).gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        positiveSmoothUnifiedSource
        (spatiallyRecenterHolonomicConfiguration InputActual space)
        ).gravityConnection 0
  simpa only [canonicalCauchySlicePoint_zero_zero_local] using
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityConnection_slice
      positiveSmoothUnifiedSource InputActual 0 space

private theorem sectionGaugeConnection_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    SectionActual.gaugeConnection (canonicalCauchySlicePoint 0 space) =
      (recenteredContactActual space).gaugeConnection 0 := by
  change
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource InputActual).gaugeConnection
        (canonicalCauchySlicePoint 0 space) =
      (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        positiveSmoothUnifiedSource
        (spatiallyRecenterHolonomicConfiguration InputActual space)
        ).gaugeConnection 0
  simpa only [canonicalCauchySlicePoint_zero_zero_local] using
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection_slice
      positiveSmoothUnifiedSource InputActual 0 space

private theorem inputSimplicity :
    FormNativeGravitySimplicityEquation InputActual := by
  unfold InputActual FixedP506FormNativeJointActionSolvedSuccessor
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
      positiveSmoothUnifiedSource _

private theorem sectionGravityAuxiliary_eq_input :
    SectionActual.gravityAuxiliary = InputActual.gravityAuxiliary := by
  exact
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_eq_current
      positiveSmoothUnifiedSource InputActual inputSimplicity

private theorem recenteredContactGravityAuxiliary_eq_inputComp
    (space : StageNineSpatialPoint) :
    (recenteredContactActual space).gravityAuxiliary =
      InputActual.gravityAuxiliary ∘
        canonicalSpatialContactTranslation space := by
  funext point
  change
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      positiveSmoothUnifiedSource
      (spatiallyRecenterHolonomicConfiguration InputActual space)
      ).gravityAuxiliary point = _
  rw [diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityAuxiliary]
  change
    physicalIIPlusBivector
        (InputActual.coframe
          (canonicalSpatialContactTranslation space point)) =
      InputActual.gravityAuxiliary
        (canonicalSpatialContactTranslation space point)
  exact (inputSimplicity _).symm

private theorem sectionGravityAuxiliaryExteriorCovariantDerivative_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative SectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicGravityAuxiliaryExteriorCovariantDerivative
        (recenteredContactActual space) 0 := by
  have inputDifferentiable :
      DifferentiableAt ℝ InputActual.gravityAuxiliary
        (canonicalSpatialContactTranslation space 0) :=
    ((holonomicGravityAuxiliary_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth).differentiable
      (by simp)).differentiableAt
  have derivativeEquality :
      gravityAuxiliaryDirectionalDerivative SectionActual
          (canonicalCauchySlicePoint 0 space) =
        gravityAuxiliaryDirectionalDerivative
          (recenteredContactActual space) 0 := by
    funext direction
    unfold gravityAuxiliaryDirectionalDerivative
    rw [sectionGravityAuxiliary_eq_input,
      recenteredContactGravityAuxiliary_eq_inputComp]
    rw [fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
      InputActual.gravityAuxiliary space 0 direction inputDifferentiable]
    rw [canonicalSpatialContactTranslation_zero_local]
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet
  rw [sectionGravityConnection_eq_recenteredContact]
  apply congrArg
    (pointwisePhysicalBivectorExteriorCovariantDerivative
      ((recenteredContactActual space).gravityConnection 0))
  congr 1
  · rw [sectionGravityAuxiliary_eq_input,
      recenteredContactGravityAuxiliary_eq_inputComp,
      Function.comp_apply,
      canonicalSpatialContactTranslation_zero_local]

private theorem recenteredContactGaugeAuxiliary_eq_sectionComp
    (space : StageNineSpatialPoint) :
    (recenteredContactActual space).gaugeAuxiliary =
      SectionActual.gaugeAuxiliary ∘
        canonicalSpatialContactTranslation space := by
  funext point
  change
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      positiveSmoothUnifiedSource
      (spatiallyRecenterHolonomicConfiguration InputActual space)
      ).gaugeAuxiliary point =
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource InputActual).gaugeAuxiliary
        (canonicalSpatialContactTranslation space point)
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeAuxiliary]
  rw [diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      positiveSmoothUnifiedSource InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [holonomicGaugeCurvature_spatiallyRecenter InputActual
    fixedP506FormNativeJointActionSolvedSuccessor_smooth]
  rfl

private theorem recenteredContactGaugeAuxiliaryCoordinate_eq_sectionComp
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate (recenteredContactActual space) =
      holonomicP286GaugeAuxiliaryCoordinate SectionActual ∘
        canonicalSpatialContactTranslation space := by
  funext point
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [recenteredContactGaugeAuxiliary_eq_sectionComp]
  rfl

private theorem sectionGaugeAuxiliaryCoordinate_eq_actionInverse :
    holonomicP286GaugeAuxiliaryCoordinate SectionActual =
      fixedP506FormNativeConstitutiveAuxiliaryCoordinate := by
  funext point
  unfold holonomicP286GaugeAuxiliaryCoordinate
  change
    (fun pair => p286CoordinateEquiv
      ((diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).gaugeAuxiliary point pair)) =
      fixedP506FormNativeConstitutiveAuxiliaryCoordinate point
  rw [diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      positiveSmoothUnifiedSource InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth]
  rfl

private theorem sectionGaugeAuxiliaryDirectionalDerivative_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    p286GaugeAuxiliaryDirectionalDerivative SectionActual
        (canonicalCauchySlicePoint 0 space) =
      p286GaugeAuxiliaryDirectionalDerivative
        (recenteredContactActual space) 0 := by
  funext direction
  have sectionDifferentiable :
      DifferentiableAt ℝ
        (holonomicP286GaugeAuxiliaryCoordinate SectionActual)
        (canonicalCauchySlicePoint 0 space) := by
    rw [sectionGaugeAuxiliaryCoordinate_eq_actionInverse]
    exact
      fixedP506FormNativeConstitutiveAuxiliaryCoordinate_differentiableAt_zeroSlice
        space
  unfold p286GaugeAuxiliaryDirectionalDerivative
  rw [recenteredContactGaugeAuxiliaryCoordinate_eq_sectionComp]
  symm
  simpa only [canonicalSpatialContactTranslation_zero_local] using
    fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
      (holonomicP286GaugeAuxiliaryCoordinate SectionActual)
      space 0 direction
      (by
        simpa only [canonicalSpatialContactTranslation_zero_local] using
          sectionDifferentiable)

private theorem sectionP286GaugeAuxiliaryExteriorCovariantDerivative_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative SectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (recenteredContactActual space) 0 := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  unfold holonomicP286GaugeConnectionCoordinate
  rw [sectionGaugeConnection_eq_recenteredContact]
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate SectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate
        (recenteredContactActual space) 0 by
    rw [recenteredContactGaugeAuxiliaryCoordinate_eq_sectionComp,
      Function.comp_apply, canonicalSpatialContactTranslation_zero_local]]
  rw [sectionGaugeAuxiliaryDirectionalDerivative_eq_recenteredContact]

private theorem recenteredContactScalarCovariantDerivative_eq_sectionComp
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative (recenteredContactActual space) point =
      holonomicScalarCovariantDerivative SectionActual
        (canonicalSpatialContactTranslation space point) := by
  funext direction
  change
    holonomicScalarCovariantDerivative
        (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
          positiveSmoothUnifiedSource
          (spatiallyRecenterHolonomicConfiguration InputActual space))
        point direction =
      holonomicScalarCovariantDerivative
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          positiveSmoothUnifiedSource InputActual)
        (canonicalSpatialContactTranslation space point) direction
  unfold holonomicScalarCovariantDerivative
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection]
  change
    fieldDirectionalDerivative
          (InputActual.scalar ∘ canonicalSpatialContactTranslation space)
          point direction + _ =
      fieldDirectionalDerivative InputActual.scalar
          (canonicalSpatialContactTranslation space point) direction + _
  rw [fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
    InputActual.scalar space point direction]
  · rfl
  · exact
      (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
        |>.differentiable (by simp)).differentiableAt

private theorem recenteredContactCoframe_eq_sectionComp
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (recenteredContactActual space).coframe point =
      SectionActual.coframe
        (canonicalSpatialContactTranslation space point) := by
  change
    (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
      positiveSmoothUnifiedSource
      (spatiallyRecenterHolonomicConfiguration InputActual space)
      ).coframe point =
    (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
      positiveSmoothUnifiedSource InputActual).coframe
        (canonicalSpatialContactTranslation space point)
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe]
  rfl

private theorem recenteredContactScalarDifferentialMomentum_eq_sectionComp
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredContactActual space) direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
          SectionActual direction derivativeDirection ∘
        canonicalSpatialContactTranslation space := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    generatedVolumeDensity
  simp only [Function.comp_apply, toContinuumPointField]
  rw [recenteredContactScalarCovariantDerivative_eq_sectionComp,
    recenteredContactCoframe_eq_sectionComp]
  unfold scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]

private theorem sectionScalarCovariantDerivative_eq_input :
    holonomicScalarCovariantDerivative SectionActual =
      holonomicScalarCovariantDerivative InputActual := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [sectionScalar_eq_input, sectionGaugeConnection_eq_input]

private theorem sectionScalarDifferentialMomentum_eq_input
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource SectionActual
        direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sectionScalarCovariantDerivative_eq_input,
    sectionCoframe_eq_input]

private theorem inputScalarDifferentialMomentum_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
        direction derivativeDirection)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeSmooth : ContDiff ℝ ∞ InputActual.coframe :=
    holonomicCoframe_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
  have coframeAtPoint : InputActual.coframe point = 1 := by
    simpa only [point] using
      fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have coframeNondegenerate : Matrix.det (InputActual.coframe point) ≠ 0 := by
    rw [coframeAtPoint]
    norm_num
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (InputActual.coframe candidate)|)
      point :=
    (coframe_volume_contDiffAt (InputActual.coframe point)
      coframeNondegenerate).comp point coframeSmooth.contDiffAt
  have metricSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (InputActual.coframe candidate))⁻¹)
      point :=
    (lorentzianMetric_inv_contDiffAt (InputActual.coframe point)
      coframeNondegenerate).comp point coframeSmooth.contDiffAt
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun candidate =>
        holonomicScalarCovariantDerivative InputActual candidate
          formDirection :=
    holonomicScalarCovariantDerivative_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth formDirection
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun _ : BasePoint =>
        scalarVariationDifferentialDirection direction derivativeDirection
          formDirection :=
    contDiff_const
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
    generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeSmooth.mul
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  apply (contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second).mul
  exact
    ((scalarCoordinatePairingRe_joint_contDiff_local
      _ _ (variationSmooth first) (covariantSmooth second)).add
      (scalarCoordinatePairingRe_joint_contDiff_local
        _ _ (covariantSmooth first) (variationSmooth second))).contDiffAt

/-- The scalar canonical momentum of the matching action-generated contact is
`C∞` at its origin.  This is the fixed P506/L0 regularity mouth needed by
downstream source/action-owned scalar writes; it does not assert regularity for
an arbitrary `StageNineHolonomicConfiguration`. -/
theorem recenteredContactScalarDifferentialMomentum_contDiffAt_origin
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredContactActual space) direction derivativeDirection)
      0 := by
  rw [recenteredContactScalarDifferentialMomentum_eq_sectionComp,
    sectionScalarDifferentialMomentum_eq_input]
  have translationSmooth : ContDiffAt ℝ ∞
      (canonicalSpatialContactTranslation space) 0 := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have inputSmooth :=
    inputScalarDifferentialMomentum_contDiffAt_zeroSlice space direction
      derivativeDirection
  have inputSmoothAtTranslation : ContDiffAt ℝ ∞
      (scalarDifferentialMomentum positiveSmoothUnifiedSource InputActual
        direction derivativeDirection)
      (canonicalSpatialContactTranslation space 0) := by
    simpa only [canonicalSpatialContactTranslation_zero_local] using
      inputSmooth
  exact inputSmoothAtTranslation.comp 0 translationSmooth

private theorem sectionScalarDifferentialMomentumDivergence_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    (fun direction =>
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        SectionActual direction (canonicalCauchySlicePoint 0 space)) =
      fun direction =>
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          (recenteredContactActual space) direction 0 := by
  funext direction
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [recenteredContactScalarDifferentialMomentum_eq_sectionComp]
  have sectionDifferentiable : DifferentiableAt ℝ
      (scalarDifferentialMomentum positiveSmoothUnifiedSource SectionActual
        direction derivativeDirection)
      (canonicalCauchySlicePoint 0 space) := by
    rw [sectionScalarDifferentialMomentum_eq_input]
    exact
      (inputScalarDifferentialMomentum_contDiffAt_zeroSlice space direction
        derivativeDirection).differentiableAt (by simp)
  symm
  simpa only [canonicalSpatialContactTranslation_zero_local] using
    fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
      (scalarDifferentialMomentum positiveSmoothUnifiedSource SectionActual
        direction derivativeDirection)
      space 0 derivativeDirection
      (by
        simpa only [canonicalSpatialContactTranslation_zero_local] using
          sectionDifferentiable)

private theorem repairedMatterWrittenCurrent_conjugateMatter_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    (diracDualFormNativeRepairedMatterWrittenCurrent current).conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      current.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  unfold diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  let primal :=
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual current
  let output :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      primal
  let point := canonicalCauchySlicePoint 0 space
  change output.conjugateMatter point = current.conjugateMatter point
  calc
    output.conjugateMatter point =
        matterDualOfCoordinates
          (matterDualCoordinates (output.conjugateMatter point)) :=
      (matterDualOfCoordinates_surjective _).symm
    _ = matterDualOfCoordinates
          (matterDualCoordinates (primal.conjugateMatter point)) := by
      apply congrArg matterDualOfCoordinates
      unfold output
        actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
      rw [installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates]
      simp [conjugateMatterLinearTimeCoordinateWrite, point,
        canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
    _ = primal.conjugateMatter point := matterDualOfCoordinates_surjective _
    _ = current.conjugateMatter point := by
      rfl

private theorem recenteredContact_conjugateMatter_zeroSlice
    (space localSpace : StageNineSpatialPoint) :
    (recenteredContactActual space).conjugateMatter
        (canonicalCauchySlicePoint 0 localSpace) =
      InputActual.conjugateMatter
        (canonicalSpatialContactTranslation space
          (canonicalCauchySlicePoint 0 localSpace)) := by
  rw [show
    (recenteredContactActual space).conjugateMatter =
      (diracDualFormNativeRepairedMatterWrittenCurrent
        (spatiallyRecenterHolonomicConfiguration InputActual space)
        ).conjugateMatter by
      exact
        diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter
          positiveSmoothUnifiedSource
          (spatiallyRecenterHolonomicConfiguration InputActual space)]
  rw [repairedMatterWrittenCurrent_conjugateMatter_zeroSlice]
  rfl

private def localCoordinateAxis
    (direction : LorentzianIndex) : ℝ → BasePoint :=
  fun parameter => parameter • coordinateDirection direction

private theorem sectionConjugateMatter_eq_recenteredContact_onCoordinateAxis
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex)
    (parameter : ℝ) :
    SectionActual.conjugateMatter
        (canonicalSpatialContactTranslation space
          (localCoordinateAxis direction parameter)) =
      (recenteredContactActual space).conjugateMatter
        (localCoordinateAxis direction parameter) := by
  by_cases temporal : direction = canonicalLorentzianTimeDirection
  · subst direction
    have localTemporal :
        localCoordinateAxis canonicalLorentzianTimeDirection parameter =
          canonicalCauchySlicePoint parameter 0 := by
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;>
        simp [localCoordinateAxis, coordinateDirection,
          canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]
    rw [localTemporal, canonicalSpatialContactTranslation_timeAxis]
    exact
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice
        positiveSmoothUnifiedSource InputActual parameter space
  · have directionNeZero : direction ≠ (0 : LorentzianIndex) := by
      simpa [canonicalLorentzianTimeDirection] using temporal
    have localTimeZero :
        canonicalTimeProjection (localCoordinateAxis direction parameter) =
          0 := by
      unfold localCoordinateAxis canonicalTimeProjection
      simp [coordinateDirection, canonicalLorentzianTimeDirection,
        Ne.symm directionNeZero]
    have globalTimeZero :
        canonicalTimeProjection
            (canonicalSpatialContactTranslation space
              (localCoordinateAxis direction parameter)) =
          0 := by
      unfold canonicalSpatialContactTranslation
      simp [map_add, localTimeZero, canonicalTimeProjection_slice]
    have localDecomposition :
        canonicalCauchySlicePoint 0
            (canonicalSpatialProjection
              (localCoordinateAxis direction parameter)) =
          localCoordinateAxis direction parameter := by
      rw [← localTimeZero]
      exact
        canonicalCauchySlicePoint_projections
          (localCoordinateAxis direction parameter)
    have globalDecomposition :
        canonicalCauchySlicePoint 0
            (canonicalSpatialProjection
              (canonicalSpatialContactTranslation space
                (localCoordinateAxis direction parameter))) =
          canonicalSpatialContactTranslation space
            (localCoordinateAxis direction parameter) := by
      rw [← globalTimeZero]
      exact
        canonicalCauchySlicePoint_projections
          (canonicalSpatialContactTranslation space
            (localCoordinateAxis direction parameter))
    calc
      SectionActual.conjugateMatter
          (canonicalSpatialContactTranslation space
            (localCoordinateAxis direction parameter)) =
          SectionActual.conjugateMatter
            (canonicalCauchySlicePoint 0
              (canonicalSpatialProjection
                (canonicalSpatialContactTranslation space
                  (localCoordinateAxis direction parameter)))) :=
        congrArg SectionActual.conjugateMatter globalDecomposition.symm
      _ = InputActual.conjugateMatter
            (canonicalCauchySlicePoint 0
              (canonicalSpatialProjection
                (canonicalSpatialContactTranslation space
                  (localCoordinateAxis direction parameter)))) :=
        diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
          positiveSmoothUnifiedSource InputActual _
      _ = InputActual.conjugateMatter
            (canonicalSpatialContactTranslation space
              (localCoordinateAxis direction parameter)) :=
        congrArg InputActual.conjugateMatter globalDecomposition
      _ = InputActual.conjugateMatter
            (canonicalSpatialContactTranslation space
              (canonicalCauchySlicePoint 0
                (canonicalSpatialProjection
                  (localCoordinateAxis direction parameter)))) :=
        congrArg
          (fun point => InputActual.conjugateMatter
            (canonicalSpatialContactTranslation space point))
          localDecomposition.symm
      _ = (recenteredContactActual space).conjugateMatter
            (canonicalCauchySlicePoint 0
              (canonicalSpatialProjection
                (localCoordinateAxis direction parameter))) :=
        (recenteredContact_conjugateMatter_zeroSlice space _).symm
      _ = (recenteredContactActual space).conjugateMatter
            (localCoordinateAxis direction parameter) :=
        congrArg (recenteredContactActual space).conjugateMatter
          localDecomposition

private theorem sectionMatterDifferentialMomentum_eq_comparison
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource SectionActual
        direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        fixedP506FormNativeRepairedSpatialMatterSmoothComparison
        direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [← repairedMatterComparison_coframe_eq_repaired,
    ← repairedMatterComparison_conjugateMatter_eq_repaired]

private def recenteredContactMatterActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedMatterWrittenCurrent
    (spatiallyRecenterHolonomicConfiguration InputActual space)

private theorem recenteredContactMatterActual_smooth
    (space : StageNineSpatialPoint) :
    (recenteredContactMatterActual space).Smooth := by
  unfold recenteredContactMatterActual
    diracDualFormNativeRepairedMatterWrittenCurrent
  exact
    actionGeneratedDiracDualRepairedMatterJointResponseActual_smooth _
      (spatiallyRecenterHolonomicConfiguration_smooth InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth space)

private theorem recenteredContactMatterActual_coframe_origin
    (space : StageNineSpatialPoint) :
    (recenteredContactMatterActual space).coframe 0 = 1 := by
  change
    InputActual.coframe (canonicalSpatialContactTranslation space 0) = 1
  rw [canonicalSpatialContactTranslation_zero_local]
  exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space

private theorem recenteredContact_matterDifferentialMomentum_eq_matterActual
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredContactActual space) direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredContactMatterActual space) direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [show
    (recenteredContactActual space).coframe =
      (recenteredContactMatterActual space).coframe by
      rfl]
  rw [show
    (recenteredContactActual space).conjugateMatter =
      (recenteredContactMatterActual space).conjugateMatter by
      exact
        diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_conjugateMatter
          positiveSmoothUnifiedSource
          (spatiallyRecenterHolonomicConfiguration InputActual space)]

private theorem matterDifferentialMomentum_differentiableAt_of_smooth_coframe_one
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (coframeOne : configuration.coframe point = 1)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource configuration
        direction derivativeDirection) point := by
  let outer :=
    matterDifferentialMomentumPointCoframe positiveSmoothUnifiedSource
      configuration direction derivativeDirection
  have outerDifferentiable : DifferentiableAt ℝ outer (point, 1) :=
    (matterDifferentialMomentumPointCoframe_contDiffAt
      positiveSmoothUnifiedSource configuration smooth point 1 (by norm_num)
      direction derivativeDirection).differentiableAt (by simp)
  have coframeDifferentiable : DifferentiableAt ℝ configuration.coframe point :=
    ((holonomicCoframe_contDiff configuration smooth).differentiable (by simp)
      ).differentiableAt
  rw [matterDifferentialMomentum_eq_pointCoframe_actualSection]
  have innerDifferentiable : DifferentiableAt ℝ
      (fun candidate : BasePoint =>
        (candidate, configuration.coframe candidate)) point :=
    differentiableAt_id.prodMk coframeDifferentiable
  have outerAtActual : DifferentiableAt ℝ outer
      (point, configuration.coframe point) := by
    rw [coframeOne]
    exact outerDifferentiable
  exact outerAtActual.comp point innerDifferentiable

private theorem sectionMatterDifferentialMomentum_differentiableAt
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource SectionActual
        direction derivativeDirection)
      (canonicalCauchySlicePoint 0 space) := by
  rw [sectionMatterDifferentialMomentum_eq_comparison]
  apply matterDifferentialMomentum_differentiableAt_of_smooth_coframe_one
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison_smooth
  have jet := repairedMatterComparison_coframeFirstJet_zeroSlice space
  exact congrArg PointwiseLorentzianCoframeJet.coframe jet

private theorem recenteredContactMatterDifferentialMomentum_differentiableAt
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredContactActual space) direction derivativeDirection) 0 := by
  rw [recenteredContact_matterDifferentialMomentum_eq_matterActual]
  exact
    matterDifferentialMomentum_differentiableAt_of_smooth_coframe_one
      (recenteredContactMatterActual space)
      (recenteredContactMatterActual_smooth space) 0
      (recenteredContactMatterActual_coframe_origin space)
      direction derivativeDirection

private theorem localCoordinateAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (localCoordinateAxis direction)
      (coordinateDirection direction) 0 := by
  unfold localCoordinateAxis
  simpa using
    (hasDerivAt_id (𝕜 := ℝ) 0).smul_const (coordinateDirection direction)

private theorem translatedCoordinateAxis_hasDerivAt
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    HasDerivAt
      (canonicalSpatialContactTranslation space ∘ localCoordinateAxis direction)
      (coordinateDirection direction) 0 := by
  have translation :
      HasFDerivAt (canonicalSpatialContactTranslation space)
        (ContinuousLinearMap.id ℝ BasePoint)
        (localCoordinateAxis direction 0) := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  exact translation.comp_hasDerivAt 0 (localCoordinateAxis_hasDerivAt direction)

private theorem
    sectionMatterDifferentialMomentum_eq_recenteredContact_onCoordinateAxis
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource SectionActual
          direction derivativeDirection ∘
        (canonicalSpatialContactTranslation space ∘
          localCoordinateAxis derivativeDirection) =
      matterDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredContactActual space) direction derivativeDirection ∘
        localCoordinateAxis derivativeDirection := by
  funext parameter
  simp only [Function.comp_apply]
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [← recenteredContactCoframe_eq_sectionComp space
    (localCoordinateAxis derivativeDirection parameter)]
  rw [sectionConjugateMatter_eq_recenteredContact_onCoordinateAxis
    space derivativeDirection parameter]

private theorem sectionMatterDifferentialMomentumDerivative_eq_recenteredContact
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource SectionActual
          direction derivativeDirection)
        (canonicalCauchySlicePoint 0 space) derivativeDirection =
      fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          (recenteredContactActual space) direction derivativeDirection)
        0 derivativeDirection := by
  let sectionMomentum :=
    matterDifferentialMomentum positiveSmoothUnifiedSource SectionActual
      direction derivativeDirection
  let contactMomentum :=
    matterDifferentialMomentum positiveSmoothUnifiedSource
      (recenteredContactActual space) direction derivativeDirection
  have sectionAxisOrigin :
      canonicalSpatialContactTranslation space
          (localCoordinateAxis derivativeDirection 0) =
        canonicalCauchySlicePoint 0 space := by
    simp [localCoordinateAxis, canonicalSpatialContactTranslation_zero_local]
  have sectionOuter : HasFDerivAt sectionMomentum
      (fderiv ℝ sectionMomentum (canonicalCauchySlicePoint 0 space))
      ((canonicalSpatialContactTranslation space ∘
        localCoordinateAxis derivativeDirection) 0) := by
    rw [Function.comp_apply, sectionAxisOrigin]
    exact
      (sectionMatterDifferentialMomentum_differentiableAt space direction
        derivativeDirection).hasFDerivAt
  have contactOuter : HasFDerivAt contactMomentum
      (fderiv ℝ contactMomentum 0)
      (localCoordinateAxis derivativeDirection 0) := by
    rw [show localCoordinateAxis derivativeDirection 0 = 0 by
      simp [localCoordinateAxis]]
    exact
      (recenteredContactMatterDifferentialMomentum_differentiableAt space
        direction derivativeDirection).hasFDerivAt
  have sectionDerivative :=
    sectionOuter.comp_hasDerivAt 0
      (translatedCoordinateAxis_hasDerivAt space derivativeDirection)
  have contactDerivative :=
    contactOuter.comp_hasDerivAt 0
      (localCoordinateAxis_hasDerivAt derivativeDirection)
  change HasDerivAt
      (sectionMomentum ∘
        (canonicalSpatialContactTranslation space ∘
          localCoordinateAxis derivativeDirection))
      (fieldDirectionalDerivative sectionMomentum
        (canonicalCauchySlicePoint 0 space) derivativeDirection) 0
    at sectionDerivative
  change HasDerivAt
      (contactMomentum ∘ localCoordinateAxis derivativeDirection)
      (fieldDirectionalDerivative contactMomentum 0 derivativeDirection) 0
    at contactDerivative
  have transported : HasDerivAt
      (contactMomentum ∘ localCoordinateAxis derivativeDirection)
      (fieldDirectionalDerivative sectionMomentum
        (canonicalCauchySlicePoint 0 space) derivativeDirection) 0 := by
    rw [← sectionMatterDifferentialMomentum_eq_recenteredContact_onCoordinateAxis
      space direction derivativeDirection]
    exact sectionDerivative
  exact transported.unique contactDerivative

private theorem sectionMatterDifferentialMomentumDivergence_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    (fun direction =>
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        SectionActual direction (canonicalCauchySlicePoint 0 space)) =
      fun direction =>
        matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
          (recenteredContactActual space) direction 0 := by
  funext direction
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    sectionMatterDifferentialMomentumDerivative_eq_recenteredContact
      space direction derivativeDirection

/-- Complete action-jet naturality for the fixed P506/L0 repaired section.
The only seam is the already-classified derived gravity-curvature assembly
coordinate carried by `recenteredContactActionJetWithGravitySeam`; every
primitive value and every derivative slot is read from the same matching
source/action-generated contact. -/
theorem sectionActionJet_eq_recenteredContactWithGravitySeam
    (space : StageNineSpatialPoint) :
    sectionActionJet space =
      recenteredContactActionJetWithGravitySeam space := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · exact sectionPointField_eq_recenteredContactWithGravitySeam space
  · exact sectionGravityConnection_eq_recenteredContact space
  · exact sectionGaugeConnection_eq_recenteredContact space
  · exact
      sectionGravityAuxiliaryExteriorCovariantDerivative_eq_recenteredContact
        space
  · exact
      sectionP286GaugeAuxiliaryExteriorCovariantDerivative_eq_recenteredContact
        space
  · exact sectionScalarDifferentialMomentumDivergence_eq_recenteredContact space
  · exact sectionMatterDifferentialMomentumDivergence_eq_recenteredContact space

/-- Whole nine-channel readout of the matching contact action jet after the
single derived gravity-curvature assembly seam is installed. -/
def recenteredContactJointResidualWithGravitySeam
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualOfActionJet positiveSmoothUnifiedSource
    (canonicalCauchySlicePoint 0 space)
    (recenteredContactActionJetWithGravitySeam space)

/-- The authoritative residual of the generated global section factors
through the matching contact action jet as one whole carrier. -/
theorem sectionJointResidual_eq_recenteredContactWithGravitySeam
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        SectionActual (canonicalCauchySlicePoint 0 space) =
      recenteredContactJointResidualWithGravitySeam space := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
  unfold recenteredContactJointResidualWithGravitySeam
  change
    diracDualFormNativeJointResidualOfActionJet positiveSmoothUnifiedSource
        (canonicalCauchySlicePoint 0 space) (sectionActionJet space) = _
  rw [sectionActionJet_eq_recenteredContactWithGravitySeam]

/-- Genuine residual of the matching source/action contact, read at the
global source occurrence but before the derived curvature assembly seam is
installed. -/
def recenteredContactJointResidualAtMatchingOccurrence
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualOfActionJet positiveSmoothUnifiedSource
    (canonicalCauchySlicePoint 0 space) (recenteredContactActionJet space)

/-- The sole assembly datum left by canonical diagonalization: global
curvature minus the curvature of the matching action-generated contact. -/
def recenteredContactGravityCurvatureAssemblySeam
    (space : StageNineSpatialPoint) : PhysicalBivector :=
  holonomicContravariantGravityCurvature SectionActual
      (canonicalCauchySlicePoint 0 space) -
    holonomicContravariantGravityCurvature
      (recenteredContactActual space) 0

/-- Whole carrier with the assembly seam routed only through the gravity
auxiliary equation.  All other coordinates remain the literal contact
residual. -/
def recenteredContactJointResidualWithClassifiedGravitySeam
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { recenteredContactJointResidualAtMatchingOccurrence space with
    gravityAuxiliary :=
      recenteredContactGravityCurvatureAssemblySeam space }

private theorem
    recenteredContactGravityAuxiliaryResidualWithSeam_eq_assemblySeam
    (space : StageNineSpatialPoint) :
    formNativeGravityAuxiliaryEulerResidual
        (recenteredContactPointFieldWithGravitySeam space) =
      recenteredContactGravityCurvatureAssemblySeam space := by
  have normal :=
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionResidual_gravityAuxiliary_normalForm
      0 space
  change
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField SectionActual
          (canonicalCauchySlicePoint 0 space)) =
      holonomicContravariantGravityCurvature SectionActual
          (canonicalCauchySlicePoint 0 space) -
        holonomicContravariantGravityCurvature
          (recenteredContactActual space)
          (canonicalCauchySlicePoint 0 0) at normal
  rw [canonicalCauchySlicePoint_zero_zero_local] at normal
  change
    formNativeGravityAuxiliaryEulerResidual
        (recenteredContactPointFieldWithGravitySeam space) = _
  rw [← sectionPointField_eq_recenteredContactWithGravitySeam space]
  exact normal

/-- The whole residual comparison separates the single diagonal-assembly
curvature seam from the literal residual of the matching action-generated
contact.  This classifies support; it does not construct a successor. -/
theorem recenteredContactJointResidualWithGravitySeam_classification
    (space : StageNineSpatialPoint) :
    recenteredContactJointResidualWithGravitySeam space =
      recenteredContactJointResidualWithClassifiedGravitySeam space := by
  have coframeOne :
      (recenteredContactActual space).coframe 0 = 1 := by
    change
      InputActual.coframe (canonicalSpatialContactTranslation space 0) = 1
    rw [canonicalSpatialContactTranslation_zero_local]
    exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have nondegenerate : Matrix.det
      ((recenteredContactActionJet space).pointField.coframe) ≠ 0 := by
    change Matrix.det ((recenteredContactActual space).coframe 0) ≠ 0
    rw [coframeOne]
    norm_num
  have dependency :=
    diracDualFormNativeJointResidualOfActionJet_withGravityCurvature
      positiveSmoothUnifiedSource (canonicalCauchySlicePoint 0 space)
      (recenteredContactActionJet space)
      ((toContinuumPointField SectionActual
        (canonicalCauchySlicePoint 0 space)).gravityCurvature)
      nondegenerate
  change
    recenteredContactJointResidualWithGravitySeam space =
      { recenteredContactJointResidualAtMatchingOccurrence space with
        gravityAuxiliary :=
          formNativeGravityAuxiliaryEulerResidual
            (recenteredContactPointFieldWithGravitySeam space) } at dependency
  rw [dependency,
    recenteredContactGravityAuxiliaryResidualWithSeam_eq_assemblySeam]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterActionJetNaturality
