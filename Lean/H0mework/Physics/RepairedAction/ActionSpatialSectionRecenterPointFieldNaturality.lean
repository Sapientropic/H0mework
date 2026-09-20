import H0mework.Physics.ConstitutiveAction.SpatialSectionGaugeClosure
import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterFirstJet

/-!
# Recentered point-field naturality of the repaired spatial section

For the fixed P506/L0 source, this module compares the already-generated
four-dimensional repaired section at `(0, space)` with the matching
source/action-generated recentered contact at its origin.  All point-field
coordinates agree simultaneously except the derived gravity curvature,
which is retained as one explicit assembly seam.

The theorem is a positive action-jet checkpoint.  It does not claim complete
residual naturality, does not assume the curvature seam is zero, and does not
construct a write from a residual coordinate or support branch.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000

local instance repairedRecenterP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

private abbrev InputActual :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev SectionActual :=
  FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

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
  simp

theorem spatiallyRecenterHolonomicConfiguration_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (space : StageNineSpatialPoint) :
    (spatiallyRecenterHolonomicConfiguration current space).Smooth := by
  have translationSmooth :
      ContDiff ℝ ∞ (canonicalSpatialContactTranslation space) := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  rcases smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, gaugeAuxiliary, scalar, matter, conjugateMatter⟩
  exact
    ⟨fun row column => by
        change ContDiff ℝ ∞
          ((fun point => current.coframe point row column) ∘
            canonicalSpatialContactTranslation space)
        exact (coframe row column).comp translationSmooth,
      fun direction internalOut internalIn => by
        change ContDiff ℝ ∞
          ((fun point => current.gravityConnection point direction
            internalOut internalIn) ∘
              canonicalSpatialContactTranslation space)
        exact (gravityConnection direction internalOut internalIn).comp
          translationSmooth,
      fun internalPair spacetimePair => by
        change ContDiff ℝ ∞
          ((fun point => current.gravityAuxiliary point internalPair
            spacetimePair) ∘ canonicalSpatialContactTranslation space)
        exact (gravityAuxiliary internalPair spacetimePair).comp
          translationSmooth,
      fun internalPair spacetimePair => by
        change ContDiff ℝ ∞
          ((fun point => current.gravitySimplicityMultiplier point
            internalPair spacetimePair) ∘
              canonicalSpatialContactTranslation space)
        exact (multiplier internalPair spacetimePair).comp translationSmooth,
      fun direction => by
        change ContDiff ℝ ∞
          ((fun point => p286CoordinateEquiv
            (current.gaugeConnection point direction)) ∘
              canonicalSpatialContactTranslation space)
        exact (gaugeConnection direction).comp translationSmooth,
      fun pair => by
        change ContDiff ℝ ∞
          ((fun point => p286CoordinateEquiv
            (current.gaugeAuxiliary point pair)) ∘
              canonicalSpatialContactTranslation space)
        exact (gaugeAuxiliary pair).comp translationSmooth,
      by
        change ContDiff ℝ ∞
          (current.scalar ∘ canonicalSpatialContactTranslation space)
        exact scalar.comp translationSmooth,
      by
        change ContDiff ℝ ∞
          ((fun point => matterCoordinateEquiv (current.matter point)) ∘
            canonicalSpatialContactTranslation space)
        exact matter.comp translationSmooth,
      fun index => by
        change ContDiff ℝ ∞
          ((fun point => current.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index 1))) ∘
                canonicalSpatialContactTranslation space)
        exact (conjugateMatter index).comp translationSmooth⟩

/-- Matching local action response generated after translating the fixed input
current so that `space` is the contact origin. -/
def recenteredContactActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    positiveSmoothUnifiedSource
    (spatiallyRecenterHolonomicConfiguration InputActual space)

/-- The recentered contact point field with only the assembled section's
derived gravity curvature retained. -/
def recenteredContactPointFieldWithGravitySeam
    (space : StageNineSpatialPoint) : StageNineContinuumPointField :=
  { toContinuumPointField (recenteredContactActual space) 0 with
    gravityCurvature :=
      (toContinuumPointField SectionActual
        (canonicalCauchySlicePoint 0 space)).gravityCurvature }

private theorem sectionScalarCovariantDerivative_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative SectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative (recenteredContactActual space) 0 := by
  funext direction
  change
    holonomicScalarCovariantDerivative
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          positiveSmoothUnifiedSource InputActual)
        (canonicalCauchySlicePoint 0 space) direction =
      holonomicScalarCovariantDerivative
        (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
          positiveSmoothUnifiedSource
          (spatiallyRecenterHolonomicConfiguration InputActual space))
        0 direction
  unfold holonomicScalarCovariantDerivative
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar,
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]
  change
    fieldDirectionalDerivative InputActual.scalar
          (canonicalCauchySlicePoint 0 space) direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (InputActual.gaugeConnection
              (canonicalCauchySlicePoint 0 space) direction))
          (InputActual.scalar (canonicalCauchySlicePoint 0 space)) =
      fieldDirectionalDerivative
          (InputActual.scalar ∘ canonicalSpatialContactTranslation space)
          0 direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (InputActual.gaugeConnection
              (canonicalSpatialContactTranslation space 0) direction))
          (InputActual.scalar (canonicalSpatialContactTranslation space 0))
  rw [fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
    InputActual.scalar space 0 direction]
  · simp [canonicalSpatialContactTranslation]
  · exact
      (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
        |>.differentiable (by simp)).differentiableAt

private theorem sectionMatterCovariantDerivative_eq_recenteredContact
    (space : StageNineSpatialPoint) :
    holonomicMatterCovariantDerivative SectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicMatterCovariantDerivative (recenteredContactActual space) 0 := by
  let current := spatiallyRecenterHolonomicConfiguration InputActual space
  have currentSmooth : current.Smooth :=
    spatiallyRecenterHolonomicConfiguration_smooth InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth space
  have currentDerivative (direction : LorentzianIndex) :
      holonomicMatterCovariantDerivative current 0 direction =
        holonomicMatterCovariantDerivative InputActual
          (canonicalCauchySlicePoint 0 space) direction := by
    unfold holonomicMatterCovariantDerivative
    change
      matterCoordinateEquiv.symm
            (fieldDirectionalDerivative
              ((fun point => matterCoordinateEquiv (InputActual.matter point)) ∘
                canonicalSpatialContactTranslation space)
              0 direction) + _ + _ = _
    rw [fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
      (fun point => matterCoordinateEquiv (InputActual.matter point))
      space 0 direction]
    · simp [current, spatiallyRecenterHolonomicConfiguration,
        canonicalSpatialContactTranslation]
    · exact
        (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
          |>.differentiable (by simp)).differentiableAt
  have currentCoframe : current.coframe 0 = 1 := by
    change InputActual.coframe
        (canonicalSpatialContactTranslation space 0) = 1
    rw [show canonicalSpatialContactTranslation space 0 =
        canonicalCauchySlicePoint 0 space by
      simp [canonicalSpatialContactTranslation]]
    exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have currentKnownVector :
      holonomicDiracDualCurrentCoframeMatterKnownVector current 0 =
        holonomicDiracDualIdentityCoframeMatterKnownVector InputActual
          (canonicalCauchySlicePoint 0 space) := by
    unfold holonomicDiracDualCurrentCoframeMatterKnownVector
      holonomicDiracDualIdentityCoframeMatterKnownVector
    rw [currentCoframe]
    rw [show
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet) =
          identityCoframeMatterGeometry by rfl]
    simp_rw [inverseCoframeDiracGamma_identity]
    simp_rw [currentDerivative]
    simp [current, spatiallyRecenterHolonomicConfiguration,
      canonicalSpatialContactTranslation]
  have contactToPrimal (direction : LorentzianIndex) :
      holonomicMatterCovariantDerivative (recenteredContactActual space) 0
          direction =
        holonomicMatterCovariantDerivative
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            current)
          0 direction := by
    change
      holonomicMatterCovariantDerivative
          (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
            positiveSmoothUnifiedSource current)
          0 direction = _
    unfold holonomicMatterCovariantDerivative
    rw [
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_matter,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gravityConnection_zero,
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]
    rfl
  funext direction
  rw [
    fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matterCovariantDerivative_zeroSlice_actionNormalForm]
  rw [contactToPrimal direction]
  obtain rfl | ⟨spatialDirection, rfl⟩ := direction.eq_zero_or_eq_succ
  · have contactTime :=
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_timeCovariantDerivative
        current currentSmooth
    have generatedTime :
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
            current 0 =
          -identityCoframeMatterTimePrincipal
            (holonomicDiracDualIdentityCoframeMatterKnownVector InputActual
              (canonicalCauchySlicePoint 0 space)) := by
      unfold
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        actionGeneratedCurrentCoframeMatterTemporalDerivative
      rw [currentCoframe, currentKnownVector,
        currentCoframeMatterTemporalPrincipalInverse_one]
    simpa only [canonicalLorentzianTimeDirection, if_pos] using
      (contactTime.trans generatedTime).symm
  · have contactSpatial :=
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_spatialCovariantDerivative
        current currentSmooth spatialDirection
    simpa only [canonicalLorentzianTimeDirection, Fin.succ_ne_zero, if_false]
      using (contactSpatial.trans (currentDerivative spatialDirection.succ)).symm

/-- Whole point-field naturality on the generated zero slice.  The record
update makes the sole unproved assembly coordinate explicit: every other
point-field coordinate, including scalar and matter covariant first jets,
comes from the matching recentered action contact. -/
theorem sectionPointField_eq_recenteredContactWithGravitySeam
    (space : StageNineSpatialPoint) :
    toContinuumPointField SectionActual (canonicalCauchySlicePoint 0 space) =
      recenteredContactPointFieldWithGravitySeam space := by
  apply StageNineContinuumPointField.ext
  case coframe =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).coframe
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).coframe 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe_slice
        positiveSmoothUnifiedSource InputActual 0 space
  case gravityCurvature =>
    rfl
  case gaugeCurvature =>
    change
      holonomicGaugeCurvature SectionActual
          (canonicalCauchySlicePoint 0 space) =
        holonomicGaugeCurvature (recenteredContactActual space) 0
    calc
      holonomicGaugeCurvature SectionActual
          (canonicalCauchySlicePoint 0 space) =
          holonomicGaugeCurvature InputActual
            (canonicalCauchySlicePoint 0 space) := by
        exact holonomicGaugeCurvature_eq_of_connection_eq_current
          SectionActual InputActual
          (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
            positiveSmoothUnifiedSource InputActual)
          _
      _ = holonomicGaugeCurvature
          (spatiallyRecenterHolonomicConfiguration InputActual space) 0 := by
        rw [holonomicGaugeCurvature_spatiallyRecenter InputActual
          fixedP506FormNativeJointActionSolvedSuccessor_smooth]
        simp [canonicalSpatialContactTranslation]
      _ = holonomicGaugeCurvature (recenteredContactActual space) 0 := by
        symm
        exact holonomicGaugeCurvature_eq_of_connection_eq_current
          (recenteredContactActual space)
          (spatiallyRecenterHolonomicConfiguration InputActual space)
          (diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection
            positiveSmoothUnifiedSource _)
          0
  case gravityAuxiliary =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).gravityAuxiliary
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).gravityAuxiliary 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gravityAuxiliary_slice
        positiveSmoothUnifiedSource InputActual 0 space
  case gravitySimplicityMultiplier =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).gravitySimplicityMultiplier
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).gravitySimplicityMultiplier 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_multiplier_slice
        positiveSmoothUnifiedSource InputActual 0 space
  case gaugeAuxiliary =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).gaugeAuxiliary
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).gaugeAuxiliary 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice
        positiveSmoothUnifiedSource InputActual 0 space
  case scalar =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).scalar
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).scalar 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar_slice
        positiveSmoothUnifiedSource InputActual 0 space
  case scalarCovariantDerivative =>
    exact sectionScalarCovariantDerivative_eq_recenteredContact space
  case matter =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).matter
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).matter 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_matter_slice
        positiveSmoothUnifiedSource InputActual 0 space
  case matterCovariantDerivative =>
    exact sectionMatterCovariantDerivative_eq_recenteredContact space
  case conjugateMatter =>
    change
      (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource InputActual).conjugateMatter
          (canonicalCauchySlicePoint 0 space) =
        (recenteredContactActual space).conjugateMatter 0
    simpa only [recenteredContactActual,
      canonicalCauchySlicePoint_zero_zero_local] using
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_slice
        positiveSmoothUnifiedSource InputActual 0 space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
