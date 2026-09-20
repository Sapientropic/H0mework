import H0mework.Physics.JointVariation.GeneratedProfilesFixed
import H0mework.Physics.JointVariation.GeneratedProfilesFixedRegularity
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyCurvatureTargetSpatialRegularity
import H0mework.Physics.FixedJoint.FixedP286RequiredExteriorDerivativeSpatialRegularity
import H0mework.Physics.ScalarJets.FixedScalarAccelerationSpatialRegularity
import H0mework.Physics.FinalJoint.FixedPointwiseJointResidualNormalForm
import H0mework.Physics.RepairedAction.ActionSpatialSectionAdjointResponseRegularity
import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterFirstJet

/-!
# Fixed P506/L0 complete-joint global-section regularity

The complete-joint spacetime operator is already one source/current-only
four-dimensional write.  This module unfolds its fixed P506/L0 affine and
quadratic normal forms and proves regularity of that one global actual.  The
proof never accepts a contact family, residual, seam, target field, branch,
or smoothness receipt as producer input.

The resulting `Smooth` theorem is intended for the full-occurrence
action-jet comparison.  It is not a claim that the section is already in the
all-point zero fiber.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineConjugateMatterVariation
open StageNineBlockwiseConstitutive
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperatorFixedP506Specialization
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506ECFullCauchyCurvatureTargetSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286RequiredExteriorDerivativeSpatialRegularity
open StageNineDiracDualFormNativeFixedP506ScalarAccelerationSpatialRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointResponseRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineScalarActionSecondJetLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance completeJointGlobalP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance completeJointGlobalP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance completeJointGlobalP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem normalizedAffineLorentzConnectionField_joint_contDiff
    (origin : BasePoint → PointwiseLorentzSpinConnection)
    (target : BasePoint → PhysicalBivector)
    (localPoint : BasePoint → BasePoint)
    (originSmooth : ∀ formDirection internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        origin point formDirection internalOut internalIn)
    (targetSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        target point internalPair spacetimePair)
    (localPointSmooth : ContDiff ℝ ∞ localPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      normalizedAffineLorentzConnectionField
          (origin point) (target point) (localPoint point)
          formDirection internalOut internalIn := by
  unfold normalizedAffineLorentzConnectionField
    StageNineLorentzConnectionVariation.lorentzSkewConnectionOfBivectorOneForm
    StageNineLorentzConnectionVariation.loweredLorentzBivectorMatrix
    normalizedAffineBivectorOneForm
    normalizedAffineBivectorComponentLinear
    normalizedDerivativeBivector
    originLorentzBracketCurvature
  fun_prop

private theorem originLorentzBracketCurvature_joint_component_contDiff
    (connection : BasePoint → PointwiseLorentzSpinConnection)
    (connectionSmooth : ∀ formDirection internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        connection point formDirection internalOut internalIn)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      originLorentzBracketCurvature (connection point)
        internalPair spacetimePair := by
  unfold originLorentzBracketCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.sum
  intro middle _
  exact
    ((connectionSmooth (pairFirst spacetimePair)
        (pairFirst internalPair) middle).mul
      (connectionSmooth (pairSecond spacetimePair)
        middle (pairSecond internalPair))).sub
    ((connectionSmooth (pairSecond spacetimePair)
        (pairFirst internalPair) middle).mul
      (connectionSmooth (pairFirst spacetimePair)
        middle (pairSecond internalPair)))

private theorem normalizedAffineGravityCurvature_joint_component_contDiff
    (origin : BasePoint → PointwiseLorentzSpinConnection)
    (target : BasePoint → PhysicalBivector)
    (localPoint : BasePoint → BasePoint)
    (originSmooth : ∀ formDirection internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        origin point formDirection internalOut internalIn)
    (targetSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        target point internalPair spacetimePair)
    (localPointSmooth : ContDiff ℝ ∞ localPoint)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicGravityCurvature
        (normalizedAffineConfiguration (origin point) (target point))
        (localPoint point) internalPair spacetimePair := by
  rw [show
    (fun point =>
      holonomicGravityCurvature
          (normalizedAffineConfiguration (origin point) (target point))
          (localPoint point) internalPair spacetimePair) =
      fun point =>
        (target point - originLorentzBracketCurvature (origin point) +
          originLorentzBracketCurvature
            (normalizedAffineLorentzConnectionField
              (origin point) (target point) (localPoint point)))
          internalPair spacetimePair by
    funext point
    rw [
      SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseAwayCurvatureNoGo.holonomicGravityCurvature_normalizedAffineConfiguration_at]]
  exact
    ((targetSmooth internalPair spacetimePair).sub
      (originLorentzBracketCurvature_joint_component_contDiff
        origin originSmooth internalPair spacetimePair)).add
      (originLorentzBracketCurvature_joint_component_contDiff
        (fun point =>
          normalizedAffineLorentzConnectionField
            (origin point) (target point) (localPoint point))
        (normalizedAffineLorentzConnectionField_joint_contDiff
          origin target localPoint originSmooth targetSmooth localPointSmooth)
        internalPair spacetimePair)

private theorem gravityInternalDualEquiv_joint_component_contDiff
    (bivector : BasePoint → PhysicalBivector)
    (bivectorSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        bivector point internalPair spacetimePair)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (bivector point)
        internalPair spacetimePair := by
  fin_cases internalPair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      bivectorSmooth 3 spacetimePair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      bivectorSmooth 4 spacetimePair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      bivectorSmooth 5 spacetimePair
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      (bivectorSmooth 0 spacetimePair).neg
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      (bivectorSmooth 1 spacetimePair).neg
  · simpa [gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge] using
      (bivectorSmooth 2 spacetimePair).neg

private theorem
    normalizedAffineContravariantGravityCurvature_joint_component_contDiff
    (origin : BasePoint → PointwiseLorentzSpinConnection)
    (target : BasePoint → PhysicalBivector)
    (localPoint : BasePoint → BasePoint)
    (originSmooth : ∀ formDirection internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        origin point formDirection internalOut internalIn)
    (targetSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        target point internalPair spacetimePair)
    (localPointSmooth : ContDiff ℝ ∞ localPoint)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature
        (normalizedAffineConfiguration (origin point) (target point))
        (localPoint point) internalPair spacetimePair := by
  rw [show
    (fun point =>
      holonomicContravariantGravityCurvature
          (normalizedAffineConfiguration (origin point) (target point))
          (localPoint point) internalPair spacetimePair) =
      fun point => lorentzianTwoFormSign internalPair *
        holonomicGravityCurvature
          (normalizedAffineConfiguration (origin point) (target point))
          (localPoint point) internalPair spacetimePair by
    funext point
    rfl]
  exact contDiff_const.mul
    (normalizedAffineGravityCurvature_joint_component_contDiff
      origin target localPoint originSmooth targetSmooth localPointSmooth
      internalPair spacetimePair)

private theorem holonomicGravityCurvature_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gravityConnection = second.gravityConnection)
    (point : BasePoint) :
    holonomicGravityCurvature first point =
      holonomicGravityCurvature second point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connectionEq]

private theorem formNativeP286CanonicalAuxiliaryIncrement_joint_contDiff
    (origin : BasePoint → P286GaugeTwoForm)
    (target : BasePoint → P286GaugeThreeForm)
    (localPoint : BasePoint → BasePoint)
    (originSmooth : ∀ pair,
      ContDiff ℝ ∞ fun point => origin point pair)
    (targetSmooth : ∀ triple,
      ContDiff ℝ ∞ fun point => target point triple)
    (localPointSmooth : ContDiff ℝ ∞ localPoint)
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      origin point pair +
        formNativeP286CanonicalAuxiliaryIncrement
          (target point) (localPoint point) pair := by
  unfold formNativeP286CanonicalAuxiliaryIncrement
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
  fin_cases pair <;>
    simp [Fin.sum_univ_four,
      StageNineP286ActionVelocityLocalActualLift.localBaseCoordinate_apply] <;>
    fun_prop

private theorem scalarQuadraticTimeCorrection_joint_contDiff
    (acceleration : BasePoint → ScalarCoordinateCarrier)
    (localPoint : BasePoint → BasePoint)
    (accelerationSmooth : ContDiff ℝ ∞ acceleration)
    (localPointSmooth : ContDiff ℝ ∞ localPoint) :
    ContDiff ℝ ∞ fun point =>
      scalarQuadraticTimeCorrection
        (acceleration point) (localPoint point) := by
  unfold scalarQuadraticTimeCorrection scalarQuadraticTimeCoefficient
  fun_prop

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev GlobalActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private theorem completeJointActionMatchingContactPoint_contDiff :
    ContDiff ℝ ∞ completeJointActionMatchingContactPoint := by
  rw [show completeJointActionMatchingContactPoint =
      fun point =>
        canonicalTimeProjection point •
          coordinateDirection canonicalLorentzianTimeDirection by
    funext point
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [completeJointActionMatchingContactPoint,
        canonicalCauchySlicePoint, canonicalTimeProjection,
        canonicalLorentzianTimeDirection, coordinateDirection,
        Fin.sum_univ_three]]
  exact canonicalTimeProjection.contDiff.smul contDiff_const

/-! ## One fixed-lineage global write -/

theorem fixedP506L0CompleteJointActionSpacetimeSection_eq_contactDiagonal :
    GlobalActual =
      spatialContactTimeAxisDiagonal fixedP506L0FinalCommonActionActual := by
  unfold GlobalActual
    fixedP506L0CompleteJointActionSpacetimeSectionActual
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
  apply congrArg spatialContactTimeAxisDiagonal
  funext space
  unfold completeJointActionSpatialContact
  change
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator
        positiveSmoothUnifiedSource (fixedP506L0CartanRestartActual space) =
      fixedP506L0FinalCommonActionActual space
  exact
    sourceActionGeneratedDiracDualCompleteJointActionResponseOperator_fixed
      space

/-! ## Primitive fields inherited globally -/

theorem fixedP506L0CompleteJointActionSpacetimeSection_coframe_contDiff :
    ContDiff ℝ ∞ GlobalActual.coframe := by
  rw [show GlobalActual.coframe = InputActual.coframe by
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe
        positiveSmoothUnifiedSource InputActual]
  exact holonomicCoframe_contDiff InputActual
    fixedP506FormNativeJointActionSolvedSuccessor_smooth

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gaugeConnection_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (GlobalActual.gaugeConnection point direction) := by
  rw [show GlobalActual.gaugeConnection = InputActual.gaugeConnection by
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource InputActual]
  exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
    direction

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gravityAuxiliary_contDiff :
    ContDiff ℝ ∞ GlobalActual.gravityAuxiliary := by
  rw [show GlobalActual.gravityAuxiliary =
      fun point => physicalIIPlusBivector (InputActual.coframe point) by
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary
        positiveSmoothUnifiedSource InputActual]
  exact physicalIIPlusBivector_contDiff.comp
    (holonomicCoframe_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth)

/-! ## Scalar affine/quadratic normal form -/

theorem fixedP506L0CompleteJointActionSpacetimeSection_scalar_normalForm
    (point : BasePoint) :
    GlobalActual.scalar point =
      InputActual.scalar point +
        scalarQuadraticTimeCorrection
          (recenteredContactDiracDualScalarAcceleration
            (canonicalSpatialProjection point))
          (canonicalCauchySlicePoint (canonicalTimeProjection point) 0) := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      positiveSmoothUnifiedSource InputActual).scalar point = _
  rw [sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_scalar_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact point).scalar
        (completeJointActionMatchingContactPoint point) = _
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  rw [fixedP506L0FinalCommonActionActual_scalar_point_normalForm]
  simp [fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration,
    completeJointActionMatchingContactPoint,
    canonicalSpatialContactTranslation_timeAxis]
  rw [canonicalCauchySlicePoint_projections]

theorem fixedP506L0CompleteJointActionSpacetimeSection_scalar_contDiff :
    ContDiff ℝ ∞ GlobalActual.scalar := by
  rw [show GlobalActual.scalar = fun point =>
      InputActual.scalar point +
        scalarQuadraticTimeCorrection
          (recenteredContactDiracDualScalarAcceleration
            (canonicalSpatialProjection point))
          (completeJointActionMatchingContactPoint point) by
    funext point
    rw [fixedP506L0CompleteJointActionSpacetimeSection_scalar_normalForm]
    rfl]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.add
      (scalarQuadraticTimeCorrection_joint_contDiff
        (fun point => recenteredContactDiracDualScalarAcceleration
          (canonicalSpatialProjection point))
        completeJointActionMatchingContactPoint
        (recenteredContactDiracDualScalarAcceleration_contDiff.comp
          canonicalSpatialProjection.contDiff)
        completeJointActionMatchingContactPoint_contDiff)

/-! ## Primal and adjoint affine normal forms -/

theorem fixedP506L0CompleteJointActionSpacetimeSection_matter_normalForm
    (point : BasePoint) :
    matterCoordinateEquiv (GlobalActual.matter point) =
      matterCoordinateEquiv (InputActual.matter point) +
        canonicalTimeProjection point •
          matterCoordinateEquiv
            (diracDualCurrentCoframeMatterTimeResponseWrite
              (fixedP506L0CartanRestartActual
                (canonicalSpatialProjection point))) := by
  change
    matterCoordinateEquiv
        ((sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          positiveSmoothUnifiedSource InputActual).matter point) = _
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_matter_at]
  change
    matterCoordinateEquiv
        ((fixedP506L0CompleteJointActionMatchingContact point).matter
          (completeJointActionMatchingContactPoint point)) = _
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  rw [fixedP506L0FinalCommonActionActual_matter_point_normalForm]
  simp [fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration,
    completeJointActionMatchingContactPoint,
    canonicalSpatialContactTranslation_timeAxis,
    matterLinearTimeCoordinateWrite]
  rw [canonicalCauchySlicePoint_projections]

theorem fixedP506L0CompleteJointActionSpacetimeSection_matter_contDiff :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (GlobalActual.matter point) := by
  rw [show
    (fun point => matterCoordinateEquiv (GlobalActual.matter point)) =
      fun point =>
        matterCoordinateEquiv (InputActual.matter point) +
          canonicalTimeProjection point •
            matterCoordinateEquiv
              (diracDualCurrentCoframeMatterTimeResponseWrite
                (fixedP506L0CartanRestartActual
                  (canonicalSpatialProjection point))) by
    funext point
    exact
      fixedP506L0CompleteJointActionSpacetimeSection_matter_normalForm point]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.add
      (canonicalTimeProjection.contDiff.smul
        (fixedP506L0CompleteJointMatterResponseWrite_contDiff.comp
          canonicalSpatialProjection.contDiff))

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_normalForm
    (point : BasePoint) :
    matterDualCoordinates (GlobalActual.conjugateMatter point) =
      matterDualCoordinates (InputActual.conjugateMatter point) +
        canonicalTimeProjection point •
          matterDualCoordinates
            (liveCoframeConjugateMatterTimeResponseWrite
              (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
                (fixedP506L0CartanRestartActual
                  (canonicalSpatialProjection point)))) := by
  change
    matterDualCoordinates
        ((sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          positiveSmoothUnifiedSource InputActual).conjugateMatter point) = _
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_conjugateMatter_at]
  change
    matterDualCoordinates
        ((fixedP506L0CompleteJointActionMatchingContact point).conjugateMatter
          (completeJointActionMatchingContactPoint point)) = _
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter_point_normalForm]
  simp [fixedP506L0RecenteredInput,
    spatiallyRecenterHolonomicConfiguration,
    completeJointActionMatchingContactPoint,
    canonicalSpatialContactTranslation_timeAxis,
    conjugateMatterLinearTimeCoordinateWrite]
  rw [canonicalCauchySlicePoint_projections]

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_field_normalForm
    (point : BasePoint) :
    GlobalActual.conjugateMatter point =
      InputActual.conjugateMatter point +
        canonicalTimeProjection point •
          liveCoframeConjugateMatterTimeResponseWrite
            (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
              (fixedP506L0CartanRestartActual
                (canonicalSpatialProjection point))) := by
  calc
    GlobalActual.conjugateMatter point =
        matterDualOfCoordinates
          (matterDualCoordinates (GlobalActual.conjugateMatter point)) := by
      exact
        (matterDualOfCoordinates_surjective
          (GlobalActual.conjugateMatter point)).symm
    _ =
        matterDualOfCoordinates
          (matterDualCoordinates (InputActual.conjugateMatter point) +
            canonicalTimeProjection point •
              matterDualCoordinates
                (liveCoframeConjugateMatterTimeResponseWrite
                  (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
                    (fixedP506L0CartanRestartActual
                      (canonicalSpatialProjection point))))) := by
      rw [
        fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_normalForm]
    _ = _ := by
      rw [matterDualOfCoordinates_add, matterDualOfCoordinates_real_smul,
        matterDualOfCoordinates_surjective,
        matterDualOfCoordinates_surjective]

private def adjointRegularityComparison
    (adjoint : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { coframe := fun _ => 0
    gravityConnection := fun _ _ _ _ => 0
    gravityAuxiliary := fun _ _ _ => 0
    gravitySimplicityMultiplier := fun _ _ _ => 0
    gaugeConnection := fun _ _ => 0
    gaugeAuxiliary := fun _ _ => 0
    scalar := fun _ => 0
    matter := fun _ => 0
    conjugateMatter := adjoint }

private theorem matterDualCoordinates_contDiff_of_apply
    (adjoint : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (adjointSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ fun point =>
        adjoint point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) :
    ContDiff ℝ ∞ fun point => matterDualCoordinates (adjoint point) := by
  have comparisonSmooth : (adjointRegularityComparison adjoint).Smooth := by
    unfold StageNineHolonomicConfiguration.Smooth
    dsimp only [adjointRegularityComparison]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intros
      fun_prop
    · intros
      fun_prop
    · intros
      fun_prop
    · intros
      fun_prop
    · intro
      fun_prop
    · intro
      fun_prop
    · fun_prop
    · fun_prop
    · exact adjointSmooth
  have coordinatesSmooth :=
    StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates_contDiff
      (adjointRegularityComparison adjoint) comparisonSmooth
  change ContDiff ℝ ∞ (fun point => matterDualCoordinates (adjoint point))
    at coordinatesSmooth
  exact coordinatesSmooth

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ fun point =>
      matterDualCoordinates (GlobalActual.conjugateMatter point) := by
  have inputSmooth :=
    StageNineHolonomicIdentityCoframeConjugateMatterActionResponse.holonomicConjugateMatterCoordinates_contDiff
      InputActual fixedP506FormNativeJointActionSolvedSuccessor_smooth
  change ContDiff ℝ ∞ fun point =>
    matterDualCoordinates (InputActual.conjugateMatter point) at inputSmooth
  let response : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier :=
    fun point =>
      liveCoframeConjugateMatterTimeResponseWrite
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual
            (canonicalSpatialProjection point)))
  have responseSmooth : ContDiff ℝ ∞ fun point =>
      matterDualCoordinates (response point) :=
    matterDualCoordinates_contDiff_of_apply response (fun index => by
      change ContDiff ℝ ∞ fun point =>
        liveCoframeConjugateMatterTimeResponseWrite
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            (fixedP506L0CartanRestartActual
              (canonicalSpatialProjection point)))
          (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))
      exact
        (fixedP506L0CompleteJointAdjointResponseWrite_direct_apply_contDiff
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index 1))).comp
          canonicalSpatialProjection.contDiff)
  rw [show
    (fun point => matterDualCoordinates (GlobalActual.conjugateMatter point)) =
      fun point =>
        matterDualCoordinates (InputActual.conjugateMatter point) +
          canonicalTimeProjection point • matterDualCoordinates (response point) by
    funext point
    exact
      fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_normalForm
        point]
  exact inputSmooth.add
    (canonicalTimeProjection.contDiff.smul responseSmooth)

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_contDiff
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ fun point : BasePoint =>
      GlobalActual.conjugateMatter point
        (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)) := by
  let evaluation : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation
      (matterCoordinateEquiv.symm
        (EuclideanSpace.single index 1))).restrictScalars ℝ
  have composed : ContDiff ℝ ∞ fun point =>
      evaluation
        (matterDualCoordinates (GlobalActual.conjugateMatter point)) :=
    evaluation.contDiff.comp
      fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatterCoordinates_contDiff
  rw [show
    (fun point =>
      evaluation (matterDualCoordinates (GlobalActual.conjugateMatter point))) =
      fun point => GlobalActual.conjugateMatter point
        (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)) by
    funext point
    dsimp only [evaluation]
    change
      StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation
          (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))
          (matterDualCoordinates (GlobalActual.conjugateMatter point)) =
        GlobalActual.conjugateMatter point
          (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))
    rw [StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport.matterDualCoordinateEvaluation_apply,
      matterDualOfCoordinates_surjective]] at composed
  exact composed

/-! ## Generated Einstein--Cartan connection normal form -/

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_normalForm
    (point : BasePoint) :
    GlobalActual.gravityConnection point =
      normalizedAffineLorentzConnectionField
          (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual
              (canonicalSpatialProjection point)))
          (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual
              (canonicalSpatialProjection point)))
          (completeJointActionMatchingContactPoint point) := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      positiveSmoothUnifiedSource InputActual).gravityConnection point = _
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityConnection_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact point).gravityConnection
        (completeJointActionMatchingContactPoint point) = _
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  unfold fixedP506L0FinalCommonActionActual
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_eq_normalizedAffine]

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      GlobalActual.gravityConnection point
        formDirection internalOut internalIn := by
  rw [show
    (fun point =>
      GlobalActual.gravityConnection point
        formDirection internalOut internalIn) =
      fun point =>
        normalizedAffineLorentzConnectionField
            (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual
                (canonicalSpatialProjection point)))
            (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual
                (canonicalSpatialProjection point)))
            (completeJointActionMatchingContactPoint point)
            formDirection internalOut internalIn by
    funext point
    exact congrFun (congrFun (congrFun
      (fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_normalForm
        point) formDirection) internalOut) internalIn]
  exact
    normalizedAffineLorentzConnectionField_joint_contDiff
      (fun point =>
        sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual
            (canonicalSpatialProjection point)))
      (fun point =>
        sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual
            (canonicalSpatialProjection point)))
      completeJointActionMatchingContactPoint
      (fun direction out inn =>
        (fixedP506L0FinalCommonPreECConnectionOrigin_component_contDiff
          direction out inn).comp canonicalSpatialProjection.contDiff)
      (fun internal spacetime =>
        (fixedP506L0FinalCommonPreECFullCauchyCurvatureTarget_component_contDiff
          internal spacetime).comp canonicalSpatialProjection.contDiff)
      completeJointActionMatchingContactPoint_contDiff
      formDirection internalOut internalIn

/-! ## Generated P286 auxiliary normal form -/

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate GlobalActual point =
      currentP286OriginAuxiliaryCoordinate
          (recenteredCartanRepairedScalarSecondJetActual
            (canonicalSpatialProjection point)) +
        formNativeP286CanonicalAuxiliaryIncrement
          (formNativeCurrentP286RequiredExteriorDerivative
            positiveSmoothUnifiedSource
            (recenteredCartanRepairedScalarSecondJetActual
              (canonicalSpatialProjection point)))
          (completeJointActionMatchingContactPoint point) := by
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          positiveSmoothUnifiedSource InputActual) point = _
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeAuxiliary_at]
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (fixedP506L0CompleteJointActionMatchingContact point)
        (completeJointActionMatchingContactPoint point) = _
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  exact
    fixedP506L0FinalCommonActionActual_gaugeAuxiliaryCoordinate_normalForm
      (canonicalSpatialProjection point)
      (completeJointActionMatchingContactPoint point)

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_contDiff
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (GlobalActual.gaugeAuxiliary point pair) := by
  rw [show
    (fun point =>
      p286CoordinateEquiv (GlobalActual.gaugeAuxiliary point pair)) =
    fun point =>
      currentP286OriginAuxiliaryCoordinate
            (recenteredCartanRepairedScalarSecondJetActual
              (canonicalSpatialProjection point)) pair +
        formNativeP286CanonicalAuxiliaryIncrement
            (formNativeCurrentP286RequiredExteriorDerivative
              positiveSmoothUnifiedSource
              (recenteredCartanRepairedScalarSecondJetActual
                (canonicalSpatialProjection point)))
            (completeJointActionMatchingContactPoint point) pair by
    funext point
    exact congrFun
      (fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_normalForm
        point) pair]
  exact
    formNativeP286CanonicalAuxiliaryIncrement_joint_contDiff
      (fun point =>
        currentP286OriginAuxiliaryCoordinate
          (recenteredCartanRepairedScalarSecondJetActual
            (canonicalSpatialProjection point)))
      (fun point =>
        formNativeCurrentP286RequiredExteriorDerivative
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedScalarSecondJetActual
            (canonicalSpatialProjection point)))
      completeJointActionMatchingContactPoint
      (fun candidatePair =>
        (fixedP506L0CompleteJointP286OriginAuxiliary_component_contDiff
          candidatePair).comp canonicalSpatialProjection.contDiff)
      (fun triple =>
        (fixedP506L0RecenteredCartanRequiredExteriorDerivative_component_contDiff
          triple).comp canonicalSpatialProjection.contDiff)
      completeJointActionMatchingContactPoint_contDiff pair

/-! ## Source-generated gravity reaction normal form -/

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_multiplier_normalForm
    (point : BasePoint) :
    GlobalActual.gravitySimplicityMultiplier point =
      formNativeGravityReactionField
        (fixedP506L0FinalCommonActionActual
          (canonicalSpatialProjection point))
        (completeJointActionMatchingContactPoint point) := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      positiveSmoothUnifiedSource InputActual).gravitySimplicityMultiplier
        point = _
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_multiplier_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact point
      ).gravitySimplicityMultiplier
        (completeJointActionMatchingContactPoint point) = _
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
  exact congrFun
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reactionSelfGenerated
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonPreECActionActual
        (canonicalSpatialProjection point)))
    (completeJointActionMatchingContactPoint point)

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_multiplier_algebraic_normalForm
    (point : BasePoint) :
    GlobalActual.gravitySimplicityMultiplier point =
      gravityInternalDualEquiv (GlobalActual.gravityAuxiliary point) -
        holonomicContravariantGravityCurvature
          (normalizedAffineConfiguration
            (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual
                (canonicalSpatialProjection point)))
            (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
              positiveSmoothUnifiedSource
              (fixedP506L0FinalCommonPreECActionActual
                (canonicalSpatialProjection point))))
          (completeJointActionMatchingContactPoint point) := by
  let space := canonicalSpatialProjection point
  let localPoint := completeJointActionMatchingContactPoint point
  have auxiliaryEq :
      (fixedP506L0FinalCommonActionActual space).gravityAuxiliary localPoint =
        GlobalActual.gravityAuxiliary point := by
    have generated :=
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityAuxiliary_at
        positiveSmoothUnifiedSource InputActual point
    change
      GlobalActual.gravityAuxiliary point =
        (fixedP506L0CompleteJointActionMatchingContact point
          ).gravityAuxiliary localPoint at generated
    rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
      at generated
    exact generated.symm
  have connectionEq :
      (fixedP506L0FinalCommonActionActual space).gravityConnection =
        (normalizedAffineConfiguration
          (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space))
          (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual space))).gravityConnection := by
    unfold fixedP506L0FinalCommonActionActual
    exact
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_eq_normalizedAffine
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)
  rw [fixedP506L0CompleteJointActionSpacetimeSection_multiplier_normalForm]
  unfold formNativeGravityReactionField
  rw [auxiliaryEq]
  unfold holonomicContravariantGravityCurvature
  rw [holonomicGravityCurvature_eq_of_connection_eq
    (fixedP506L0FinalCommonActionActual space)
    (normalizedAffineConfiguration
      (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space))
      (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space)))
    connectionEq localPoint]

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_multiplier_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      GlobalActual.gravitySimplicityMultiplier point
        internalPair spacetimePair := by
  rw [show
    (fun point =>
      GlobalActual.gravitySimplicityMultiplier point
        internalPair spacetimePair) =
      fun point =>
        gravityInternalDualEquiv (GlobalActual.gravityAuxiliary point)
              internalPair spacetimePair -
          holonomicContravariantGravityCurvature
            (normalizedAffineConfiguration
              (sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
                positiveSmoothUnifiedSource
                (fixedP506L0FinalCommonPreECActionActual
                  (canonicalSpatialProjection point)))
              (sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
                positiveSmoothUnifiedSource
                (fixedP506L0FinalCommonPreECActionActual
                  (canonicalSpatialProjection point))))
            (completeJointActionMatchingContactPoint point)
            internalPair spacetimePair by
    funext point
    exact congrFun (congrFun
      (fixedP506L0CompleteJointActionSpacetimeSection_multiplier_algebraic_normalForm
        point) internalPair) spacetimePair]
  exact
    (gravityInternalDualEquiv_joint_component_contDiff
      GlobalActual.gravityAuxiliary
      (fun internal spacetime =>
        contDiff_pi.mp
          (contDiff_pi.mp
            fixedP506L0CompleteJointActionSpacetimeSection_gravityAuxiliary_contDiff
            internal)
          spacetime)
      internalPair spacetimePair).sub
      (normalizedAffineContravariantGravityCurvature_joint_component_contDiff
        (fun point =>
          sourceActionGeneratedDiracDualECFullCauchyConnectionOrigin
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual
              (canonicalSpatialProjection point)))
        (fun point =>
          sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
            positiveSmoothUnifiedSource
            (fixedP506L0FinalCommonPreECActionActual
              (canonicalSpatialProjection point)))
        completeJointActionMatchingContactPoint
        (fun direction out inn =>
          (fixedP506L0FinalCommonPreECConnectionOrigin_component_contDiff
            direction out inn).comp canonicalSpatialProjection.contDiff)
        (fun internal spacetime =>
          (fixedP506L0FinalCommonPreECFullCauchyCurvatureTarget_component_contDiff
            internal spacetime).comp canonicalSpatialProjection.contDiff)
      completeJointActionMatchingContactPoint_contDiff
      internalPair spacetimePair)

private theorem fixedP506L0CompleteJointActionSpacetimeSection_gravitySmooth :
    (∀ row column,
      ContDiff ℝ ∞ fun point =>
        GlobalActual.coframe point row column) ∧
    (∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        GlobalActual.gravityConnection point
          direction internalOut internalIn) ∧
    (∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        GlobalActual.gravityAuxiliary point
          internalPair spacetimePair) ∧
    (∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        GlobalActual.gravitySimplicityMultiplier point
          internalPair spacetimePair) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro row column
    exact
      contDiff_pi.mp
        (contDiff_pi.mp
          fixedP506L0CompleteJointActionSpacetimeSection_coframe_contDiff
          row)
        column
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_contDiff
  · intro internalPair spacetimePair
    exact
      contDiff_pi.mp
        (contDiff_pi.mp
          fixedP506L0CompleteJointActionSpacetimeSection_gravityAuxiliary_contDiff
          internalPair)
        spacetimePair
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_multiplier_contDiff

private theorem fixedP506L0CompleteJointActionSpacetimeSection_matterGaugeSmooth :
    (∀ direction,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv
          (GlobalActual.gaugeConnection point direction)) ∧
    (∀ pair,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv
          (GlobalActual.gaugeAuxiliary point pair)) ∧
    ContDiff ℝ ∞ GlobalActual.scalar ∧
    ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv (GlobalActual.matter point)) ∧
    (∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞ fun point =>
        GlobalActual.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index 1))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_gaugeConnection_contDiff
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_contDiff
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_scalar_contDiff
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_matter_contDiff
  · exact
      fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_contDiff

private theorem nineWayAnd_of_fourAnd_five
    {first second third fourth fifth sixth seventh eighth ninth : Prop}
    (head : first ∧ second ∧ third ∧ fourth)
    (tail : fifth ∧ sixth ∧ seventh ∧ eighth ∧ ninth) :
    first ∧ second ∧ third ∧ fourth ∧ fifth ∧ sixth ∧ seventh ∧ eighth ∧
      ninth :=
  ⟨head.1, head.2.1, head.2.2.1, head.2.2.2,
    tail.1, tail.2.1, tail.2.2.1, tail.2.2.2.1, tail.2.2.2.2⟩

private theorem stageNineSmooth_of_gravity_and_matterGauge
    (configuration : StageNineHolonomicConfiguration)
    (gravitySmooth :
      (∀ row column,
        ContDiff ℝ ∞ fun point =>
          configuration.coframe point row column) ∧
      (∀ direction internalOut internalIn,
        ContDiff ℝ ∞ fun point =>
          configuration.gravityConnection point
            direction internalOut internalIn) ∧
      (∀ internalPair spacetimePair,
        ContDiff ℝ ∞ fun point =>
          configuration.gravityAuxiliary point
            internalPair spacetimePair) ∧
      (∀ internalPair spacetimePair,
        ContDiff ℝ ∞ fun point =>
          configuration.gravitySimplicityMultiplier point
            internalPair spacetimePair))
    (matterGaugeSmooth :
      (∀ direction,
        ContDiff ℝ ∞ fun point =>
          p286CoordinateEquiv
            (configuration.gaugeConnection point direction)) ∧
      (∀ pair,
        ContDiff ℝ ∞ fun point =>
          p286CoordinateEquiv
            (configuration.gaugeAuxiliary point pair)) ∧
      ContDiff ℝ ∞ configuration.scalar ∧
      ContDiff ℝ ∞ (fun point =>
        matterCoordinateEquiv (configuration.matter point)) ∧
      (∀ index : MatterCoordinateIndex,
        ContDiff ℝ ∞ fun point =>
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index 1)))) :
    configuration.Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  exact nineWayAnd_of_fourAnd_five gravitySmooth matterGaugeSmooth

/-- The fixed P506/L0 complete-joint spacetime write is one globally smooth
nine-field actual.  This packages the explicit affine/quadratic normal forms;
it does not assume or assert the all-point action zero fiber. -/
theorem fixedP506L0CompleteJointActionSpacetimeSection_smooth :
    GlobalActual.Smooth :=
  stageNineSmooth_of_gravity_and_matterGauge GlobalActual
    fixedP506L0CompleteJointActionSpacetimeSection_gravitySmooth
    fixedP506L0CompleteJointActionSpacetimeSection_matterGaugeSmooth

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
