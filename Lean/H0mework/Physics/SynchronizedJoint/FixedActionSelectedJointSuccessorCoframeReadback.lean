import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorScalarReadback
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorMatterAdjointClosure
import H0mework.Physics.IdentityGerms.CoframeHessianLoadStability

/-!
# Coframe readback of the Lorentz-path action-selected joint successor

The same source/current-only whole-action occurrence has already generated
the common successor.  At every point of the canonical zero slice, its
matching recentered Einstein--Cartan contact settles the complete coframe
Euler covector.  This module transports that settlement back to the diagonal
successor by comparing the one gauge-plus-matter load actually read by the
coframe equation.

No residual coordinate, support branch, target first jet, or zero-fiber
receipt enters a constructor.  The residual is used only as the final
readback of the already generated successor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorCoframeReadback

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorScalarReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286ActionCauchySplit
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCoframeVariation
open StageNineDynamicBreakingVacuum
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineScalarLocalSpinDensity

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance coframeReadbackCoframeNormedAddCommGroup :
    NormedAddCommGroup LorentzianCoframe :=
  inferInstanceAs (NormedAddCommGroup (Fin 4 → Fin 4 → ℝ))

local instance coframeReadbackCoframeNormedSpace :
    NormedSpace ℝ LorentzianCoframe :=
  inferInstanceAs (NormedSpace ℝ (Fin 4 → Fin 4 → ℝ))

local instance coframeReadbackP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance coframeReadbackP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

local instance coframeReadbackP286CoordinateNormedAddCommGroup :
    NormedAddCommGroup P286CoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : P286CoordinateIndex => ℝ)

local instance coframeReadbackP286CoordinateNormedSpace :
    NormedSpace ℝ P286CoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : P286CoordinateIndex => ℝ)

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

private abbrev Point (space : StageNineSpatialPoint) : BasePoint :=
  canonicalCauchySlicePoint 0 space

private abbrev Recentered (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Coupled (Point space)

private abbrev PreEC (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    Source (Recentered space)

private abbrev Contact (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  completeJointLiveElectricECFullOccurrenceContact Source Coupled (Point space)

private abbrev SuccessorField (space : StageNineSpatialPoint) :
    StageNineContinuumPointField :=
  toContinuumPointField Successor (Point space)

private abbrev ContactField (space : StageNineSpatialPoint) :
    StageNineContinuumPointField :=
  toContinuumPointField (Contact space) 0

private theorem coupled_coframe_eq_one :
    Coupled.coframe = fun _ => (1 : LorentzianCoframe) := by
  calc
    Coupled.coframe = Carry.coframe :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
        Source Carry
    _ = fun _ => (1 : LorentzianCoframe) :=
      actionSelectedCarry_coframe_eq_one

private theorem successor_coframe_eq_one :
    Successor.coframe = fun _ => (1 : LorentzianCoframe) := by
  calc
    Successor.coframe = Coupled.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source Coupled
    _ = fun _ => (1 : LorentzianCoframe) := coupled_coframe_eq_one

private theorem preEC_coframe_origin_eq_one
    (space : StageNineSpatialPoint) :
    (PreEC space).coframe 0 = 1 := by
  rw [sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe,
    completeJointGlobalP286AlgebraicCurrent,
    diracDualFormNativeP286CanonicalGeneratedActual_coframe,
    completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin,
    coupled_coframe_eq_one]

private theorem contact_coframeEuler_zero
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeEulerCovector Source 0 (ContactField space) = 0 := by
  change
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            Source (PreEC space)) 0) = 0
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_fullCoframeEuler_zero
      Source (PreEC space) (preEC_coframe_origin_eq_one space)

private theorem successorField_coframe_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).coframe = (ContactField space).coframe := by
  change Successor.coframe (Point space) = (Contact space).coframe 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe_at
      Source Coupled (Point space)

private theorem successorField_multiplier_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).gravitySimplicityMultiplier =
      (ContactField space).gravitySimplicityMultiplier := by
  change
    Successor.gravitySimplicityMultiplier (Point space) =
      (Contact space).gravitySimplicityMultiplier 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_multiplier_at
      Source Coupled (Point space)

private theorem successorField_gaugeAuxiliary_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).gaugeAuxiliary =
      (ContactField space).gaugeAuxiliary := by
  change Successor.gaugeAuxiliary (Point space) =
    (Contact space).gaugeAuxiliary 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeAuxiliary_at
      Source Coupled (Point space)

private theorem successorField_gravityConnection_eq_contactField
    (space : StageNineSpatialPoint) :
    Successor.gravityConnection (Point space) =
      (Contact space).gravityConnection 0 :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_at
    Source Coupled (Point space)

private theorem successorField_gaugeConnection_eq_contactField
    (space : StageNineSpatialPoint) :
    Successor.gaugeConnection (Point space) =
      (Contact space).gaugeConnection 0 :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection_at
    Source Coupled (Point space)

private theorem successorField_scalar_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).scalar = (ContactField space).scalar := by
  change Successor.scalar (Point space) = (Contact space).scalar 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_at
      Source Coupled (Point space)

private theorem successorField_matter_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).matter = (ContactField space).matter := by
  change Successor.matter (Point space) = (Contact space).matter 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_at
      Source Coupled (Point space)

private theorem successorField_conjugateMatter_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).conjugateMatter =
      (ContactField space).conjugateMatter := by
  change Successor.conjugateMatter (Point space) =
    (Contact space).conjugateMatter 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_at
      Source Coupled (Point space)

private theorem successor_gravityConnection_eq_coupled :
    Successor.gravityConnection =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Coupled).gravityConnection :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
    Source Coupled

private theorem successor_gaugeConnection_eq_coupled :
    Successor.gaugeConnection = Coupled.gaugeConnection :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection
    Source Coupled

private theorem successor_scalar_eq_coupled :
    Successor.scalar = Coupled.scalar :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
    Source Coupled

private theorem successor_matter_eq_coupled :
    Successor.matter = Coupled.matter :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
    Source Coupled

private theorem contact_gaugeConnection_eq_localAlgebraic
    (space : StageNineSpatialPoint) :
    (Contact space).gaugeConnection =
      (completeJointGlobalP286AlgebraicCurrent Source
        (Recentered space)).gaugeConnection := by
  unfold Contact completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection,
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection]

private theorem successorField_gaugeCurvature_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).gaugeCurvature =
      (ContactField space).gaugeCurvature := by
  change holonomicGaugeCurvature Successor (Point space) =
    holonomicGaugeCurvature (Contact space) 0
  calc
    holonomicGaugeCurvature Successor (Point space) =
        holonomicGaugeCurvature Coupled (Point space) :=
      holonomicGaugeCurvature_eq_of_connection_eq Successor Coupled
        successor_gaugeConnection_eq_coupled (Point space)
    _ = holonomicGaugeCurvature
          (completeJointGlobalP286AlgebraicCurrent Source
            (Recentered space)) 0 :=
      (actionSelectedCoupled_localAlgebraic_gaugeCurvature_origin_eq
        (Point space)).symm
    _ = holonomicGaugeCurvature (Contact space) 0 :=
      (holonomicGaugeCurvature_eq_of_connection_eq
        (Contact space)
        (completeJointGlobalP286AlgebraicCurrent Source (Recentered space))
        (contact_gaugeConnection_eq_localAlgebraic space) 0).symm

private theorem successorField_coframe_nondegenerate
    (space : StageNineSpatialPoint) :
    Matrix.det (SuccessorField space).coframe ≠ 0 := by
  rw [show (SuccessorField space).coframe = 1 by
    change Successor.coframe (Point space) = 1
    rw [successor_coframe_eq_one]]
  norm_num

private theorem contactField_coframe_nondegenerate
    (space : StageNineSpatialPoint) :
    Matrix.det (ContactField space).coframe ≠ 0 := by
  rw [← successorField_coframe_eq_contactField]
  exact successorField_coframe_nondegenerate space

private theorem contact_scalar_eq_temporalRecentered
    (space : StageNineSpatialPoint) :
    (Contact space).scalar =
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source (Recentered space)).scalar := by
  rfl

private theorem contact_matter_eq_temporalRecentered
    (space : StageNineSpatialPoint) :
    (Contact space).matter =
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source (Recentered space)).matter := by
  rfl

private theorem contactTranslation_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

private theorem recenteredCoupled_scalar_differentiableAt
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ (Recentered space).scalar 0 := by
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  change DifferentiableAt ℝ (Coupled.scalar ∘ translation) 0
  have atTranslated : DifferentiableAt ℝ Coupled.scalar (translation 0) := by
    simpa [translation, canonicalSpacetimeContactTranslation, point, Point]
      using actionSelectedCoupled_scalar_differentiableAt point
  exact atTranslated.comp 0
    ((contactTranslation_contDiff point).differentiable (by simp)
      |>.differentiableAt)

private theorem recenteredCoupled_scalarAcceleration_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile Source (Recentered space)) 0 := by
  apply completeJointScalarAccelerationProfile_contDiffAt_of_local
      Source (Recentered space) 0
  · rw [fullyRecenterHolonomicConfiguration_coframe_origin,
      coupled_coframe_eq_one]
    norm_num
  · change ContDiffAt ℝ ∞
      (Coupled.coframe ∘
        canonicalSpacetimeContactTranslation (Point space)) 0
    rw [coupled_coframe_eq_one]
    fun_prop
  · change ContDiffAt ℝ ∞
      (Coupled.scalar ∘
        canonicalSpacetimeContactTranslation (Point space)) 0
    exact
      (actionSelectedCoupled_scalar_contDiff.comp
        (contactTranslation_contDiff (Point space))).contDiffAt
  · change ContDiffAt ℝ ∞
      ((fun point => matterCoordinateEquiv (Coupled.matter point)) ∘
        canonicalSpacetimeContactTranslation (Point space)) 0
    exact
      (actionSelectedCoupled_matterCoordinates_contDiff.comp
        (contactTranslation_contDiff (Point space))).contDiffAt
  · change ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates Coupled ∘
        canonicalSpacetimeContactTranslation (Point space)) 0
    exact
      (actionSelectedCoupled_conjugateMatterCoordinates_contDiff.comp
        (contactTranslation_contDiff (Point space))).contDiffAt
  · intro direction
    change ContDiffAt ℝ ∞
      ((fun point => p286CoordinateEquiv
        (Carry.gaugeConnection point direction)) ∘
          canonicalSpacetimeContactTranslation (Point space)) 0
    exact
      ((actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction).comp
        (contactTranslation_contDiff (Point space))).contDiffAt

private theorem recenteredCoupled_scalarSecondPrimitive_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (canonicalTimeSecondPrimitive
        (completeJointScalarAccelerationProfile Source (Recentered space)))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 :=
  canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt _
    ((recenteredCoupled_scalarAcceleration_contDiffAt space).of_le
      (by norm_num))

private theorem contact_scalar_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt (Contact space).scalar
      (fderiv ℝ (Recentered space).scalar 0) 0 := by
  have total :=
    (recenteredCoupled_scalar_differentiableAt space).hasFDerivAt.add
      (recenteredCoupled_scalarSecondPrimitive_hasFDerivAt space)
  rw [add_zero] at total
  rw [contact_scalar_eq_temporalRecentered space]
  change HasFDerivAt
    ((Recentered space).scalar +
      canonicalTimeSecondPrimitive
        (completeJointScalarAccelerationProfile Source (Recentered space)))
    (fderiv ℝ (Recentered space).scalar 0) 0
  exact total

private theorem contact_scalarDirectionalDerivative_eq_recentered
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (Contact space).scalar 0 direction =
      fieldDirectionalDerivative (Recentered space).scalar 0 direction := by
  unfold fieldDirectionalDerivative
  rw [(contact_scalar_hasFDerivAt space).fderiv]

private theorem localMatterCorrection_eq_translate
    (contact : BasePoint) :
    completeJointMatterTemporalCoordinateCorrection Source
        (fullyRecenterHolonomicConfiguration Coupled contact) =
      completeJointMatterTemporalCoordinateCorrection Source Coupled ∘
        canonicalSpacetimeContactTranslation contact := by
  funext point
  unfold completeJointMatterTemporalCoordinateCorrection
  simp only [Function.comp_apply]
  change
    matterCoordinateEquiv
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
            (completeJointGeneratedProfileRestartCurrent Source
              (fullyRecenterHolonomicConfiguration Coupled contact) point) 0) -
        fieldDirectionalDerivative
          ((fun target => matterCoordinateEquiv (Coupled.matter target)) ∘
            canonicalSpacetimeContactTranslation contact)
          point canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
            (completeJointGeneratedProfileRestartCurrent Source Coupled
              (canonicalSpacetimeContactTranslation contact point)) 0) -
        fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (Coupled.matter target))
          (canonicalSpacetimeContactTranslation contact point)
          canonicalLorentzianTimeDirection
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  unfold completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_recenter]

private theorem recenteredCoupled_matterCorrection_zero
    (space : StageNineSpatialPoint) :
    completeJointMatterTemporalCoordinateCorrection Source
        (Recentered space) 0 = 0 := by
  change
    completeJointMatterTemporalCoordinateCorrection Source
      (fullyRecenterHolonomicConfiguration Coupled (Point space)) 0 = 0
  rw [localMatterCorrection_eq_translate]
  simpa [canonicalSpacetimeContactTranslation] using
    actionSelectedCoupled_matterTemporalCoordinateCorrection_zeroSlice space

private theorem recenteredCoupled_matterCorrection_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection Source
        (Recentered space)) 0 := by
  apply completeJointMatterTemporalCoordinateCorrection_contDiffAt_of_local
      Source (Recentered space) 0
  · rw [fullyRecenterHolonomicConfiguration_coframe_origin,
      coupled_coframe_eq_one]
    norm_num
  · rw [fullyRecenterHolonomicConfiguration_coframe_origin,
      coupled_coframe_eq_one, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  · change ContDiffAt ℝ 1
      (Coupled.coframe ∘
        canonicalSpacetimeContactTranslation (Point space)) 0
    rw [coupled_coframe_eq_one]
    fun_prop
  · change ContDiffAt ℝ 0
      (Coupled.scalar ∘
        canonicalSpacetimeContactTranslation (Point space)) 0
    exact
      (actionSelectedCoupled_scalar_contDiff_two.comp
        ((contactTranslation_contDiff (Point space)).of_le
          (show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
            WithTop.coe_le_coe.mpr le_top))).contDiffAt.of_le
          (by norm_num)
  · exact
      actionSelectedCoupled_recenteredMatterCoordinates_contDiffAt_one_zeroSlice
        space
  · exact
      actionSelectedCoupled_recenteredConjugateMatterCoordinates_contDiffAt_zero
        space
  · intro direction
    change ContDiffAt ℝ 0
      (fun localPoint => p286CoordinateEquiv
        (Coupled.gaugeConnection
          (canonicalSpacetimeContactTranslation (Point space) localPoint)
          direction)) 0
    change ContDiffAt ℝ 0
      ((fun point => p286CoordinateEquiv
        (Carry.gaugeConnection point direction)) ∘
          canonicalSpacetimeContactTranslation (Point space)) 0
    exact
      ((actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction).comp
        (contactTranslation_contDiff (Point space))).contDiffAt.of_le
          (by norm_num)

private theorem contact_matterCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (fun localPoint => matterCoordinateEquiv
        ((Contact space).matter localPoint))
      (fderiv ℝ
        (fun localPoint => matterCoordinateEquiv
          ((Recentered space).matter localPoint)) 0) 0 := by
  have recenteredDifferentiable :
      DifferentiableAt ℝ
        (fun localPoint => matterCoordinateEquiv
          ((Recentered space).matter localPoint)) 0 := by
    exact
      (actionSelectedCoupled_recenteredMatterCoordinates_contDiffAt_one_zeroSlice
        space).differentiableAt (by norm_num)
  have generated :=
    completeJointTemporalMatterCoordinates_hasFDerivAt_zero_of_contDiffAt
      Source (Recentered space) recenteredDifferentiable
      (recenteredCoupled_matterCorrection_contDiffAt space)
  rw [← contact_matter_eq_temporalRecentered space] at generated
  rw [recenteredCoupled_matterCorrection_zero space] at generated
  simpa using generated

private theorem successor_scalarDirectionalDerivative_eq_recentered
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative Successor.scalar (Point space) direction =
      fieldDirectionalDerivative (Recentered space).scalar 0 direction := by
  rw [successor_scalar_eq_coupled]
  change
    fieldDirectionalDerivative Coupled.scalar (Point space) direction =
      fieldDirectionalDerivative
        (Coupled.scalar ∘
          canonicalSpacetimeContactTranslation (Point space)) 0 direction
  symm
  simpa [canonicalSpacetimeContactTranslation] using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      Coupled.scalar (Point space) 0 direction

private theorem successor_matterDirectionalDerivative_eq_recentered
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Successor.matter point))
        (Point space) direction =
      fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((Recentered space).matter localPoint)) 0 direction := by
  rw [successor_matter_eq_coupled]
  change
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point))
        (Point space) direction =
      fieldDirectionalDerivative
        ((fun point => matterCoordinateEquiv (Coupled.matter point)) ∘
          canonicalSpacetimeContactTranslation (Point space)) 0 direction
  symm
  simpa [canonicalSpacetimeContactTranslation] using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun point => matterCoordinateEquiv (Coupled.matter point))
      (Point space) 0 direction

private theorem contact_matterDirectionalDerivative_eq_recentered
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((Contact space).matter localPoint)) 0 direction =
      fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((Recentered space).matter localPoint)) 0 direction := by
  unfold fieldDirectionalDerivative
  rw [(contact_matterCoordinates_hasFDerivAt space).fderiv]

private theorem successorField_matterCovariantDerivative_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).matterCovariantDerivative =
      (ContactField space).matterCovariantDerivative := by
  funext direction
  change
    holonomicMatterCovariantDerivative Successor (Point space) direction =
      holonomicMatterCovariantDerivative (Contact space) 0 direction
  unfold holonomicMatterCovariantDerivative
  rw [successor_matterDirectionalDerivative_eq_recentered,
    contact_matterDirectionalDerivative_eq_recentered,
    successorField_gravityConnection_eq_contactField,
    successorField_gaugeConnection_eq_contactField,
    show Successor.matter (Point space) = (Contact space).matter 0 by
      exact successorField_matter_eq_contactField space]

private theorem successorField_scalarCovariantDerivative_eq_contactField
    (space : StageNineSpatialPoint) :
    (SuccessorField space).scalarCovariantDerivative =
      (ContactField space).scalarCovariantDerivative := by
  funext direction
  change
    holonomicScalarCovariantDerivative Successor (Point space) direction =
      holonomicScalarCovariantDerivative (Contact space) 0 direction
  unfold holonomicScalarCovariantDerivative
  rw [successor_scalarDirectionalDerivative_eq_recentered,
    contact_scalarDirectionalDerivative_eq_recentered,
    successorField_gaugeConnection_eq_contactField,
    show Successor.scalar (Point space) = (Contact space).scalar 0 by
      exact successorField_scalar_eq_contactField space]

private theorem successorField_nonGravityProjection_eq_contactField
    (space : StageNineSpatialPoint) :
    identityECNonGravityContactProjection (SuccessorField space) =
      identityECNonGravityContactProjection (ContactField space) := by
  apply StageNineContinuumPointField.ext <;>
    simp only [identityECNonGravityContactProjection]
  · exact successorField_coframe_eq_contactField space
  · exact successorField_gaugeCurvature_eq_contactField space
  · exact successorField_gaugeAuxiliary_eq_contactField space
  · exact successorField_scalar_eq_contactField space
  · exact successorField_scalarCovariantDerivative_eq_contactField space
  · exact successorField_matter_eq_contactField space
  · exact successorField_matterCovariantDerivative_eq_contactField space
  · exact successorField_conjugateMatter_eq_contactField space

private theorem successorField_gaugeDensity_eq_contactField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeDensity Source (SuccessorField space) =
      diracDualFormNativeCoframeGaugeDensity Source (ContactField space) := by
  rw [←
    diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
      Source (SuccessorField space),
    successorField_nonGravityProjection_eq_contactField space,
    diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
      Source (ContactField space)]

private theorem successorField_gaugeEuler_eq_contactField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeEulerCovector Source (SuccessorField space) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (ContactField space) := by
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [successorField_gaugeDensity_eq_contactField space,
    successorField_coframe_eq_contactField space]

private theorem coframeMatterDensity_point_independent
    (point : BasePoint) (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity Source point field =
      diracDualFormNativeCoframeMatterDensity Source 0 field := by
  funext candidate
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
    generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumMatterKineticDensity
    generatedDensitizedContinuumDiracDualYukawaDensity
    generatedVolumeDensity
    generatedScalarKineticDensity scalarFrameRelativeCovariantDerivative
    generatedScalarPotential
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
    generatedContinuumDiracDualYukawaVector
  simp

private theorem successorField_matterDensity_eq_contactField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeMatterDensity Source (Point space)
        (SuccessorField space) =
      diracDualFormNativeCoframeMatterDensity Source 0
        (ContactField space) := by
  calc
    diracDualFormNativeCoframeMatterDensity Source (Point space)
        (SuccessorField space) =
        diracDualFormNativeCoframeMatterDensity Source 0
          (SuccessorField space) :=
      coframeMatterDensity_point_independent (Point space)
        (SuccessorField space)
    _ = diracDualFormNativeCoframeMatterDensity Source 0
          (ContactField space) := by
      rw [←
        diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
          Source 0 (SuccessorField space),
        successorField_nonGravityProjection_eq_contactField space,
        diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
          Source 0 (ContactField space)]

private theorem successorField_matterEuler_eq_contactField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeMatterEulerCovector Source (Point space)
        (SuccessorField space) =
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (ContactField space) := by
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [successorField_matterDensity_eq_contactField space,
    successorField_coframe_eq_contactField space]

/-- The complete non-gravity coframe load is unchanged between the one
diagonal successor and its matching native EC contact. -/
theorem successorField_nonGravityLoad_eq_contactField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeEulerCovector Source
          (SuccessorField space) +
        diracDualFormNativeCoframeMatterEulerCovector Source (Point space)
          (SuccessorField space) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
          (ContactField space) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ContactField space) := by
  rw [successorField_gaugeEuler_eq_contactField,
    successorField_matterEuler_eq_contactField]

/-- The final coframe residual is exactly the changed read of the complete
gauge-plus-matter load between the one diagonal successor and its matching
native EC contact. -/
theorem successor_coframeResidual_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Successor
      (Point space)).coframe =
      (diracDualFormNativeCoframeGaugeEulerCovector Source
          (SuccessorField space) +
        diracDualFormNativeCoframeMatterEulerCovector Source (Point space)
          (SuccessorField space)) -
      (diracDualFormNativeCoframeGaugeEulerCovector Source
          (ContactField space) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ContactField space)) := by
  have contactZero := contact_coframeEuler_zero space
  have reactionEq :
      formNativeCoframeConstraintReaction (SuccessorField space) =
        formNativeCoframeConstraintReaction (ContactField space) := by
    funext variation
    unfold formNativeCoframeConstraintReaction
    rw [successorField_multiplier_eq_contactField,
      successorField_coframe_eq_contactField]
  change
    diracDualFormNativeCoframeEulerCovector Source (Point space)
        (SuccessorField space) = _
  apply ContinuousLinearMap.ext
  intro variation
  have contactZeroAt := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ => covector variation)
    contactZero
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      Source 0 (ContactField space)
      (contactField_coframe_nondegenerate space) variation]
    at contactZeroAt
  simp only [zero_apply] at contactZeroAt
  have contactLoadEqReaction :
      (diracDualFormNativeCoframeGaugeEulerCovector Source
            (ContactField space) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (ContactField space)) variation =
        formNativeCoframeConstraintReaction (ContactField space)
          variation :=
    sub_eq_zero.mp contactZeroAt
  have reactionEqAt := congrFun reactionEq variation
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      Source (Point space) (SuccessorField space)
      (successorField_coframe_nondegenerate space) variation]
  simp only [sub_apply, add_apply]
  rw [reactionEqAt, ← contactLoadEqReaction]
  simp only [add_apply]

/-- The already generated source/current-only successor settles the complete
coframe Euler readout on the canonical zero slice. -/
theorem successor_coframeResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Successor
      (Point space)).coframe = 0 := by
  rw [successor_coframeResidual_zeroSlice_normalForm,
    successorField_nonGravityLoad_eq_contactField]
  exact sub_self _

/-- Direct whole-carrier consumer: after the coframe settlement, the complete
zero-slice residual of this one successor is equivalent to its one remaining
gravity-curvature relation. -/
theorem successor_zeroSlice_residual_eq_zero_iff_gravityCurvatureRelation
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual Source Successor
        (Point space) = 0 ↔
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
            Coupled) (Point space) =
        sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget Source
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
            Source (Recentered space)) := by
  rw [
    successor_zeroSlice_residual_eq_zero_iff_remainingGravityCoframeRelations,
    successor_coframeResidual_zeroSlice,
    eq_self,
    and_true]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorCoframeReadback
