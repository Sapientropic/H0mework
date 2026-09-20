import H0mework.Physics.GravityTail.FixedAllPointResidualNormalForm
import H0mework.Physics.CoframeResponse.MatterActionAcceptance
import H0mework.Physics.SynchronizedJoint.GravityTailProfileLocalRegularity

/-!
# Source-generated gravity-tail origin settlement

For an arbitrary source/current pair, smoothness and origin nondegeneracy of
the operation-generated synchronized Base make the operation's output and
matching contact carry identical complete action jets at the radial origin.
This is a local domain law of the gravity-tail material itself.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

namespace SaturationMonoid.PhysicsCore
namespace StageNineDiracDualFormNativeCartanECSynchronizedGravityTailOriginSettlement

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeFirstJet
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeLorentzGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineRadialCurveIntegralFirstJet
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarMomentumCoframeReadout
open StageNineScalarPointwiseEquation
open StageNineScalarVariation

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

section GenericMaterial

variable (source : SmoothUnifiedSource)
variable (current : StageNineHolonomicConfiguration)

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase source current

private abbrev Output : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
    source current

private abbrev Contact : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailProfileContact source current 0

private abbrev Normalized : StageNineHolonomicConfiguration :=
  normalizedAffineConfiguration
    (cartanECSynchronizedGravityTailProfileOrigin source current 0)
    (cartanECSynchronizedGravityTailProfileTarget source current 0)

private theorem jetCLM_contDiffAt_origin
    (baseSmooth : (Base source current).Smooth)
    (nondegenerate : Matrix.det ((Base source current).coframe 0) ≠ 0) :
    ContDiffAt ℝ 0
      (cartanECSynchronizedGravityTailJetCLM source current) 0 :=
  (cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt
    source current baseSmooth 0 nondegenerate).of_le (by norm_num)

private theorem output_connectionDerivative_origin_eq_normalized
    (baseSmooth : (Base source current).Smooth)
    (nondegenerate : Matrix.det ((Base source current).coframe 0) ≠ 0)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    gravityConnectionDerivative (Output source current) 0
        derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) =
      gravityConnectionDerivative (Normalized source current) 0
        derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) := by
  have outputGenerated :=
    cartanECSynchronizedGravityTailPathConnectionField_loweredFirstJet_zero_of_contDiffAt
      source current (jetCLM_contDiffAt_origin source current baseSmooth
        nondegenerate) derivativeDirection formDirection internalPair
  change
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative (Output source current) 0
          derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cartanECSynchronizedGravityTailJetCLM source current 0
        (coordinateDirection derivativeDirection) formDirection internalPair
    at outputGenerated
  rw [cartanECSynchronizedGravityTailJetCLM_coordinate] at outputGenerated
  have normalizedGenerated :
      cartanECSynchronizedGravityTailJetOneForm source current 0
          derivativeDirection formDirection internalPair =
        minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative (Normalized source current) 0
            derivativeDirection formDirection
            (pairFirst internalPair) (pairSecond internalPair) := by
    unfold cartanECSynchronizedGravityTailJetOneForm
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
      gravityConnectionDerivative
    rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm]
    rfl
  rw [normalizedGenerated] at outputGenerated
  fin_cases internalPair <;>
    simpa [pairFirst, pairSecond, minkowskiInternalSign] using outputGenerated

private theorem output_connection_origin_eq_normalized :
    (Output source current).gravityConnection 0 =
      (Normalized source current).gravityConnection 0 := by
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection,
    cartanECSynchronizedGravityTailPathConnectionField_zero]
  unfold cartanECSynchronizedGravityTailPathAnchor
  change
    (Base source current).gravityConnection 0 =
      normalizedAffineLorentzConnectionField
        (cartanECSynchronizedGravityTailProfileOrigin source current 0)
        (cartanECSynchronizedGravityTailProfileTarget source current 0) 0
  rw [normalizedAffineLorentzConnectionField_zero,
    cartanECSynchronizedGravityTailProfileOrigin_eq_base]

private theorem output_curvature_origin_eq_contact :
    (baseSmooth : (Base source current).Smooth) →
    (Matrix.det ((Base source current).coframe 0) ≠ 0) →
    holonomicGravityCurvature (Output source current) 0 =
      holonomicGravityCurvature (Contact source current) 0 := by
  intro baseSmooth nondegenerate
  have outputNormalized :
      holonomicGravityCurvature (Output source current) 0 =
        holonomicGravityCurvature (Normalized source current) 0 := by
    funext internalPair spacetimePair
    unfold holonomicGravityCurvature
    dsimp only
    rw [output_connectionDerivative_origin_eq_normalized source current
        baseSmooth nondegenerate,
      output_connectionDerivative_origin_eq_normalized source current
        baseSmooth nondegenerate,
      output_connection_origin_eq_normalized source current]
  have contactConnection : (Contact source current).gravityConnection =
      (Normalized source current).gravityConnection := by
    unfold Contact
    rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm]
    rfl
  rw [outputNormalized]
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [contactConnection]

private theorem seam_coframe_origin_zero :
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)).coframe = 0 := by
  change
    (Output source current).coframe 0 -
      (Contact source current).coframe 0 = 0
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe,
    cartanECSynchronizedGravityTailCoframePathField_zero]
  unfold cartanECSynchronizedGravityTailCoframePathAnchor Contact
    cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  exact sub_eq_zero.mpr
    (fullyRecenterHolonomicConfiguration_coframe_origin
      (Base source current) 0).symm

private theorem seam_curvature_origin_zero :
    (baseSmooth : (Base source current).Smooth) →
    (Matrix.det ((Base source current).coframe 0) ≠ 0) →
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)).gravityCurvature = 0 := by
  intro baseSmooth nondegenerate
  change
    holonomicGravityCurvature (Output source current) 0 -
      holonomicGravityCurvature (Contact source current) 0 = 0
  exact sub_eq_zero.mpr
    (output_curvature_origin_eq_contact source current baseSmooth
      nondegenerate)

private theorem seam_connection_origin_zero :
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)).gravityConnection = 0 := by
  change
    (Output source current).gravityConnection 0 -
      (Contact source current).gravityConnection 0 = 0
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection,
    cartanECSynchronizedGravityTailPathConnectionField_zero]
  unfold cartanECSynchronizedGravityTailPathAnchor
  rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm,
    normalizedAffineLorentzConnectionField_zero,
    cartanECSynchronizedGravityTailProfileOrigin_eq_base]
  exact sub_self _

private theorem output_coframe_origin_eq_contact :
    (Output source current).coframe 0 =
      (Contact source current).coframe 0 :=
  sub_eq_zero.mp (seam_coframe_origin_zero source current)

private theorem seam_auxiliary_origin_zero :
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)).gravityAuxiliary = 0 := by
  change
    (Output source current).gravityAuxiliary 0 -
      (Contact source current).gravityAuxiliary 0 = 0
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityAuxiliary]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_auxiliary]
  apply sub_eq_zero.mpr
  exact congrArg physicalIIPlusBivector
    (output_coframe_origin_eq_contact source current)

private theorem seam_multiplier_origin_zero :
    (baseSmooth : (Base source current).Smooth) →
    (Matrix.det ((Base source current).coframe 0) ≠ 0) →
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)).gravitySimplicityMultiplier = 0 := by
  intro baseSmooth nondegenerate
  change
    (Output source current).gravitySimplicityMultiplier 0 -
      (Contact source current).gravitySimplicityMultiplier 0 = 0
  have outputReaction := congrFun
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_reactionSelfGenerated
      source current) 0
  have contactReaction := congrFun
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_reactionSelfGenerated
      source (cartanECSynchronizedGravityTailProfileInput source current 0) 0) 0
  change (Output source current).gravitySimplicityMultiplier 0 =
    formNativeGravityReactionField (Output source current) 0 at outputReaction
  change (Contact source current).gravitySimplicityMultiplier 0 =
    formNativeGravityReactionField (Contact source current) 0 at contactReaction
  rw [outputReaction, contactReaction]
  unfold formNativeGravityReactionField
  have auxiliaryEq : (Output source current).gravityAuxiliary 0 =
      (Contact source current).gravityAuxiliary 0 :=
    sub_eq_zero.mp (seam_auxiliary_origin_zero source current)
  rw [auxiliaryEq]
  unfold holonomicContravariantGravityCurvature
  rw [output_curvature_origin_eq_contact source current baseSmooth
    nondegenerate]
  abel

private theorem output_matter_eq_contact :
    (Output source current).matter = (Contact source current).matter := by
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_matter]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter]
  unfold cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero]
  exact
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter
      source current 0).symm

private theorem output_gaugeConnection_eq_contact :
    (Output source current).gaugeConnection =
      (Contact source current).gaugeConnection := by
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeConnection]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection]
  unfold cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero]
  exact
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
      source current 0).symm

private theorem output_connection_origin_eq_contact :
    (Output source current).gravityConnection 0 =
      (Contact source current).gravityConnection 0 :=
  sub_eq_zero.mp (seam_connection_origin_zero source current)

private theorem seam_matterDerivative_origin_zero :
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)).matterCovariantDerivative = 0 := by
  change
    holonomicMatterCovariantDerivative (Output source current) 0 -
      holonomicMatterCovariantDerivative (Contact source current) 0 = 0
  apply sub_eq_zero.mpr
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [output_matter_eq_contact source current,
    output_gaugeConnection_eq_contact source current,
    output_connection_origin_eq_contact source current]

private theorem coframeRadialFirstJetDefect_origin_zero
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
        source current 0 internal coordinate = 0 := by
  unfold cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
    radialCurveIntegralFirstJetDefect
  change
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        source current 0 internal coordinate -
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current 0 internal coordinate = 0
  rw [cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate_zero]
  exact sub_self _

/-- The source-generated coframe radial first-jet defect vanishes at the
radial origin. -/
theorem sourceActionGeneratedGravityTail_coframeRadialFirstJetDefect_origin_zero :
    (fun internal coordinate =>
      cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
        source current 0 internal coordinate) = 0 := by
  funext internal coordinate
  exact coframeRadialFirstJetDefect_origin_zero source current internal coordinate

private theorem coframeJetCoordinateCLM_contDiffAt_origin
    (baseSmooth : (Base source current).Smooth)
    (nondegenerate : Matrix.det ((Base source current).coframe 0) ≠ 0)
    (internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        source current contact internal coordinate) 0 :=
  (cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    source current baseSmooth 0 nondegenerate internal coordinate).of_le
      (by norm_num)

private theorem output_coframe_component_differentiableAt_origin
    (baseSmooth : (Base source current).Smooth)
    (nondegenerate : Matrix.det ((Base source current).coframe 0) ≠ 0)
    (internal coordinate : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate =>
        (Output source current).coframe candidate internal coordinate) 0 := by
  change DifferentiableAt ℝ
    (fun candidate =>
      cartanECSynchronizedGravityTailCoframePathField
        source current candidate internal coordinate) 0
  exact
    (cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_zero_of_contDiffAt
      source current internal coordinate
      (coframeJetCoordinateCLM_contDiffAt_origin source current baseSmooth
        nondegenerate internal coordinate)).differentiableAt

private theorem contact_coframe_component_differentiableAt_origin
    (internal coordinate : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate =>
        (Contact source current).coframe candidate internal coordinate) 0 := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  have smooth :=
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
      source (cartanECSynchronizedGravityTailProfileInput source current 0) 0
  exact
    (contDiff_pi.mp (contDiff_pi.mp smooth internal) coordinate).differentiable
      (by simp) |>.differentiableAt

private theorem output_coframeFirstJet_origin_eq_contact :
    (baseSmooth : (Base source current).Smooth) →
    (Matrix.det ((Base source current).coframe 0) ≠ 0) →
    holonomicCoframeFirstJetAt (Output source current).coframe 0 =
      holonomicCoframeFirstJetAt (Contact source current).coframe 0 := by
  intro baseSmooth nondegenerate
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe]
  rw [holonomicCoframeFirstJetAt_cartanECSynchronizedGravityTailCoframePathField_zero_of_contDiffAt
    source current (coframeJetCoordinateCLM_contDiffAt_origin source current
      baseSmooth nondegenerate)]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframeFirstJet_contact]
  exact
    cartanECSynchronizedGravityTailCoframeRadialFirstJet_zero_eq_profile
      source current

private theorem seam_auxiliaryExterior_origin_zero :
    (baseSmooth : (Base source current).Smooth) →
    (Matrix.det ((Base source current).coframe 0) ≠ 0) →
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source
        (Output source current) 0)
      (generatedDiracDualFormNativePointwiseActionJet source
        (Contact source current) 0)
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 := by
  intro baseSmooth nondegenerate
  change
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (Output source current) 0 -
      holonomicGravityAuxiliaryExteriorCovariantDerivative
        (Contact source current) 0 = 0
  apply sub_eq_zero.mpr
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
  rw [output_connection_origin_eq_contact source current]
  apply congrArg
    (pointwisePhysicalBivectorExteriorCovariantDerivative
      ((Contact source current).gravityConnection 0))
  apply holonomicGravityAuxiliaryJet_eq_of_iiPlus_of_coframeFirstJet_eq
  · funext candidate
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityAuxiliary
        source current candidate
  · funext candidate
    unfold Contact cartanECSynchronizedGravityTailProfileContact
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_auxiliary
        source (cartanECSynchronizedGravityTailProfileInput source current 0)
          0 candidate
  · exact output_coframe_component_differentiableAt_origin source current
      baseSmooth nondegenerate
  · exact contact_coframe_component_differentiableAt_origin source current
  · exact output_coframeFirstJet_origin_eq_contact source current baseSmooth
      nondegenerate

variable (baseSmooth : (Base source current).Smooth)
variable (nondegenerate : Matrix.det ((Base source current).coframe 0) ≠ 0)

include baseSmooth nondegenerate

local notation "B" => Base source current
local notation "O" => Output source current
local notation "C" => Contact source current

private theorem output_scalar_eq_contact : (O).scalar = (C).scalar := by
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_scalar]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar]
  unfold cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero]
  exact
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar
      source current 0).symm

private theorem output_scalarCovariantDerivative_eq_contact :
    holonomicScalarCovariantDerivative O =
      holonomicScalarCovariantDerivative C := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [output_scalar_eq_contact source current baseSmooth nondegenerate,
    output_gaugeConnection_eq_contact source current]

private theorem contact_scalarCovariantDerivative_contDiff :
    ContDiff ℝ ∞ (holonomicScalarCovariantDerivative C) := by
  rw [show holonomicScalarCovariantDerivative C =
      holonomicScalarCovariantDerivative B by
    funext point direction
    unfold Contact cartanECSynchronizedGravityTailProfileContact
    unfold holonomicScalarCovariantDerivative
    rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar,
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection]
    unfold cartanECSynchronizedGravityTailProfileInput
    rw [fullyRecenterHolonomicConfiguration_zero]]
  apply contDiff_pi'
  intro direction
  exact holonomicScalarCovariantDerivative_contDiff B baseSmooth direction

private theorem coframe_differentiableAt_of_components
    (coframe : BasePoint → LorentzianCoframe)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) 0) :
    DifferentiableAt ℝ coframe 0 := by
  apply differentiableAt_pi.mpr
  intro internal
  apply differentiableAt_pi.mpr
  intro coordinate
  exact componentDifferentiable internal coordinate

private theorem output_coframe_differentiableAt_origin :
    DifferentiableAt ℝ (O).coframe 0 :=
  coframe_differentiableAt_of_components source current baseSmooth
    nondegenerate (O).coframe
    (output_coframe_component_differentiableAt_origin source current
      baseSmooth nondegenerate)

private theorem contact_coframe_differentiableAt_origin :
    DifferentiableAt ℝ (C).coframe 0 :=
  coframe_differentiableAt_of_components source current baseSmooth
    nondegenerate (C).coframe
    (contact_coframe_component_differentiableAt_origin source current)

private theorem fieldDirectionalDerivative_pi_apply_of_differentiableAt
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → I → V)
    (direction : LorentzianIndex) (index : I)
    (fieldDifferentiableAt : DifferentiableAt ℝ field 0) :
    (fieldDirectionalDerivative field 0 direction) index =
      fieldDirectionalDerivative (fun candidate => field candidate index)
        0 direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply fieldDifferentiableAt index
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] V =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

private theorem output_coframe_fderiv_origin_eq_contact :
    fderiv ℝ (O).coframe 0 = fderiv ℝ (C).coframe 0 := by
  apply ContinuousLinearMap.ext
  intro tangent
  have tangentExpansion :
      tangent = ∑ direction : LorentzianIndex,
        tangent direction • coordinateDirection direction := by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [coordinateDirection, Fin.sum_univ_four]
  rw [tangentExpansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [map_smul]
  congr 1
  ext internal coordinate
  change
    (fieldDirectionalDerivative (O).coframe 0 direction) internal coordinate =
      (fieldDirectionalDerivative (C).coframe 0 direction) internal coordinate
  calc
    _ = (fieldDirectionalDerivative
          (fun candidate => (O).coframe candidate internal)
          0 direction) coordinate :=
      congrFun
        (fieldDirectionalDerivative_pi_apply_of_differentiableAt source current
          baseSmooth nondegenerate (O).coframe direction internal
          (output_coframe_differentiableAt_origin source current baseSmooth
            nondegenerate))
        coordinate
    _ = fieldDirectionalDerivative
          (fun candidate => (O).coframe candidate internal coordinate)
          0 direction :=
      fieldDirectionalDerivative_pi_apply_of_differentiableAt source current
        baseSmooth nondegenerate
        (fun candidate => (O).coframe candidate internal) direction coordinate
        (differentiableAt_pi.mp
          (output_coframe_differentiableAt_origin source current baseSmooth
            nondegenerate) internal)
    _ = fieldDirectionalDerivative
          (fun candidate => (C).coframe candidate internal coordinate)
          0 direction := by
      exact congrArg
        (fun jet => jet.derivative direction internal coordinate)
        (output_coframeFirstJet_origin_eq_contact source current baseSmooth
          nondegenerate)
    _ = (fieldDirectionalDerivative
          (fun candidate => (C).coframe candidate internal)
          0 direction) coordinate :=
      (fieldDirectionalDerivative_pi_apply_of_differentiableAt source current
        baseSmooth nondegenerate
        (fun candidate => (C).coframe candidate internal) direction coordinate
        (differentiableAt_pi.mp
          (contact_coframe_differentiableAt_origin source current baseSmooth
            nondegenerate) internal)).symm
    _ = (fieldDirectionalDerivative (C).coframe 0 direction)
          internal coordinate :=
      congrFun
        (fieldDirectionalDerivative_pi_apply_of_differentiableAt source current
          baseSmooth nondegenerate (C).coframe direction internal
          (contact_coframe_differentiableAt_origin source current baseSmooth
            nondegenerate)).symm
        coordinate

private def scalarMomentumInner
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint → LorentzianCoframe ×
      (LorentzianIndex → ScalarCoordinateCarrier) :=
  fun candidate =>
    (configuration.coframe candidate,
      holonomicScalarCovariantDerivative configuration candidate)

private theorem contact_scalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicScalarCovariantDerivative C) 0 :=
  ((contact_scalarCovariantDerivative_contDiff source current baseSmooth
    nondegenerate).differentiable (by simp)).differentiableAt

private theorem output_scalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicScalarCovariantDerivative O) 0 := by
  rw [output_scalarCovariantDerivative_eq_contact source current baseSmooth
    nondegenerate]
  exact contact_scalarCovariantDerivative_differentiableAt_origin source
    current baseSmooth nondegenerate

private theorem output_scalarMomentumInner_differentiableAt_origin :
    DifferentiableAt ℝ (scalarMomentumInner O) 0 :=
  (output_coframe_differentiableAt_origin source current baseSmooth
    nondegenerate).prodMk
      (output_scalarCovariantDerivative_differentiableAt_origin source current
        baseSmooth nondegenerate)

private theorem contact_scalarMomentumInner_differentiableAt_origin :
    DifferentiableAt ℝ (scalarMomentumInner C) 0 :=
  (contact_coframe_differentiableAt_origin source current baseSmooth
    nondegenerate).prodMk
      (contact_scalarCovariantDerivative_differentiableAt_origin source current
        baseSmooth nondegenerate)

private theorem output_scalarMomentumInner_origin_eq_contact :
    scalarMomentumInner O 0 = scalarMomentumInner C 0 := by
  apply Prod.ext
  · exact output_coframe_origin_eq_contact source current
  · exact congrFun
      (output_scalarCovariantDerivative_eq_contact source current baseSmooth
        nondegenerate) 0

private theorem output_scalarMomentumInner_fderiv_origin_eq_contact :
    fderiv ℝ (scalarMomentumInner O) 0 =
      fderiv ℝ (scalarMomentumInner C) 0 := by
  unfold scalarMomentumInner
  let commonDerivative :=
    (fderiv ℝ (C).coframe 0).prod
      (fderiv ℝ (holonomicScalarCovariantDerivative C) 0)
  have outputDerivative : HasFDerivAt
      (fun candidate : BasePoint =>
        ((O).coframe candidate,
          holonomicScalarCovariantDerivative O candidate))
      commonDerivative 0 := by
    apply HasFDerivAt.prodMk
    · rw [← output_coframe_fderiv_origin_eq_contact source current baseSmooth
        nondegenerate]
      exact (output_coframe_differentiableAt_origin source current baseSmooth
        nondegenerate).hasFDerivAt
    · rw [output_scalarCovariantDerivative_eq_contact source current baseSmooth
        nondegenerate]
      exact (contact_scalarCovariantDerivative_differentiableAt_origin source
        current baseSmooth nondegenerate).hasFDerivAt
  have contactDerivative : HasFDerivAt
      (fun candidate : BasePoint =>
        ((C).coframe candidate,
          holonomicScalarCovariantDerivative C candidate))
      commonDerivative 0 :=
    HasFDerivAt.prodMk
      (contact_coframe_differentiableAt_origin source current baseSmooth
        nondegenerate).hasFDerivAt
      (contact_scalarCovariantDerivative_differentiableAt_origin source current
        baseSmooth nondegenerate).hasFDerivAt
  exact outputDerivative.fderiv.trans contactDerivative.fderiv.symm

private theorem contact_coframe_nondegenerate_origin :
    Matrix.det ((C).coframe 0) ≠ 0 := by
  rw [show (C).coframe 0 = (B).coframe 0 by
    unfold Contact cartanECSynchronizedGravityTailProfileContact
    rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
    exact fullyRecenterHolonomicConfiguration_coframe_origin B 0]
  exact nondegenerate

private theorem output_scalarMomentumComposition_fderiv_origin_eq_contact
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner O) 0 =
      fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner C) 0 := by
  let outer :=
    scalarMomentumCoframeCovariantReadout direction derivativeDirection
  have outerAtContact : DifferentiableAt ℝ outer
      (scalarMomentumInner C 0) := by
    exact
      (scalarMomentumCoframeCovariantReadout_contDiffAt direction
        derivativeDirection ((C).coframe 0)
        (contact_coframe_nondegenerate_origin source current baseSmooth
          nondegenerate)
        (holonomicScalarCovariantDerivative C 0)
        ).differentiableAt (by simp)
  have outerAtOutput : DifferentiableAt ℝ outer
      (scalarMomentumInner O 0) := by
    rw [output_scalarMomentumInner_origin_eq_contact source current baseSmooth
      nondegenerate]
    exact outerAtContact
  change
    fderiv ℝ (outer ∘ scalarMomentumInner O) 0 =
      fderiv ℝ (outer ∘ scalarMomentumInner C) 0
  rw [fderiv_comp 0 outerAtOutput
      (output_scalarMomentumInner_differentiableAt_origin source current
        baseSmooth nondegenerate),
    fderiv_comp 0 outerAtContact
      (contact_scalarMomentumInner_differentiableAt_origin source current
        baseSmooth nondegenerate),
    output_scalarMomentumInner_origin_eq_contact source current baseSmooth
      nondegenerate]
  exact congrArg
    (fun innerDerivative : BasePoint →L[ℝ]
        (LorentzianCoframe ×
          (LorentzianIndex → ScalarCoordinateCarrier)) =>
      (fderiv ℝ outer (scalarMomentumInner C 0)).comp innerDerivative)
    (output_scalarMomentumInner_fderiv_origin_eq_contact source current
      baseSmooth nondegenerate)

private theorem seam_scalarDivergence_origin_zero :
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source O 0)
      (generatedDiracDualFormNativePointwiseActionJet source C 0)
      ).scalarDifferentialMomentumDivergence = 0 := by
  change
    (fun direction =>
      scalarDifferentialMomentumDivergence source O direction 0) -
        (fun direction =>
          scalarDifferentialMomentumDivergence source C direction 0) = 0
  apply sub_eq_zero.mpr
  funext direction
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_eq_readout,
    scalarDifferentialMomentum_eq_readout]
  change
    (fderiv ℝ
      (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
        scalarMomentumInner O) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner C) 0)
          (coordinateDirection derivativeDirection)
  rw [output_scalarMomentumComposition_fderiv_origin_eq_contact source current
    baseSmooth nondegenerate]

private theorem output_conjugateMatter_eq_contact :
    (O).conjugateMatter = (C).conjugateMatter := by
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_conjugateMatter]
  unfold Contact cartanECSynchronizedGravityTailProfileContact
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter]
  unfold cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero]
  exact
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
      source current 0).symm

private theorem contact_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates C) := by
  rw [show holonomicConjugateMatterCoordinates C =
      holonomicConjugateMatterCoordinates B by
    funext candidate
    unfold holonomicConjugateMatterCoordinates Contact
      cartanECSynchronizedGravityTailProfileContact
    rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter]
    unfold cartanECSynchronizedGravityTailProfileInput
    rw [fullyRecenterHolonomicConfiguration_zero]]
  exact holonomicConjugateMatterCoordinates_contDiff B baseSmooth

private theorem matterMomentumPointCoframe_output_eq_contact
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentumPointCoframe source O direction
        derivativeDirection =
      matterDifferentialMomentumPointCoframe source C direction
        derivativeDirection := by
  funext joint
  unfold matterDifferentialMomentumPointCoframe
    matterDifferentialVariationVector generatedVolumeDensity
  simp only [toContinuumPointField, withCoframe]
  rw [output_conjugateMatter_eq_contact source current baseSmooth
    nondegenerate]

private def pointCoframeSection
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint → BasePoint × LorentzianCoframe :=
  fun candidate => (candidate, configuration.coframe candidate)

private theorem output_pointCoframeSection_differentiableAt_origin :
    DifferentiableAt ℝ (pointCoframeSection O) 0 :=
  differentiableAt_id.prodMk
    (output_coframe_differentiableAt_origin source current baseSmooth
      nondegenerate)

private theorem contact_pointCoframeSection_differentiableAt_origin :
    DifferentiableAt ℝ (pointCoframeSection C) 0 :=
  differentiableAt_id.prodMk
    (contact_coframe_differentiableAt_origin source current baseSmooth
      nondegenerate)

private theorem output_pointCoframeSection_origin_eq_contact :
    pointCoframeSection O 0 = pointCoframeSection C 0 := by
  apply Prod.ext
  · rfl
  · exact output_coframe_origin_eq_contact source current

private theorem output_pointCoframeSection_fderiv_origin_eq_contact :
    fderiv ℝ (pointCoframeSection O) 0 =
      fderiv ℝ (pointCoframeSection C) 0 := by
  unfold pointCoframeSection
  let commonDerivative :=
    (fderiv ℝ (fun candidate : BasePoint => candidate) 0).prod
      (fderiv ℝ (C).coframe 0)
  have outputDerivative : HasFDerivAt
      (fun candidate : BasePoint => (candidate, (O).coframe candidate))
      commonDerivative 0 := by
    apply HasFDerivAt.prodMk differentiableAt_id.hasFDerivAt
    rw [← output_coframe_fderiv_origin_eq_contact source current baseSmooth
      nondegenerate]
    exact (output_coframe_differentiableAt_origin source current baseSmooth
      nondegenerate).hasFDerivAt
  have contactDerivative : HasFDerivAt
      (fun candidate : BasePoint => (candidate, (C).coframe candidate))
      commonDerivative 0 :=
    HasFDerivAt.prodMk differentiableAt_id.hasFDerivAt
      (contact_coframe_differentiableAt_origin source current baseSmooth
        nondegenerate).hasFDerivAt
  exact outputDerivative.fderiv.trans contactDerivative.fderiv.symm

private theorem output_matterMomentumComposition_fderiv_origin_eq_contact
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fderiv ℝ
        (matterDifferentialMomentumPointCoframe source O direction
            derivativeDirection ∘ pointCoframeSection O) 0 =
      fderiv ℝ
        (matterDifferentialMomentumPointCoframe source C direction
            derivativeDirection ∘ pointCoframeSection C) 0 := by
  let outer := matterDifferentialMomentumPointCoframe source C
    direction derivativeDirection
  have coordinatesDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates C) 0 :=
    ((contact_conjugateMatterCoordinates_contDiff source current baseSmooth
      nondegenerate).differentiable (by simp)).differentiableAt
  have outerAtContact : DifferentiableAt ℝ outer
      (pointCoframeSection C 0) := by
    change DifferentiableAt ℝ outer (0, (C).coframe 0)
    exact
      matterDifferentialMomentumPointCoframe_differentiableAt_of_conjugateMatterCoordinates
        source C 0 ((C).coframe 0)
        (contact_coframe_nondegenerate_origin source current baseSmooth
          nondegenerate)
        coordinatesDifferentiable direction derivativeDirection
  have outerAtOutput : DifferentiableAt ℝ outer
      (pointCoframeSection O 0) := by
    rw [output_pointCoframeSection_origin_eq_contact source current baseSmooth
      nondegenerate]
    exact outerAtContact
  rw [matterMomentumPointCoframe_output_eq_contact source current baseSmooth
    nondegenerate direction derivativeDirection]
  change
    fderiv ℝ (outer ∘ pointCoframeSection O) 0 =
      fderiv ℝ (outer ∘ pointCoframeSection C) 0
  rw [fderiv_comp 0 outerAtOutput
      (output_pointCoframeSection_differentiableAt_origin source current
        baseSmooth nondegenerate),
    fderiv_comp 0 outerAtContact
      (contact_pointCoframeSection_differentiableAt_origin source current
        baseSmooth nondegenerate),
    output_pointCoframeSection_origin_eq_contact source current baseSmooth
      nondegenerate]
  exact congrArg
    (fun innerDerivative :
        BasePoint →L[ℝ] (BasePoint × LorentzianCoframe) =>
      (fderiv ℝ outer (pointCoframeSection C 0)).comp innerDerivative)
    (output_pointCoframeSection_fderiv_origin_eq_contact source current
      baseSmooth nondegenerate)

private theorem seam_matterDivergence_origin_zero :
    (gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source O 0)
      (generatedDiracDualFormNativePointwiseActionJet source C 0)
      ).matterDifferentialMomentumDivergence = 0 := by
  change
    (fun direction => matterDifferentialMomentumDivergence source O
      direction 0) -
      (fun direction => matterDifferentialMomentumDivergence source C
        direction 0) = 0
  apply sub_eq_zero.mpr
  funext direction
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  unfold fieldDirectionalDerivative
  rw [matterDifferentialMomentum_eq_pointCoframe_actualSection,
    matterDifferentialMomentum_eq_pointCoframe_actualSection]
  change
    (fderiv ℝ
      (matterDifferentialMomentumPointCoframe source O direction
          derivativeDirection ∘ pointCoframeSection O) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ
        (matterDifferentialMomentumPointCoframe source C direction
            derivativeDirection ∘ pointCoframeSection C) 0)
          (coordinateDirection derivativeDirection)
  rw [output_matterMomentumComposition_fderiv_origin_eq_contact source current
    baseSmooth nondegenerate]

/-- A smooth, origin-nondegenerate synchronized Base makes the gravity-tail
output and its matching contact carry the same complete action jet at the
radial origin. -/
theorem sourceActionGeneratedGravityTail_origin_seam_zero_of_baseSmooth :
    gravityTailActionJetSeam
      (generatedDiracDualFormNativePointwiseActionJet source O 0)
      (generatedDiracDualFormNativePointwiseActionJet source C 0) = 0 := by
  apply GravityTailActionJetSeam.ext
  · exact seam_coframe_origin_zero source current
  · exact seam_curvature_origin_zero source current baseSmooth nondegenerate
  · exact seam_auxiliary_origin_zero source current
  · exact seam_multiplier_origin_zero source current baseSmooth nondegenerate
  · exact seam_matterDerivative_origin_zero source current
  · exact seam_connection_origin_zero source current
  · exact seam_auxiliaryExterior_origin_zero source current baseSmooth
      nondegenerate
  · exact seam_scalarDivergence_origin_zero source current baseSmooth
      nondegenerate
  · exact seam_matterDivergence_origin_zero source current baseSmooth
      nondegenerate

end GenericMaterial

end
end StageNineDiracDualFormNativeCartanECSynchronizedGravityTailOriginSettlement
end SaturationMonoid.PhysicsCore
