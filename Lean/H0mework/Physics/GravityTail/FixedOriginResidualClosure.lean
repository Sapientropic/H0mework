import H0mework.Physics.GravityTail.FixedJointPath
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier

/-!
# Fixed P506/L0 gravity-tail successor origin residual closure

The source/current-only gravity-tail occurrence emits one joint coframe and
connection path, computes `B = II+(e)`, and installs the live reaction.  At
the canonical source occurrence its complete action jet is exactly the jet
of the already closed constraint/Cauchy current, so all nine residual
channels remain on the same zero fiber.

No residual coordinate, support branch, target field, completion payload,
selector, or free coefficient enters the writer.  The residual is consumed
only after the emitted actual exists.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailOriginResidualClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyOriginJointResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineIIPlusRestriction
open StageNineCoframeScalarMatterRegularity
open StageNineMatterPointwiseEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineScalarMomentumCoframeReadout
open StageNineScalarVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineGlobalIntegratedAction

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual
private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Current
private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual
private abbrev Normalized : StageNineHolonomicConfiguration :=
  normalizedAffineConfiguration
    (cartanECSynchronizedGravityTailProfileOrigin Source Current 0)
    (cartanECSynchronizedGravityTailProfileTarget Source Current 0)

private theorem base_connection_origin_eq_current :
    Base.gravityConnection 0 = Current.gravityConnection 0 := by
  unfold Base cartanECSynchronizedGravityTailBase
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_connection,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]

private theorem base_curvature_origin_eq_current :
    holonomicGravityCurvature Base 0 =
      holonomicGravityCurvature Current 0 := by
  unfold Base cartanECSynchronizedGravityTailBase
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_curvature,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact,
    ← fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_eq_contactTarget_origin]

private theorem base_contactLoad_origin_eq_current :
    diracDualFormNativeCoframeECContactLoad Source Base 0 =
      diracDualFormNativeCoframeECContactLoad Source Current 0 := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_contactLoad_contact
      Source Current 0

private theorem base_target_origin_eq_current :
    diracDualFormNativeCoframeECContactCurvatureTarget Source Base 0 =
      holonomicGravityCurvature Current 0 := by
  have currentFixed :=
    fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_eq_contactTarget_origin
  unfold diracDualFormNativeCoframeECContactCurvatureTarget
  change
    coframeDiracDualECCurvatureTarget (Base.coframe 0)
        (holonomicGravityCurvature Base 0)
        (-diracDualFormNativeCoframeECContactLoad Source Base 0) =
      holonomicGravityCurvature Current 0
  rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_zero,
    base_curvature_origin_eq_current,
    base_contactLoad_origin_eq_current]
  unfold diracDualFormNativeCoframeECContactCurvatureTarget at currentFixed
  rw [fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin]
    at currentFixed
  change
    holonomicGravityCurvature Current 0 =
      coframeDiracDualECCurvatureTarget 1
        (holonomicGravityCurvature Current 0)
        (-diracDualFormNativeCoframeECContactLoad Source Current 0)
    at currentFixed
  exact currentFixed.symm

private theorem profileInput_contactLoad_origin_eq_base :
    diracDualFormNativeCoframeECContactLoad Source
        (cartanECSynchronizedGravityTailProfileInput Source Current 0) 0 =
      diracDualFormNativeCoframeECContactLoad Source Base 0 := by
  unfold diracDualFormNativeCoframeECContactLoad
  rw [cartanECSynchronizedGravityTailProfileField_eq_base Source Current 0]
  rw [show
      (cartanECSynchronizedGravityTailProfileInput Source Current 0
        ).coframe 0 = Base.coframe 0 by
    exact fullyRecenterHolonomicConfiguration_coframe_origin Base 0]

private theorem profileTarget_origin_eq_current :
    cartanECSynchronizedGravityTailProfileTarget Source Current 0 =
      holonomicGravityCurvature Current 0 := by
  unfold cartanECSynchronizedGravityTailProfileTarget
    diracDualFormNativeCoframeECContactCurvatureTarget
  rw [cartanECSynchronizedGravityTailProfilePreparedCurvature_eq_base]
  rw [profileInput_contactLoad_origin_eq_base]
  rw [show
      (cartanECSynchronizedGravityTailProfileInput Source Current 0
        ).coframe 0 = Base.coframe 0 by
    exact fullyRecenterHolonomicConfiguration_coframe_origin Base 0]
  exact base_target_origin_eq_current

/-- The occurrence-native profile target at the radial source is the exact
curvature already carried by the source current. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailProfileTarget_origin_eq_current :
    cartanECSynchronizedGravityTailProfileTarget Source Current 0 =
      holonomicGravityCurvature Current 0 :=
  profileTarget_origin_eq_current

private theorem output_connection_origin_eq_current :
    Output.gravityConnection 0 = Current.gravityConnection 0 := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection,
    cartanECSynchronizedGravityTailPathConnectionField_zero]
  exact base_connection_origin_eq_current

private theorem output_connectionDerivative_pair_origin_eq_normalized
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    gravityConnectionDerivative Output 0 derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) =
      gravityConnectionDerivative Normalized 0 derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) := by
  have outputGenerated :=
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_loweredConnectionFirstJet_origin
      derivativeDirection formDirection internalPair
  unfold cartanECSynchronizedGravityTailJetOneForm at outputGenerated
  change
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative Output 0 derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
        Source Current 0 derivativeDirection formDirection internalPair
    at outputGenerated
  have normalizedGenerated :
      cartanECSynchronizedGravityTailLoweredConnectionFirstJet
          Source Current 0 derivativeDirection formDirection internalPair =
        minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative Normalized 0 derivativeDirection
            formDirection (pairFirst internalPair) (pairSecond internalPair) := by
    unfold cartanECSynchronizedGravityTailLoweredConnectionFirstJet Normalized
      normalizedAffineConfiguration configurationOfLorentzConnection
      gravityConnectionDerivative
    rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm]
  rw [normalizedGenerated] at outputGenerated
  fin_cases internalPair <;>
    simpa [pairFirst, pairSecond, minkowskiInternalSign] using outputGenerated

private theorem output_curvature_origin_eq_normalized :
    holonomicGravityCurvature Output 0 =
      holonomicGravityCurvature Normalized 0 := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  rw [output_connectionDerivative_pair_origin_eq_normalized,
    output_connectionDerivative_pair_origin_eq_normalized]
  have connectionValue : Output.gravityConnection 0 = Normalized.gravityConnection 0 := by
    rw [output_connection_origin_eq_current]
    unfold Normalized normalizedAffineConfiguration configurationOfLorentzConnection
    change Current.gravityConnection 0 =
      normalizedAffineLorentzConnectionField
        (cartanECSynchronizedGravityTailProfileOrigin Source Current 0)
        (cartanECSynchronizedGravityTailProfileTarget Source Current 0) 0
    rw [normalizedAffineLorentzConnectionField_zero]
    rw [cartanECSynchronizedGravityTailProfileOrigin_eq_base]
    exact base_connection_origin_eq_current.symm
  simp_rw [connectionValue]

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_curvature_origin_eq_current :
    holonomicGravityCurvature Output 0 =
      holonomicGravityCurvature Current 0 := by
  rw [output_curvature_origin_eq_normalized]
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          (cartanECSynchronizedGravityTailProfileOrigin Source Current 0)
          (cartanECSynchronizedGravityTailProfileTarget Source Current 0)) 0 =
      holonomicGravityCurvature Current 0
  rw [holonomicGravityCurvature_normalizedAffineConfiguration_zero]
  exact profileTarget_origin_eq_current

private theorem output_coframe_origin_eq_current :
    Output.coframe 0 = Current.coframe 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframe_zero,
    fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin]

private theorem output_gravityAuxiliary_origin_eq_current :
    Output.gravityAuxiliary 0 = Current.gravityAuxiliary 0 := by
  calc
    Output.gravityAuxiliary 0 =
        physicalIIPlusBivector (Output.coframe 0) := by
      unfold Output
      rw [
        fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityAuxiliary,
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe]
    _ = physicalIIPlusBivector (Current.coframe 0) := by
      rw [output_coframe_origin_eq_current]
    _ = Current.gravityAuxiliary 0 :=
      (fixedP506L0CartanECConstraintCauchyGlobalActual_simplicity 0).symm

private theorem output_multiplier_origin_eq_current :
    Output.gravitySimplicityMultiplier 0 =
      Current.gravitySimplicityMultiplier 0 := by
  have outputReaction := congrFun
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_reactionSelfGenerated
      Source Current) 0
  change Output.gravitySimplicityMultiplier 0 =
    formNativeGravityReactionField Output 0 at outputReaction
  have currentResidual :
      formNativeGravityAuxiliaryEulerResidual
          (toContinuumPointField Current 0) = 0 := by
    have projected := congrArg
      DiracDualFormNativePointwiseJointResidualCarrier.gravityAuxiliary
      fixedP506L0CartanECConstraintCauchyGlobalActual_residual_origin_zero
    change
      formNativeGravityAuxiliaryEulerResidual
          (toContinuumPointField Current 0) = 0 at projected
    exact projected
  have currentReactionAt :=
    (formNativeGravityAuxiliaryEulerResidual_eq_zero_iff_reaction
      (toContinuumPointField Current 0)).1 currentResidual
  have currentReaction :
      Current.gravitySimplicityMultiplier 0 =
        formNativeGravityReactionField Current 0 := by
    change
      (toContinuumPointField Current 0).gravitySimplicityMultiplier =
        formNativeGravityReactionOfBF (toContinuumPointField Current 0)
    exact currentReactionAt
  rw [outputReaction, currentReaction]
  unfold formNativeGravityReactionField holonomicContravariantGravityCurvature
  rw [output_gravityAuxiliary_origin_eq_current,
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_curvature_origin_eq_current]

private theorem output_gaugeConnection_eq_current :
    Output.gaugeConnection = Current.gaugeConnection := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeConnection]

private theorem output_gaugeAuxiliary_eq_current :
    Output.gaugeAuxiliary = Current.gaugeAuxiliary := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeAuxiliary]

private theorem output_scalar_eq_current : Output.scalar = Current.scalar := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_scalar]

private theorem output_matter_eq_current : Output.matter = Current.matter := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_matter]

private theorem output_conjugateMatter_eq_current :
    Output.conjugateMatter = Current.conjugateMatter := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_conjugateMatter]

private theorem output_gaugeCurvature_origin_eq_current :
    holonomicGaugeCurvature Output 0 =
      holonomicGaugeCurvature Current 0 :=
  holonomicGaugeCurvature_eq_of_connection_eq
    Output Current output_gaugeConnection_eq_current 0

private theorem output_scalarCovariantDerivative_eq_current :
    holonomicScalarCovariantDerivative Output =
      holonomicScalarCovariantDerivative Current := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [output_scalar_eq_current, output_gaugeConnection_eq_current]

private theorem output_matterCovariantDerivative_origin_eq_current :
    holonomicMatterCovariantDerivative Output 0 =
      holonomicMatterCovariantDerivative Current 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [output_matter_eq_current, output_gaugeConnection_eq_current,
    output_connection_origin_eq_current]

private theorem output_pointField_origin_eq_current :
    toContinuumPointField Output 0 =
      toContinuumPointField Current 0 := by
  apply StageNineContinuumPointField.ext
  · exact output_coframe_origin_eq_current
  · exact
      fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_curvature_origin_eq_current
  · exact output_gravityAuxiliary_origin_eq_current
  · exact output_multiplier_origin_eq_current
  · exact output_gaugeCurvature_origin_eq_current
  · exact congrFun output_gaugeAuxiliary_eq_current 0
  · exact congrFun output_scalar_eq_current 0
  · exact congrFun output_scalarCovariantDerivative_eq_current 0
  · exact congrFun output_matter_eq_current 0
  · exact output_matterCovariantDerivative_origin_eq_current
  · exact congrFun output_conjugateMatter_eq_current 0

private theorem output_coframe_coordinate_hasFDerivAt_origin
    (internal coordinate : LorentzianIndex) :
    HasFDerivAt
      (fun point => Output.coframe point internal coordinate)
      (cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current 0 internal coordinate)
      0 := by
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe]
  exact
    cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_zero_of_contDiffAt
      Source Current internal coordinate
      (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiffAt_origin
        internal coordinate)

private theorem output_coframe_differentiableAt_origin :
    DifferentiableAt ℝ Output.coframe 0 := by
  apply differentiableAt_pi.mpr
  intro internal
  apply differentiableAt_pi.mpr
  intro coordinate
  exact
    (output_coframe_coordinate_hasFDerivAt_origin internal coordinate
      ).differentiableAt

private theorem current_coframe_differentiableAt_origin :
    DifferentiableAt ℝ Current.coframe 0 := by
  change DifferentiableAt ℝ
    fixedP506L0CartanECConstraintCauchyGlobalActual.coframe 0
  rw [show
      fixedP506L0CartanECConstraintCauchyGlobalActual.coframe =
        fixedP506L0CartanECConstraintPreparedActual.coframe by
    exact
      sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe
        Source fixedP506L0CartanECConstraintPreparedActual]
  exact
    (StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      fixedP506L0CartanECConstraintPreparedActual
      fixedP506L0CartanECConstraintPreparedActual_smooth).differentiable
        (by simp) |>.differentiableAt

private theorem coframe_fderiv_coordinateDirection_eq_zero_of_identityFirstJet
    (configuration : StageNineHolonomicConfiguration)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe 0)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        identityCoframeMatterGeometry)
    (direction : LorentzianIndex) :
    (fderiv ℝ configuration.coframe 0)
        (coordinateDirection direction) = 0 := by
  ext internal coordinate
  let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate :
        (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj internal :
        LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
  have evaluatedDerivative :
      HasFDerivAt
        (fun candidate : BasePoint =>
          evaluation (configuration.coframe candidate))
        (evaluation.comp (fderiv ℝ configuration.coframe 0)) 0 :=
    evaluation.hasFDerivAt.comp 0 coframeDifferentiable.hasFDerivAt
  have componentDerivativeZero := congrArg
    (fun jet => jet.derivative direction internal coordinate) firstJet
  have evaluatedFunctionEquality :
      (fun candidate : BasePoint =>
        evaluation (configuration.coframe candidate)) =
      (fun candidate : BasePoint =>
        configuration.coframe candidate internal coordinate) := by
    funext candidate
    rfl
  have evaluatedZero :
      (fderiv ℝ
          (fun candidate : BasePoint =>
            evaluation (configuration.coframe candidate)) 0)
          (coordinateDirection direction) = 0 := by
    rw [evaluatedFunctionEquality]
    simpa [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry,
      fieldDirectionalDerivative] using componentDerivativeZero
  rw [evaluatedDerivative.fderiv] at evaluatedZero
  exact evaluatedZero

private theorem coframe_fderiv_eq_zero_of_identityFirstJet
    (configuration : StageNineHolonomicConfiguration)
    (coframeDifferentiable : DifferentiableAt ℝ configuration.coframe 0)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        identityCoframeMatterGeometry) :
    fderiv ℝ configuration.coframe 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro tangent
  have tangentExpansion :
      tangent = ∑ direction : LorentzianIndex,
        tangent direction • coordinateDirection direction := by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [coordinateDirection, Fin.sum_univ_four]
  rw [tangentExpansion, map_sum]
  simp only [map_smul]
  rw [show
      ∑ direction : LorentzianIndex,
          tangent direction •
            (fderiv ℝ configuration.coframe 0)
              (coordinateDirection direction) = 0 by
    apply Finset.sum_eq_zero
    intro direction _
    rw [coframe_fderiv_coordinateDirection_eq_zero_of_identityFirstJet
      configuration coframeDifferentiable firstJet direction]
    simp]
  rfl

private theorem output_coframe_fderiv_origin_zero :
    fderiv ℝ Output.coframe 0 = 0 :=
  coframe_fderiv_eq_zero_of_identityFirstJet Output
    output_coframe_differentiableAt_origin
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_origin_eq_identity

private theorem current_coframe_fderiv_origin_zero :
    fderiv ℝ Current.coframe 0 = 0 :=
  coframe_fderiv_eq_zero_of_identityFirstJet Current
    current_coframe_differentiableAt_origin
    fixedP506L0CartanECConstraintCauchyGlobalActual_coframeFirstJet_origin

private theorem output_gravityAuxiliary_eq_iiPlus :
    Output.gravityAuxiliary =
      fun point => physicalIIPlusBivector (Output.coframe point) := by
  funext point
  unfold Output
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityAuxiliary,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe]

private theorem current_gravityAuxiliary_eq_iiPlus :
    Current.gravityAuxiliary =
      fun point => physicalIIPlusBivector (Current.coframe point) := by
  funext point
  exact fixedP506L0CartanECConstraintCauchyGlobalActual_simplicity point

private theorem output_iiPlus_fderiv_origin_eq_current :
    fderiv ℝ (fun point => physicalIIPlusBivector (Output.coframe point)) 0 =
      fderiv ℝ (fun point =>
        physicalIIPlusBivector (Current.coframe point)) 0 := by
  have outerAtCurrent : DifferentiableAt ℝ physicalIIPlusBivector
      (Current.coframe 0) :=
    (physicalIIPlusBivector_contDiff.differentiable (by simp)
      ).differentiableAt
  have outerAtOutput : DifferentiableAt ℝ physicalIIPlusBivector
      (Output.coframe 0) := by
    rw [output_coframe_origin_eq_current]
    exact outerAtCurrent
  change
    fderiv ℝ (physicalIIPlusBivector ∘ Output.coframe) 0 =
      fderiv ℝ (physicalIIPlusBivector ∘ Current.coframe) 0
  rw [fderiv_comp 0 outerAtOutput output_coframe_differentiableAt_origin,
    fderiv_comp 0 outerAtCurrent current_coframe_differentiableAt_origin,
    output_coframe_origin_eq_current]
  exact congrArg
    (fun innerDerivative : BasePoint →L[ℝ] LorentzianCoframe =>
      (fderiv ℝ physicalIIPlusBivector (Current.coframe 0)).comp
        innerDerivative)
    (output_coframe_fderiv_origin_zero.trans
      current_coframe_fderiv_origin_zero.symm)

private theorem output_gravityAuxiliaryExterior_origin_eq_current :
    holonomicGravityAuxiliaryExteriorCovariantDerivative Output 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative Current 0 := by
  have derivativeEq :
      ∀ direction,
        gravityAuxiliaryDirectionalDerivative Output 0 direction =
          gravityAuxiliaryDirectionalDerivative Current 0 direction := by
    intro direction
    unfold gravityAuxiliaryDirectionalDerivative fieldDirectionalDerivative
    rw [output_gravityAuxiliary_eq_iiPlus,
      current_gravityAuxiliary_eq_iiPlus,
      output_iiPlus_fderiv_origin_eq_current]
  have jetEq :
      holonomicGravityAuxiliaryJet Output 0 =
        holonomicGravityAuxiliaryJet Current 0 := by
    unfold holonomicGravityAuxiliaryJet
    exact congrArg₂ PointwisePhysicalBivectorJet.mk
      output_gravityAuxiliary_origin_eq_current (funext derivativeEq)
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
  rw [output_connection_origin_eq_current, jetEq]

private theorem output_p286GaugeAuxiliaryExterior_origin_eq_current :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Current 0 := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [output_gaugeConnection_eq_current,
    output_gaugeAuxiliary_eq_current]

private theorem current_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates Current) 0 := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates Current =
        holonomicConjugateMatterCoordinates
          fixedP506L0CartanECConstraintPreparedActual := by
    funext point
    unfold holonomicConjugateMatterCoordinates
    rw [fixedP506L0CartanECConstraintCauchyGlobalActual_conjugateMatter_eq_prepared]
  rw [coordinatesEq]
  exact
    (holonomicConjugateMatterCoordinates_contDiff
      fixedP506L0CartanECConstraintPreparedActual
      fixedP506L0CartanECConstraintPreparedActual_smooth).differentiable
        (by simp) |>.differentiableAt

private theorem output_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates Output) 0 := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates Output =
        holonomicConjugateMatterCoordinates Current := by
    funext point
    unfold holonomicConjugateMatterCoordinates
    rw [output_conjugateMatter_eq_current]
  rw [coordinatesEq]
  exact current_conjugateMatterCoordinates_differentiableAt_origin

private theorem identityComparison_matterDivergence_eq
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source
        (identityCoframeComparison Output) direction 0 =
      matterDifferentialMomentumDivergence Source
        (identityCoframeComparison Current) direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  unfold fieldDirectionalDerivative matterDifferentialMomentum
    matterDifferentialVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  simp only [identityCoframeComparison_coframe,
    identityCoframeComparison_conjugateMatter]
  rw [output_conjugateMatter_eq_current]

private theorem output_matterDivergence_origin_eq_current
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source Output direction 0 =
      matterDifferentialMomentumDivergence Source Current direction 0 := by
  calc
    _ = matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Output) direction 0 :=
      matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
        Source Output 0 output_coframe_differentiableAt_origin
        output_conjugateMatterCoordinates_differentiableAt_origin
        fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_origin_eq_identity
        direction
    _ = matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Current) direction 0 :=
      identityComparison_matterDivergence_eq direction
    _ = matterDifferentialMomentumDivergence Source Current direction 0 :=
      (matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
        Source Current 0 current_coframe_differentiableAt_origin
        current_conjugateMatterCoordinates_differentiableAt_origin
        fixedP506L0CartanECConstraintCauchyGlobalActual_coframeFirstJet_origin
        direction).symm

private theorem current_scalar_eq_prepared :
    Current.scalar = fixedP506L0CartanECConstraintPreparedActual.scalar := by
  unfold Current
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_scalar
      Source fixedP506L0CartanECConstraintPreparedActual

private theorem current_gaugeConnection_eq_prepared :
    Current.gaugeConnection =
      fixedP506L0CartanECConstraintPreparedActual.gaugeConnection := by
  unfold Current
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gaugeConnection
      Source fixedP506L0CartanECConstraintPreparedActual

private theorem current_scalarCovariantDerivative_eq_prepared :
    holonomicScalarCovariantDerivative Current =
      holonomicScalarCovariantDerivative
        fixedP506L0CartanECConstraintPreparedActual := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [current_scalar_eq_prepared, current_gaugeConnection_eq_prepared]

private theorem current_scalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicScalarCovariantDerivative Current) 0 := by
  rw [current_scalarCovariantDerivative_eq_prepared]
  rw [differentiableAt_pi]
  intro direction
  exact
    ((holonomicScalarCovariantDerivative_contDiff_local
      fixedP506L0CartanECConstraintPreparedActual
      fixedP506L0CartanECConstraintPreparedActual_smooth direction
      ).differentiable (by simp)).differentiableAt

private theorem output_scalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicScalarCovariantDerivative Output) 0 := by
  rw [output_scalarCovariantDerivative_eq_current]
  exact current_scalarCovariantDerivative_differentiableAt_origin

private def scalarMomentumInner
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint →
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) :=
  fun point =>
    (configuration.coframe point,
      holonomicScalarCovariantDerivative configuration point)

private theorem output_scalarMomentumInner_differentiableAt_origin :
    DifferentiableAt ℝ (scalarMomentumInner Output) 0 := by
  unfold scalarMomentumInner
  exact output_coframe_differentiableAt_origin.prodMk
    output_scalarCovariantDerivative_differentiableAt_origin

private theorem current_scalarMomentumInner_differentiableAt_origin :
    DifferentiableAt ℝ (scalarMomentumInner Current) 0 := by
  unfold scalarMomentumInner
  exact current_coframe_differentiableAt_origin.prodMk
    current_scalarCovariantDerivative_differentiableAt_origin

private theorem output_scalarMomentumInner_origin_eq_current :
    scalarMomentumInner Output 0 = scalarMomentumInner Current 0 := by
  apply Prod.ext
  · exact output_coframe_origin_eq_current
  · exact congrFun output_scalarCovariantDerivative_eq_current 0

private theorem output_scalarMomentumInner_fderiv_origin :
    fderiv ℝ (scalarMomentumInner Output) 0 =
      (fderiv ℝ Output.coframe 0).prod
        (fderiv ℝ (holonomicScalarCovariantDerivative Output) 0) := by
  unfold scalarMomentumInner
  exact output_coframe_differentiableAt_origin.fderiv_prodMk
    output_scalarCovariantDerivative_differentiableAt_origin

private theorem current_scalarMomentumInner_fderiv_origin :
    fderiv ℝ (scalarMomentumInner Current) 0 =
      (fderiv ℝ Current.coframe 0).prod
        (fderiv ℝ (holonomicScalarCovariantDerivative Current) 0) := by
  unfold scalarMomentumInner
  exact current_coframe_differentiableAt_origin.fderiv_prodMk
    current_scalarCovariantDerivative_differentiableAt_origin

private theorem output_scalarMomentumInner_fderiv_origin_eq_current :
    fderiv ℝ (scalarMomentumInner Output) 0 =
      fderiv ℝ (scalarMomentumInner Current) 0 := by
  rw [output_scalarMomentumInner_fderiv_origin,
    current_scalarMomentumInner_fderiv_origin,
    output_coframe_fderiv_origin_zero,
    current_coframe_fderiv_origin_zero,
    output_scalarCovariantDerivative_eq_current]

private theorem scalarMomentumReadout_differentiableAt_currentInner
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (scalarMomentumCoframeCovariantReadout direction derivativeDirection)
      (scalarMomentumInner Current 0) := by
  change DifferentiableAt ℝ
    (scalarMomentumCoframeCovariantReadout direction derivativeDirection)
    (Current.coframe 0,
      holonomicScalarCovariantDerivative Current 0)
  rw [fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin]
  exact
    (scalarMomentumCoframeCovariantReadout_contDiffAt_one direction
      derivativeDirection
      (holonomicScalarCovariantDerivative Current 0)).differentiableAt
      (by simp)

private theorem output_scalarMomentumComposition_fderiv_origin_eq_current
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Output) 0 =
      fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Current) 0 := by
  let outer :=
    scalarMomentumCoframeCovariantReadout direction derivativeDirection
  have outerAtCurrent : DifferentiableAt ℝ outer
      (scalarMomentumInner Current 0) :=
    scalarMomentumReadout_differentiableAt_currentInner direction
      derivativeDirection
  have outerAtOutput : DifferentiableAt ℝ outer
      (scalarMomentumInner Output 0) := by
    rw [output_scalarMomentumInner_origin_eq_current]
    exact outerAtCurrent
  change
    fderiv ℝ (outer ∘ scalarMomentumInner Output) 0 =
      fderiv ℝ (outer ∘ scalarMomentumInner Current) 0
  rw [fderiv_comp 0 outerAtOutput
      output_scalarMomentumInner_differentiableAt_origin,
    fderiv_comp 0 outerAtCurrent
      current_scalarMomentumInner_differentiableAt_origin,
    output_scalarMomentumInner_origin_eq_current]
  exact congrArg
    (fun innerDerivative :
        BasePoint →L[ℝ]
          (LorentzianCoframe ×
            (LorentzianIndex → ScalarCoordinateCarrier)) =>
      (fderiv ℝ outer (scalarMomentumInner Current 0)).comp
        innerDerivative)
    output_scalarMomentumInner_fderiv_origin_eq_current

private theorem output_scalarMomentum_diagonalDerivative_eq_current
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum Source Output direction
          derivativeDirection) 0 derivativeDirection =
      fieldDirectionalDerivative
        (scalarDifferentialMomentum Source Current direction
          derivativeDirection) 0 derivativeDirection := by
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_eq_readout,
    scalarDifferentialMomentum_eq_readout]
  change
    (fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Output) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Current) 0)
        (coordinateDirection derivativeDirection)
  rw [output_scalarMomentumComposition_fderiv_origin_eq_current]

private theorem output_scalarDivergence_origin_eq_current
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source Output direction 0 =
      scalarDifferentialMomentumDivergence Source Current direction 0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact output_scalarMomentum_diagonalDerivative_eq_current direction
    derivativeDirection

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_actionJet_origin_eq_current :
    generatedDiracDualFormNativePointwiseActionJet Source Output 0 =
      generatedDiracDualFormNativePointwiseActionJet Source Current 0 := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · exact output_pointField_origin_eq_current
  · exact output_connection_origin_eq_current
  · exact congrFun output_gaugeConnection_eq_current 0
  · exact output_gravityAuxiliaryExterior_origin_eq_current
  · exact output_p286GaugeAuxiliaryExterior_origin_eq_current
  · funext direction
    exact output_scalarDivergence_origin_eq_current direction
  · funext direction
    exact output_matterDivergence_origin_eq_current direction

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_residual_origin_eq_current :
    diracDualFormNativePointwiseJointResidual Source Output 0 =
      diracDualFormNativePointwiseJointResidual Source Current 0 := by
  exact
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      Source Output Current 0 0
      fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_actionJet_origin_eq_current

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_residual_origin_zero :
    diracDualFormNativePointwiseJointResidual Source Output 0 = 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_residual_origin_eq_current]
  exact fixedP506L0CartanECConstraintCauchyGlobalActual_residual_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailOriginResidualClosure
