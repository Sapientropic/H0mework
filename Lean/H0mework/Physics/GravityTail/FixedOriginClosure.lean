import H0mework.Physics.GravityTail.FixedZeroSliceSupport

/-!
# Origin closure of the action-selected gravity tail

The fixed gravity-tail occurrence has already emitted one global actual.  At
the distinguished source origin, its occurrence-owned connection value and
first jet coincide with the matching native Cartan--EC contact.  This module
uses that positive seam to transport the remaining four action readouts; no
residual coordinate or zero-fiber witness enters the writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailOriginClosure

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLorentzClosure
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPathRadialFirstJet
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailActionJetNaturality
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailZeroSliceSupport
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorStructuralReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineScalarPointwiseEquation
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalLorentzThreeFormDualInverse

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev LegacyInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev LegacyBase : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Coupled

private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual

private abbrev Contact : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailProfileContact Source Coupled 0

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

private theorem gravityConnection_origin_eq_contact :
    Final.gravityConnection 0 = Contact.gravityConnection 0 := by
  rw [show Final.gravityConnection =
      cartanECSynchronizedGravityTailPathConnectionField Source Coupled by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gravityConnection
        Source Coupled]
  rw [cartanECSynchronizedGravityTailPathConnectionField_zero]
  unfold cartanECSynchronizedGravityTailPathAnchor Contact
    cartanECSynchronizedGravityTailProfileContact
    cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_connection,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]

private theorem gravityConnectionDerivative_origin_eq_contact
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    gravityConnectionDerivative Final 0 derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) =
      gravityConnectionDerivative Contact 0 derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) := by
  have generated :=
    fixedP506L0ActionSelectedGravityTail_gravityConnectionDerivative_eq_radialFirstJet
      0 derivativeDirection formDirection internalPair
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailRadialFirstJet_zero,
    cartanECSynchronizedGravityTailJetCLM_coordinate] at generated
  unfold cartanECSynchronizedGravityTailJetOneForm
    cartanECSynchronizedGravityTailLoweredConnectionFirstJet at generated
  fin_cases internalPair <;>
    simpa [minkowskiInternalSign, pairFirst, pairSecond] using generated

private theorem gravityCurvature_origin_eq_contact :
    holonomicGravityCurvature Final 0 =
      holonomicGravityCurvature Contact 0 := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  rw [gravityConnectionDerivative_origin_eq_contact,
    gravityConnectionDerivative_origin_eq_contact]
  simp_rw [gravityConnection_origin_eq_contact]

private theorem gravityAuxiliary_origin_eq_contact :
    Final.gravityAuxiliary 0 = Contact.gravityAuxiliary 0 := by
  calc
    Final.gravityAuxiliary 0 = Base.gravityAuxiliary 0 := rfl
    _ = Contact.gravityAuxiliary 0 := by
      change Base.gravityAuxiliary 0 =
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
          Source (fullyRecenterHolonomicConfiguration Base 0) 0
          ).gravityAuxiliary 0
      rw [fullyRecenterHolonomicConfiguration_zero,
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_auxiliary,
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_simplicity
          Source Coupled 0 0

private theorem gravityReaction_origin_eq_contact :
    formNativeGravityReactionField Final 0 =
      formNativeGravityReactionField Contact 0 := by
  unfold formNativeGravityReactionField holonomicContravariantGravityCurvature
  rw [gravityAuxiliary_origin_eq_contact, gravityCurvature_origin_eq_contact]

theorem fixedP506L0ActionSelectedGravityTail_multiplier_origin_eq_contact :
    Final.gravitySimplicityMultiplier 0 =
      Contact.gravitySimplicityMultiplier 0 := by
  calc
    Final.gravitySimplicityMultiplier 0 =
        formNativeGravityReactionField Final 0 := by
      exact congrFun
        (installFormNativeGravityReaction_reactionSelfGenerated
          (cartanECSynchronizedGravityTailConnectedActual Source Coupled)) 0
    _ = formNativeGravityReactionField Contact 0 :=
      gravityReaction_origin_eq_contact
    _ = Contact.gravitySimplicityMultiplier 0 := by
      exact (congrFun
        (installFormNativeGravityReaction_reactionSelfGenerated
          (diracDualFormNativeCartanECSynchronizedCoframePreparedActual Source
            (cartanECSynchronizedGravityTailProfileInput Source Coupled 0) 0)) 0).symm

private theorem base_gaugeConnection_eq_coupled :
    Base.gaugeConnection = Coupled.gaugeConnection :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
    Source Coupled 0

private theorem base_gaugeAuxiliary_eq_coupled :
    Base.gaugeAuxiliary = Coupled.gaugeAuxiliary :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
    Source Coupled 0

private theorem base_scalar_eq_coupled : Base.scalar = Coupled.scalar :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar
    Source Coupled 0

private theorem base_matter_eq_coupled : Base.matter = Coupled.matter :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter
    Source Coupled 0

private theorem base_conjugateMatter_eq_coupled :
    Base.conjugateMatter = Coupled.conjugateMatter :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
    Source Coupled 0

private theorem final_gaugeConnection_eq_base :
    Final.gaugeConnection = Base.gaugeConnection := by
  calc
    Final.gaugeConnection = Coupled.gaugeConnection :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gaugeConnection
        Source Coupled
    _ = Base.gaugeConnection := base_gaugeConnection_eq_coupled.symm

private theorem final_gaugeAuxiliary_eq_base :
    Final.gaugeAuxiliary = Base.gaugeAuxiliary := by
  calc
    Final.gaugeAuxiliary = Coupled.gaugeAuxiliary :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gaugeAuxiliary
        Source Coupled
    _ = Base.gaugeAuxiliary := base_gaugeAuxiliary_eq_coupled.symm

private theorem final_scalar_eq_base : Final.scalar = Base.scalar := by
  calc
    Final.scalar = Coupled.scalar :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_scalar
        Source Coupled
    _ = Base.scalar := base_scalar_eq_coupled.symm

private theorem final_matter_eq_base : Final.matter = Base.matter := by
  calc
    Final.matter = Coupled.matter :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_matter
        Source Coupled
    _ = Base.matter := base_matter_eq_coupled.symm

private theorem final_conjugateMatter_eq_base :
    Final.conjugateMatter = Base.conjugateMatter := by
  calc
    Final.conjugateMatter = Coupled.conjugateMatter :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_conjugateMatter
        Source Coupled
    _ = Base.conjugateMatter := base_conjugateMatter_eq_coupled.symm

private theorem final_coframe_eq_base : Final.coframe = Base.coframe := by
  calc
    Final.coframe = fun _ => (1 : LorentzianCoframe) :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one
    _ = Base.coframe :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one.symm

private theorem contact_gaugeConnection_eq_base :
    Contact.gaugeConnection = Base.gaugeConnection := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
    cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection]

private theorem contact_gaugeAuxiliary_eq_base :
    Contact.gaugeAuxiliary = Base.gaugeAuxiliary := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
    cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary]

private theorem contact_scalar_eq_base : Contact.scalar = Base.scalar := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
    cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar]

private theorem contact_matter_eq_base : Contact.matter = Base.matter := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
    cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter]

private theorem contact_conjugateMatter_eq_base :
    Contact.conjugateMatter = Base.conjugateMatter := by
  unfold Contact cartanECSynchronizedGravityTailProfileContact
    cartanECSynchronizedGravityTailProfileInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter]

private theorem coframe_origin_eq_contact :
    Final.coframe 0 = Contact.coframe 0 := by
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  change 1 =
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
      Source (fullyRecenterHolonomicConfiguration Base 0) 0).coframe 0
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  exact congrFun
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one 0 |>.symm

private theorem gaugeCurvature_origin_eq_contact :
    holonomicGaugeCurvature Final 0 = holonomicGaugeCurvature Contact 0 := by
  apply holonomicGaugeCurvature_eq_of_connection_eq
  exact final_gaugeConnection_eq_base.trans contact_gaugeConnection_eq_base.symm

private theorem scalarCovariantDerivative_origin_eq_contact :
    holonomicScalarCovariantDerivative Final 0 =
      holonomicScalarCovariantDerivative Contact 0 := by
  unfold holonomicScalarCovariantDerivative
  rw [final_scalar_eq_base, contact_scalar_eq_base,
    final_gaugeConnection_eq_base, contact_gaugeConnection_eq_base]

private theorem matterCovariantDerivative_origin_eq_contact :
    holonomicMatterCovariantDerivative Final 0 =
      holonomicMatterCovariantDerivative Contact 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [final_matter_eq_base, contact_matter_eq_base,
    final_gaugeConnection_eq_base, contact_gaugeConnection_eq_base,
    gravityConnection_origin_eq_contact]

private theorem pointField_origin_eq_contact :
    toContinuumPointField Final 0 = toContinuumPointField Contact 0 := by
  apply StageNineContinuumPointField.ext
  · exact coframe_origin_eq_contact
  · exact gravityCurvature_origin_eq_contact
  · exact gravityAuxiliary_origin_eq_contact
  · exact fixedP506L0ActionSelectedGravityTail_multiplier_origin_eq_contact
  · exact gaugeCurvature_origin_eq_contact
  · exact congrFun
      (final_gaugeAuxiliary_eq_base.trans
        contact_gaugeAuxiliary_eq_base.symm) 0
  · exact congrFun (final_scalar_eq_base.trans contact_scalar_eq_base.symm) 0
  · exact scalarCovariantDerivative_origin_eq_contact
  · exact congrFun (final_matter_eq_base.trans contact_matter_eq_base.symm) 0
  · exact matterCovariantDerivative_origin_eq_contact
  · exact congrFun
      (final_conjugateMatter_eq_base.trans
        contact_conjugateMatter_eq_base.symm) 0

theorem fixedP506L0ActionSelectedGravityTail_coframeResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Final 0).coframe = 0 := by
  change
    diracDualFormNativeCoframeEulerCovector Source 0
      (toContinuumPointField Final 0) = 0
  rw [pointField_origin_eq_contact]
  exact
    (fixedP506L0ActionSelectedCartanECSynchronizedGravityTailProfile_jointClosure
      0).2.1

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem final_coframe_eq_successor :
    Final.coframe = Successor.coframe := by
  calc
    Final.coframe = fun _ => (1 : LorentzianCoframe) :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one
    _ = Successor.coframe := successor_coframe_eq_one.symm

private theorem final_gaugeConnection_eq_successor :
    Final.gaugeConnection = Successor.gaugeConnection := by
  calc
    Final.gaugeConnection = Coupled.gaugeConnection :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gaugeConnection
        Source Coupled
    _ = Successor.gaugeConnection :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection
        Source Coupled).symm

private theorem final_scalar_eq_successor :
    Final.scalar = Successor.scalar := by
  calc
    Final.scalar = Coupled.scalar :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_scalar
        Source Coupled
    _ = Successor.scalar :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
        Source Coupled).symm

private theorem final_matter_eq_successor :
    Final.matter = Successor.matter := by
  calc
    Final.matter = Coupled.matter :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_matter
        Source Coupled
    _ = Successor.matter :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
        Source Coupled).symm

private theorem final_conjugateMatter_eq_successor :
    Final.conjugateMatter = Successor.conjugateMatter := by
  calc
    Final.conjugateMatter = Coupled.conjugateMatter :=
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_conjugateMatter
        Source Coupled
    _ = Successor.conjugateMatter :=
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
        Source Coupled).symm

private theorem current_matter_eq_legacyBase :
    Current.matter = LegacyBase.matter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
      Source LegacyInput).matter = LegacyBase.matter
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_matter,
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_matter]
  rfl

private theorem current_conjugateMatter_eq_legacyBase :
    Current.conjugateMatter = LegacyBase.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
      Source LegacyInput).conjugateMatter = LegacyBase.conjugateMatter
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_conjugateMatter,
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_conjugateMatter]
  rfl

private theorem coupled_coframe_eq_one :
    Coupled.coframe = fun _ => (1 : LorentzianCoframe) := by
  calc
    Coupled.coframe = Carry.coframe :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
        Source Carry
    _ = fun _ => (1 : LorentzianCoframe) :=
      actionSelectedCarry_coframe_eq_one

private theorem coupled_matter_origin_eq_legacyBase :
    Coupled.matter 0 = LegacyBase.matter 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero] at zeroSlice
  calc
    Coupled.matter 0 = Carry.matter 0 := zeroSlice
    _ = Current.matter 0 := by rfl
    _ = LegacyBase.matter 0 := congrFun current_matter_eq_legacyBase 0

private theorem coupled_conjugateMatter_origin_eq_legacyBase :
    Coupled.conjugateMatter 0 = LegacyBase.conjugateMatter 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero] at zeroSlice
  calc
    Coupled.conjugateMatter 0 = Carry.conjugateMatter 0 := zeroSlice
    _ = Current.conjugateMatter 0 := by rfl
    _ = LegacyBase.conjugateMatter 0 :=
      congrFun current_conjugateMatter_eq_legacyBase 0

private theorem current_gravityConnection_origin_eq_legacyBase :
    Current.gravityConnection 0 = LegacyBase.gravityConnection 0 := by
  calc
    Current.gravityConnection 0 =
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.gravityConnection
          0 :=
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_connection_zero
    _ = LegacyBase.gravityConnection 0 := by
      rw [
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite,
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_connection,
        sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]

private theorem coupled_gravityConnection_origin_eq_legacyBase :
    Coupled.gravityConnection 0 = LegacyBase.gravityConnection 0 := by
  change Current.gravityConnection 0 = LegacyBase.gravityConnection 0
  exact current_gravityConnection_origin_eq_legacyBase

private theorem coupled_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt Coupled.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [coupled_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

private theorem reference_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt positiveSourceTargetMatterActual.coframe 0 =
      identityCoframeMatterGeometry := by
  unfold positiveSourceTargetMatterActual
  rw [sourceActionGeneratedJointLocalActualLift_coframeFirstJetAt]
  rfl

private theorem coupled_coframe_origin_eq_reference :
    Coupled.coframe 0 = positiveSourceTargetMatterActual.coframe 0 := by
  calc
    Coupled.coframe 0 = 1 := congrFun coupled_coframe_eq_one 0
    _ = positiveSourceTargetMatterActual.coframe 0 := by rfl

private theorem coupled_matter_origin_eq_reference :
    Coupled.matter 0 = positiveSourceTargetMatterActual.matter 0 := by
  calc
    Coupled.matter 0 = LegacyBase.matter 0 :=
      coupled_matter_origin_eq_legacyBase
    _ = diracSpinTwoMatterProbe :=
      fixedP506L0CompleteJointActionSpacetimeSection_matter_origin
    _ = positiveSourceTargetMatterCauchyState.matter 0 :=
      positiveSourceTargetMatterCauchyState_matter.symm
    _ = positiveSourceTargetMatterActual.matter 0 :=
      (sourceActionGeneratedJointLocalActualLift_initialMatter
        Source positiveSourceTargetMatterCauchyState 0).symm

private theorem coupled_conjugateMatter_origin_eq_reference :
    Coupled.conjugateMatter 0 =
      positiveSourceTargetMatterActual.conjugateMatter 0 := by
  calc
    Coupled.conjugateMatter 0 = LegacyBase.conjugateMatter 0 :=
      coupled_conjugateMatter_origin_eq_legacyBase
    _ = diracSpinZeroMatterCoordinate :=
      fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_origin
    _ = positiveSourceTargetMatterCauchyState.conjugateMatter 0 :=
      positiveSourceTargetMatterCauchyState_conjugate.symm
    _ = positiveSourceTargetMatterActual.conjugateMatter 0 :=
      (sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
        Source positiveSourceTargetMatterCauchyState 0).symm

private theorem actionCartanConnectionAt_eq_of_jet_and_fields_at
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (jetEqual :
      holonomicCoframeFirstJetAt first.coframe point =
        holonomicCoframeFirstJetAt second.coframe point)
    (coframeEqual : first.coframe point = second.coframe point)
    (matterEqual : first.matter point = second.matter point)
    (conjugateEqual :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionCartanConnectionAt Source first point =
      diracDualFormNativeActionCartanConnectionAt Source second point := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      Source first second point coframeEqual matterEqual conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [jetEqual, coframeEqual, spinEqual]

private theorem coupled_actionCartanConnection_origin_eq_fixed :
    diracDualFormNativeActionCartanConnectionAt Source Coupled 0 =
      fixedActionCartanConnection := by
  change
    diracDualFormNativeActionCartanConnectionAt Source Coupled 0 =
      diracDualFormNativeActionCartanConnectionAt
        Source positiveSourceTargetMatterActual 0
  apply actionCartanConnectionAt_eq_of_jet_and_fields_at
  · exact coupled_coframeFirstJet_origin.trans
      reference_coframeFirstJet_origin.symm
  · exact coupled_coframe_origin_eq_reference
  · exact coupled_matter_origin_eq_reference
  · exact coupled_conjugateMatter_origin_eq_reference

private theorem coupled_gravityConnection_origin_selfGenerated :
    Coupled.gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt Source Coupled 0 := by
  calc
    Coupled.gravityConnection 0 = LegacyBase.gravityConnection 0 :=
      coupled_gravityConnection_origin_eq_legacyBase
    _ = fixedActionCartanConnection :=
      fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_origin
    _ = diracDualFormNativeActionCartanConnectionAt Source Coupled 0 :=
      coupled_actionCartanConnection_origin_eq_fixed.symm

private theorem base_gravityConnection_origin_eq_actionCartan :
    Base.gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt Source Coupled 0 := by
  calc
    Base.gravityConnection 0 = Coupled.gravityConnection 0 := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
          Source Coupled 0).gravityConnection 0 = Coupled.gravityConnection 0
      rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_connection,
        sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]
    _ = diracDualFormNativeActionCartanConnectionAt Source Coupled 0 :=
      coupled_gravityConnection_origin_selfGenerated

private theorem final_gravityConnection_origin_eq_base :
    Final.gravityConnection 0 = Base.gravityConnection 0 := by
  rw [show Final.gravityConnection =
      cartanECSynchronizedGravityTailPathConnectionField Source Coupled by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gravityConnection
        Source Coupled]
  rw [cartanECSynchronizedGravityTailPathConnectionField_zero]
  rfl

private theorem successor_gravityConnection_origin_eq_base :
    Successor.gravityConnection 0 = Base.gravityConnection 0 := by
  calc
    Successor.gravityConnection 0 =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source Coupled).gravityConnection 0 :=
      congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
          Source Coupled) 0
    _ = diracDualFormNativeActionCartanConnectionAt Source Coupled 0 := by
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
    _ = Base.gravityConnection 0 :=
      base_gravityConnection_origin_eq_actionCartan.symm

private theorem final_gravityConnection_origin_eq_successor :
    Final.gravityConnection 0 = Successor.gravityConnection 0 :=
  final_gravityConnection_origin_eq_base.trans
    successor_gravityConnection_origin_eq_base.symm

private theorem matterCovariantDerivative_origin_eq_successor :
    holonomicMatterCovariantDerivative Final 0 =
      holonomicMatterCovariantDerivative Successor 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [final_matter_eq_successor, final_gravityConnection_origin_eq_successor,
    final_gaugeConnection_eq_successor]

private theorem generatedMatterVector_origin_eq_successor :
    generatedContinuumDiracDualMatterVector Source 0 0
        (toContinuumPointField Final 0) =
      generatedContinuumDiracDualMatterVector Source 0 0
        (toContinuumPointField Successor 0) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [final_coframe_eq_successor, matterCovariantDerivative_origin_eq_successor,
    final_scalar_eq_successor, final_matter_eq_successor]

private theorem conjugateMatterResidual_origin_eq_successor :
    (diracDualFormNativePointwiseJointResidual Source Final 0
      ).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual Source Successor 0
        ).conjugateMatter := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source Final direction 0 =
      diracDualConjugateMatterDirectionalCoefficient Source Successor direction 0
  unfold diracDualConjugateMatterDirectionalCoefficient generatedVolumeDensity
  change
    |Matrix.det (Final.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector Source 0 0
            (toContinuumPointField Final 0))).re =
      |Matrix.det (Successor.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector Source 0 0
            (toContinuumPointField Successor 0))).re
  rw [congrFun final_coframe_eq_successor 0,
    generatedMatterVector_origin_eq_successor]

private theorem matterDifferentialMomentum_eq_successor
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum Source Final direction derivativeDirection =
      matterDifferentialMomentum Source Successor direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum generatedVolumeDensity
    matterDifferentialVariationVector inverseCoframeDiracGamma
  simp only [toContinuumPointField]
  rw [final_coframe_eq_successor, final_conjugateMatter_eq_successor]

private theorem matterDifferentialMomentumDivergence_origin_eq_successor
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source Final direction 0 =
      matterDifferentialMomentumDivergence Source Successor direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [matterDifferentialMomentum_eq_successor]

private theorem matterAlgebraic_origin_eq_successor
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient Source Final direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient Source Successor direction
        0 := by
  have variationEq :
      holonomicMatterVariationAlgebraicDirection Final direction 0 =
        holonomicMatterVariationAlgebraicDirection Successor direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [final_gravityConnection_origin_eq_successor,
      final_gaugeConnection_eq_successor]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_successor, final_scalar_eq_successor,
    final_conjugateMatter_eq_successor, variationEq]

private theorem matterResidual_origin_eq_successor :
    (diracDualFormNativePointwiseJointResidual Source Final 0).matter =
      (diracDualFormNativePointwiseJointResidual Source Successor 0).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source Final direction
        0 =
      diracDualMatterEulerLagrangeDirectionalCoefficient Source Successor
        direction 0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [matterAlgebraic_origin_eq_successor,
    matterDifferentialMomentumDivergence_origin_eq_successor]

theorem fixedP506L0ActionSelectedGravityTail_matterResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Final 0).matter = 0 := by
  rw [matterResidual_origin_eq_successor]
  have settled := successor_matterResidual_zeroSlice (0 : StageNineSpatialPoint)
  change
    (diracDualFormNativePointwiseJointResidual Source Successor
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))).matter = 0
    at settled
  rw [canonicalCauchySlicePoint_zero_zero] at settled
  exact settled

theorem fixedP506L0ActionSelectedGravityTail_conjugateMatterResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Final 0
      ).conjugateMatter = 0 := by
  rw [conjugateMatterResidual_origin_eq_successor]
  have settled :=
    successor_conjugateMatterResidual_zeroSlice (0 : StageNineSpatialPoint)
  change
    (diracDualFormNativePointwiseJointResidual Source Successor
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
      ).conjugateMatter = 0 at settled
  rw [canonicalCauchySlicePoint_zero_zero] at settled
  exact settled

private theorem coupled_gravityConnection_origin_lorentzSkew :
    LorentzSkew (Coupled.gravityConnection 0) := by
  rw [coupled_gravityConnection_origin_eq_legacyBase,
    fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_origin,
    fixedActionCartanConnection_eq_positiveNormalForm]
  exact lorentzSkewConnectionOfBivectorOneForm_lorentzSkew _

private theorem coupled_coframe_origin_nondegenerate :
    Matrix.det (Coupled.coframe 0) ≠ 0 := by
  rw [coupled_coframe_eq_one]
  norm_num

private theorem gravityAuxiliaryExteriorCovariantDerivative_origin_eq_base :
    holonomicGravityAuxiliaryExteriorCovariantDerivative Final 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative Base 0 := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [final_gravityConnection_origin_eq_base]
  rfl

private theorem matterSpinThreeForm_origin_eq_base :
    formNativeMatterSpinThreeForm Source 0 0
        (toContinuumPointField Final 0) =
      formNativeMatterSpinThreeForm Source 0 0
        (toContinuumPointField Base 0) := by
  unfold formNativeMatterSpinThreeForm
  apply congrArg lorentzOneFormContinuousDualThreeForm
  apply ContinuousLinearMap.ext
  intro direction
  simp only [formNativeLorentzMatterFirstContinuousLinearMap_apply]
  unfold formNativeLorentzMatterFirstCoefficient generatedVolumeDensity
    matterCovariantDerivativeFirstVariationDensity
    pointwiseMatterLorentzConnectionVariation
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
  simp only [toContinuumPointField]
  rw [final_coframe_eq_base, final_matter_eq_base,
    final_conjugateMatter_eq_base]

theorem fixedP506L0ActionSelectedGravityTail_lorentzResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Final 0
      ).lorentzConnection = 0 := by
  change holonomicFormNativeLorentzEulerThreeForm Source 0 Final 0 = 0
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [gravityAuxiliaryExteriorCovariantDerivative_origin_eq_base,
    matterSpinThreeForm_origin_eq_base]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_lorentzEulerThreeForm_zero_contact
      Source Coupled 0 coupled_gravityConnection_origin_lorentzSkew
      coupled_coframe_origin_nondegenerate

/-- At the distinguished P506/L0 source origin, the one action-selected
gravity-tail actual lies in the complete nine-channel zero fiber. -/
theorem fixedP506L0ActionSelectedGravityTail_residual_origin_zero :
    diracDualFormNativePointwiseJointResidual Source Final 0 = 0 := by
  have support :=
    fixedP506L0ActionSelectedGravityTail_zeroSlice_residual_eq_zero_iff_connectionSensitiveReads_zero
      (0 : StageNineSpatialPoint)
  change
    diracDualFormNativePointwiseJointResidual Source Final
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) = 0 ↔
      (diracDualFormNativePointwiseJointResidual Source Final
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
          ).lorentzConnection = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Final
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
          ).matter = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Final
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
          ).conjugateMatter = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Final
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
          ).coframe = 0 at support
  rw [canonicalCauchySlicePoint_zero_zero] at support
  exact support.2
    ⟨fixedP506L0ActionSelectedGravityTail_lorentzResidual_origin_zero,
      fixedP506L0ActionSelectedGravityTail_matterResidual_origin_zero,
      fixedP506L0ActionSelectedGravityTail_conjugateMatterResidual_origin_zero,
      fixedP506L0ActionSelectedGravityTail_coframeResidual_origin_zero⟩

theorem fixedP506L0ActionSelectedGravityTail_zeroFiber_origin :
    OnDiracDualFormNativePointwiseJointZeroFiber Source Final 0 :=
  fixedP506L0ActionSelectedGravityTail_residual_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailOriginClosure
