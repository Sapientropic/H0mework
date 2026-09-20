import H0mework.Physics.CartanAction.CartanReactionCurrentRestartGlobalRegularity
import H0mework.Physics.SynchronizedJoint.CoframeContactLorentzClosure
import H0mework.Physics.JointVariation.CauchySafeScalarTemporalDevelopment
import H0mework.Physics.JointVariation.ResponseOperatorOriginAcceptance
import H0mework.Physics.ElectricJoint.ElectricCartanPrimalOriginClosure
import H0mework.Physics.CoframeVariation.CoframeECContactLocalActualLift
import H0mework.Physics.SafeCauchy.FixedGlobalOperator
import H0mework.Physics.ConstitutiveAction.ResponseOperator
import H0mework.Physics.DualVariation.JointResidualCarrier
import H0mework.Physics.CoframeResponse.MatterEulerAcceptance
import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerCore
import H0mework.Physics.GaugeAction.P286CompleteActionResponseOperator
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeArbitraryCoframeJointZeroFiber

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineCoframeHolonomicRegularity
open StageNineCoframeFirstJet
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLorentzClosure
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperatorOriginAcceptance
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeCompleteJointLiveElectricCartanPrimalOriginClosure
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerSoundness
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev Recentered (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Current contact

private abbrev Temporal (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
    Source (Recentered contact)

/-- The action-owned constitutive value write, now applied after the common
matter/adjoint/scalar temporal leg. -/
private abbrev Constitutive (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveWrittenCurrent Source (Temporal contact)

/-- The generic arbitrary-coframe P286 connection leg. -/
private abbrev PreEC (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  formNativeCurrentP286CompleteActionResponseOperator
    Source (Constitutive contact)

/-- One arbitrary-coframe EC contact write on the same dependency-ordered
actual. -/
def Contact (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
    Source (PreEC contact) 0

private abbrev PrimalReference (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    Source (Recentered contact)

def AcceptedContact (contact : BasePoint) : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    (Contact contact)

theorem acceptedContact_gravityConnection_origin_eq_cauchyBase
    (contact : BasePoint) :
    (AcceptedContact contact).gravityConnection 0 =
      (cartanECCauchyTemporalBase positiveSmoothUnifiedSource
        fixedP506L0CartanECConstraintCauchySafePreparedActual
        ).gravityConnection contact := by
  unfold AcceptedContact
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityConnection]
  unfold Contact
  rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]
  rw [formNativeCurrentP286CompleteActionResponseOperator_gravityConnection]
  rw [diracDualFormNativeConstitutiveWrittenCurrent_gravityConnection]
  rw [sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_gravityConnection]
  unfold Recentered
  exact fullyRecenterHolonomicConfiguration_gravityConnection_origin Current contact

theorem acceptedContact_reactionSelfGenerated (contact : BasePoint) :
    (AcceptedContact contact).gravitySimplicityMultiplier =
      formNativeGravityReactionField (AcceptedContact contact) := by
  have reactionEq :
      formNativeGravityReactionField (AcceptedContact contact) =
        formNativeGravityReactionField (Contact contact) := by
    have auxiliaryEq :
        (AcceptedContact contact).gravityAuxiliary =
          (Contact contact).gravityAuxiliary :=
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityAuxiliary
        (Contact contact)
    have connectionEq :
        (AcceptedContact contact).gravityConnection =
          (Contact contact).gravityConnection :=
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityConnection
        (Contact contact)
    funext point
    unfold formNativeGravityReactionField
      holonomicContravariantGravityCurvature holonomicGravityCurvature
      gravityConnectionDerivative
    rw [auxiliaryEq, connectionEq]
  have multiplierEq :
      (AcceptedContact contact).gravitySimplicityMultiplier =
        (Contact contact).gravitySimplicityMultiplier := by
    exact
      actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravitySimplicityMultiplier
        (Contact contact)
  rw [multiplierEq, reactionEq]
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reactionSelfGenerated
      Source (PreEC contact) 0

private theorem current_smooth : Current.Smooth := by
  exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth
    Source Prepared
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate

private theorem current_nondegenerate : Current.Nondegenerate :=
  by
    intro point
    change Matrix.det (Prepared.coframe point) ≠ 0
    exact fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 :=
  by
    change coframeTemporalPrincipalScalar (Prepared.coframe point) ≠ 0
    exact
      fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
        point

private theorem recentered_smooth (contact : BasePoint) :
    (Recentered contact).Smooth :=
  fullyRecenterHolonomicConfiguration_smooth Current current_smooth contact

private theorem recentered_nondegenerate (contact : BasePoint) :
    (Recentered contact).Nondegenerate := by
  intro point
  change Matrix.det
      (Current.coframe
        (canonicalSpacetimeContactTranslation contact point)) ≠ 0
  exact current_nondegenerate _

private theorem recentered_noncharacteristic (contact point : BasePoint) :
    coframeTemporalPrincipalScalar ((Recentered contact).coframe point) ≠ 0 := by
  change coframeTemporalPrincipalScalar
      (Current.coframe
        (canonicalSpacetimeContactTranslation contact point)) ≠ 0
  exact current_noncharacteristic _

private theorem recentered_matter_differentiable_origin
    (contact : BasePoint) :
    DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv ((Recentered contact).matter point))
      0 := by
  rcases recentered_smooth contact with
    ⟨_, _, _, _, _, _, _, matterSmooth, _⟩
  exact (matterSmooth.differentiable (by simp)).differentiableAt

private theorem recentered_matterCorrection_regular_origin
    (contact : BasePoint) :
    ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection Source
        (Recentered contact)) 0 := by
  exact
    (completeJointMatterTemporalCoordinateCorrection_contDiffAt
      Source (Recentered contact) (recentered_smooth contact) 0
      (recentered_nondegenerate contact 0)
      (recentered_noncharacteristic contact 0)).of_le (by simp)

private theorem primalReference_actionLaw_origin (contact : BasePoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (PrimalReference contact) 0
      (holonomicMatterCovariantDerivative (PrimalReference contact) 0
        canonicalLorentzianTimeDirection) := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_primalActionLaw_origin
      Source (Recentered contact)
      (recentered_matter_differentiable_origin contact)
      (recentered_matterCorrection_regular_origin contact)
      (recentered_noncharacteristic contact 0)

private theorem preEC_coframe_eq_recentered (contact : BasePoint) :
    (PreEC contact).coframe = (Recentered contact).coframe :=
  rfl

private theorem preEC_nondegenerate_origin (contact : BasePoint) :
    Matrix.det ((PreEC contact).coframe 0) ≠ 0 := by
  rw [preEC_coframe_eq_recentered contact]
  exact recentered_nondegenerate contact 0

private theorem temporal_scalarEuler_origin_zero
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient Source
        (Temporal contact) direction 0 = 0 := by
  exact
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalarEuler_origin_zero
      Source (Recentered contact) (recentered_smooth contact)
      (recentered_nondegenerate contact)
      (recentered_noncharacteristic contact) direction

private theorem preEC_p286Connection_origin_zero (contact : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (PreEC contact) 0 = 0 :=
  formNativeCurrentP286CompleteActionResponseOperator_connectionEquation_origin
    Source (Constitutive contact)

private theorem preEC_p286AuxiliaryEquation_origin (contact : BasePoint) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (PreEC contact) 0) := by
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (PreEC contact) 0)
      (preEC_nondegenerate_origin contact)).2
  change
    (PreEC contact).gaugeAuxiliary 0 =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        ((PreEC contact).coframe 0)
        (holonomicGaugeCurvature (PreEC contact) 0)
  rw [formNativeCurrentP286CompleteActionResponseOperator_gaugeAuxiliary_origin]
  rfl

private theorem preEC_p286AuxiliaryResidual_origin_zero (contact : BasePoint) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (PreEC contact) 0) = 0 :=
  (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
    (sourceGeneratedUnifiedCouplings Source)
    (toContinuumPointField (PreEC contact) 0)).2
    (preEC_p286AuxiliaryEquation_origin contact)

private theorem contact_coframeEuler_origin_zero (contact : BasePoint) :
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField (Contact contact) 0) = 0 := by
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_fullCoframeEuler_zero
      Source (PreEC contact) 0 (preEC_nondegenerate_origin contact)

private theorem contact_simplicity (contact : BasePoint) :
    FormNativeGravitySimplicityEquation (Contact contact) :=
  sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_simplicity
    Source (PreEC contact) 0

private theorem contact_auxiliaryEquation (contact : BasePoint) :
    FormNativeGravityAuxiliaryEquation (Contact contact) :=
  sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_auxiliaryEquation
    Source (PreEC contact) 0

private theorem contact_p286AuxiliaryResidual_origin_zero (contact : BasePoint) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (Contact contact) 0) = 0 := by
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (Contact contact) 0)).2
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (Contact contact) 0)
      (by
        change Matrix.det ((Contact contact).coframe 0) ≠ 0
        change Matrix.det ((PreEC contact).coframe 0) ≠ 0
        exact preEC_nondegenerate_origin contact)).2
  change
    (Contact contact).gaugeAuxiliary 0 =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        ((Contact contact).coframe 0)
        (holonomicGaugeCurvature (Contact contact) 0)
  change
    (PreEC contact).gaugeAuxiliary 0 =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        ((PreEC contact).coframe 0)
        (holonomicGaugeCurvature (PreEC contact) 0)
  exact
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField (PreEC contact) 0)
      (preEC_nondegenerate_origin contact)).1
      (preEC_p286AuxiliaryEquation_origin contact)

private theorem contact_p286Connection_origin_zero (contact : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (Contact contact) 0 = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [show
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (Contact contact) 0 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (PreEC contact) 0 by
      rfl]
  rw [show
      formNativeChargedGaugeThreeForm Source 0 0
          (toContinuumPointField (Contact contact) 0) =
        formNativeChargedGaugeThreeForm Source 0 0
          (toContinuumPointField (PreEC contact) 0) by
      exact
        formNativeChargedGaugeThreeForm_eq_of_actionData_eq
          Source (Contact contact) (PreEC contact) 0 rfl rfl rfl rfl rfl]
  exact preEC_p286Connection_origin_zero contact

private theorem contact_scalarCovariantDerivative_eq_temporal
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative (Contact contact) =
      holonomicScalarCovariantDerivative (Temporal contact) := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rfl

private theorem contact_scalarDifferentialMomentum_eq_temporal
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source (Contact contact) direction
        derivativeDirection =
      scalarDifferentialMomentum Source (Temporal contact) direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [contact_scalarCovariantDerivative_eq_temporal contact]
  rfl

private theorem contact_scalarDifferentialMomentumDivergence_eq_temporal
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source (Contact contact) direction =
      scalarDifferentialMomentumDivergence Source (Temporal contact)
        direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [contact_scalarDifferentialMomentum_eq_temporal]

private theorem contact_scalarAlgebraic_origin_eq_temporal
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient Source
        (Contact contact) direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient Source
        (Temporal contact) direction 0 := by
  have coframeEq :
      (Contact contact).coframe = (Temporal contact).coframe := rfl
  have scalarEq :
      (Contact contact).scalar = (Temporal contact).scalar := rfl
  have matterEq :
      (Contact contact).matter = (Temporal contact).matter := rfl
  have conjugateMatterEq :
      (Contact contact).conjugateMatter =
        (Temporal contact).conjugateMatter := rfl
  have variationEq :
      holonomicScalarVariationAlgebraicDirection
          (Contact contact) direction 0 =
        holonomicScalarVariationAlgebraicDirection
          (Temporal contact) direction 0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rfl
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coframeEq, scalarEq, matterEq,
    conjugateMatterEq,
    contact_scalarCovariantDerivative_eq_temporal contact, variationEq]

private theorem contact_scalarResidual_origin_zero (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source (Contact contact) 0
      ).scalar = 0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source
        (Contact contact) direction 0 = 0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [contact_scalarAlgebraic_origin_eq_temporal,
    congrFun
      (contact_scalarDifferentialMomentumDivergence_eq_temporal
        contact direction) 0]
  exact temporal_scalarEuler_origin_zero contact direction

private theorem recentered_coframeFirstJet_origin (contact : BasePoint) :
    holonomicCoframeFirstJetAt (Recentered contact).coframe 0 =
      holonomicCoframeFirstJetAt Current.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · exact fullyRecenterHolonomicConfiguration_coframe_origin Current contact
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point => Current.coframe point internal coordinate) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point => Current.coframe point internal coordinate)
          contact derivativeDirection
    simpa [canonicalSpacetimeContactTranslation] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point => Current.coframe point internal coordinate)
        contact 0 derivativeDirection

private theorem recentered_actionCartanConnection_origin
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt Source
        (Recentered contact) 0 =
      diracDualFormNativeActionCartanConnectionAt Source Current contact := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recentered_coframeFirstJet_origin contact,
    fullyRecenterHolonomicConfiguration_coframe_origin]
  rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
    Source (Recentered contact) Current 0 contact
    (fullyRecenterHolonomicConfiguration_coframe_origin Current contact)
    (fullyRecenterHolonomicConfiguration_matter_origin Current contact)
    (fullyRecenterHolonomicConfiguration_conjugateMatter_origin Current
      contact)]

private theorem recentered_connection_selfGenerated_origin
    (contact : BasePoint) :
    (Recentered contact).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt Source
        (Recentered contact) 0 := by
  rw [fullyRecenterHolonomicConfiguration_gravityConnection_origin,
    recentered_actionCartanConnection_origin]
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      Source Prepared contact

private theorem temporal_matter_origin_eq_recentered
    (contact : BasePoint) :
    (Temporal contact).matter 0 = (Recentered contact).matter 0 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source (Recentered contact)).matter 0 =
      (Recentered contact).matter 0
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source (Recentered contact) (0 : StageNineSpatialPoint)
  have zeroPoint :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [zeroPoint] at generated
  exact generated

private theorem temporal_conjugateMatter_origin_eq_recentered
    (contact : BasePoint) :
    (Temporal contact).conjugateMatter 0 =
      (Recentered contact).conjugateMatter 0 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source (Recentered contact)).conjugateMatter 0 =
      (Recentered contact).conjugateMatter 0
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source (Recentered contact) (0 : StageNineSpatialPoint)
  have zeroPoint :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [zeroPoint] at generated
  exact generated

private theorem contact_coframe_eq_recentered (contact : BasePoint) :
    (Contact contact).coframe = (Recentered contact).coframe :=
  rfl

private theorem contact_matter_origin_eq_recentered (contact : BasePoint) :
    (Contact contact).matter 0 = (Recentered contact).matter 0 := by
  change (Temporal contact).matter 0 = (Recentered contact).matter 0
  exact temporal_matter_origin_eq_recentered contact

private theorem contact_conjugateMatter_origin_eq_recentered
    (contact : BasePoint) :
    (Contact contact).conjugateMatter 0 =
      (Recentered contact).conjugateMatter 0 := by
  change
    (Temporal contact).conjugateMatter 0 =
      (Recentered contact).conjugateMatter 0
  exact temporal_conjugateMatter_origin_eq_recentered contact

private theorem contact_actionCartanConnection_origin_eq_recentered
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt Source (Contact contact) 0 =
      diracDualFormNativeActionCartanConnectionAt Source
        (Recentered contact) 0 := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [contact_coframe_eq_recentered contact]
  rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    Source (Contact contact) (Recentered contact) 0 rfl
    (contact_matter_origin_eq_recentered contact)
    (contact_conjugateMatter_origin_eq_recentered contact)]

private theorem contact_connection_selfGenerated_origin
    (contact : BasePoint) :
    (Contact contact).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt Source
        (Contact contact) 0 := by
  unfold Contact
  rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]
  change
    (Recentered contact).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt Source
        (Contact contact) 0
  rw [contact_actionCartanConnection_origin_eq_recentered]
  exact recentered_connection_selfGenerated_origin contact

private theorem contact_coframe_smooth (contact : BasePoint) :
    ContDiff ℝ ∞ (Contact contact).coframe := by
  rw [contact_coframe_eq_recentered contact]
  exact holonomicCoframe_contDiff (Recentered contact)
    (recentered_smooth contact)

private theorem contact_gravityAuxiliaryJet_origin
    (contact : BasePoint) :
    holonomicGravityAuxiliaryJet (Contact contact) 0 =
      pointwisePhysicalIIPlusJet
        (holonomicCoframeFirstJetAt (Contact contact).coframe 0) := by
  have restricted :
      restrictHolonomicConfigurationToIIPlus (Contact contact) =
        Contact contact :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      (Contact contact)).2 (contact_simplicity contact)
  rw [← restricted]
  exact
    holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
      (Contact contact) (contact_coframe_smooth contact) 0

private theorem contact_connection_skew_origin (contact : BasePoint) :
    LorentzSkew ((Contact contact).gravityConnection 0) := by
  rw [contact_connection_selfGenerated_origin contact]
  exact diracDualFormNativeActionCartanConnectionAt_lorentzSkew
    Source (Contact contact) 0 (by
      change Matrix.det ((PreEC contact).coframe 0) ≠ 0
      exact preEC_nondegenerate_origin contact)

private theorem contact_torsionSpin_origin (contact : BasePoint) :
    cartanTorsionThreeForm ((Contact contact).coframe 0)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt (Contact contact).coframe 0)
          ((Contact contact).gravityConnection 0)) =
      diracDualFormNativeActionSpinResponseAt Source (Contact contact) 0 := by
  rw [contact_connection_selfGenerated_origin contact]
  exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
    Source (Contact contact) 0 (by
      change Matrix.det ((PreEC contact).coframe 0) ≠ 0
      exact preEC_nondegenerate_origin contact)

private theorem contact_lorentzResidual_origin_zero (contact : BasePoint) :
    holonomicFormNativeLorentzEulerThreeForm Source 0
        (Contact contact) 0 = 0 :=
  holonomicFormNativeLorentzEulerThreeForm_zero_of_auxiliaryJet_torsionSpin
    Source (Contact contact) 0 (contact_connection_skew_origin contact)
    (contact_gravityAuxiliaryJet_origin contact)
    (contact_torsionSpin_origin contact)

private theorem contact_coframe_eq_primalReference (contact : BasePoint) :
    (Contact contact).coframe = (PrimalReference contact).coframe := by
  rfl

private theorem contact_matter_eq_primalReference (contact : BasePoint) :
    (Contact contact).matter = (PrimalReference contact).matter := by
  rfl

private theorem contact_conjugateMatter_eq_primalReference
    (contact : BasePoint) :
    (Contact contact).conjugateMatter =
      (PrimalReference contact).conjugateMatter := by
  rfl

private theorem contact_scalar_origin_eq_primalReference
    (contact : BasePoint) :
    (Contact contact).scalar 0 = (PrimalReference contact).scalar 0 := by
  have safeOrigin :
      (Contact contact).scalar 0 = (Recentered contact).scalar 0 := by
    change (Temporal contact).scalar 0 = (Recentered contact).scalar 0
    exact
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_scalar_origin
        Source (Recentered contact)
  have standardOrigin :
      (PrimalReference contact).scalar 0 =
        (Recentered contact).scalar 0 := by
    change
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source (Recentered contact)).scalar 0 =
        (Recentered contact).scalar 0
    have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        Source (Recentered contact) (0 : StageNineSpatialPoint)
    have zeroPoint :
        canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
      ext direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]
    rw [zeroPoint] at generated
    exact generated
  exact safeOrigin.trans standardOrigin.symm

private theorem contact_gaugeConnection_origin_eq_primalReference
    (contact : BasePoint) :
    (Contact contact).gaugeConnection 0 =
      (PrimalReference contact).gaugeConnection 0 := by
  have referenceOrigin :
      (PrimalReference contact).gaugeConnection 0 =
        (Recentered contact).gaugeConnection 0 := by
    change
      (diracDualFormNativeP286CanonicalJointCandidate Source
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          Source (Recentered contact))
        (diracDualFormNativeP286CanonicalGeneratedWrite Source
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source (Recentered contact)))).gaugeConnection 0 =
        (Recentered contact).gaugeConnection 0
    exact
      (canonicalJointCandidate_connection_origin_raw
        (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          Source (Recentered contact))
        (diracDualFormNativeP286CanonicalGeneratedWrite Source
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source (Recentered contact)))).trans rfl
  change
    (Recentered contact).gaugeConnection 0 =
      (PrimalReference contact).gaugeConnection 0
  exact referenceOrigin.symm

private theorem contact_gravityConnection_origin_eq_primalReference
    (contact : BasePoint) :
    (Contact contact).gravityConnection 0 =
      (PrimalReference contact).gravityConnection 0 := by
  rw [contact_connection_selfGenerated_origin contact]
  have referenceSelfGenerated :
      (PrimalReference contact).gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt Source
          (PrimalReference contact) 0 := by
    change
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (completeJointLiveElectricGlobalP286Current Source
          (Recentered contact))).gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt Source
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
            (completeJointLiveElectricGlobalP286Current Source
              (Recentered contact))) 0
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
        Source
        (completeJointLiveElectricGlobalP286Current Source
          (Recentered contact)) 0
  rw [referenceSelfGenerated]
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [contact_coframe_eq_primalReference contact]
  rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    Source (Contact contact) (PrimalReference contact) 0 rfl
    (congrFun (contact_matter_eq_primalReference contact) 0)
    (congrFun (contact_conjugateMatter_eq_primalReference contact) 0)]

private theorem contact_matterCovariantDerivative_origin_eq_primalReference
    (contact : BasePoint) :
    holonomicMatterCovariantDerivative (Contact contact) 0 =
      holonomicMatterCovariantDerivative (PrimalReference contact) 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [contact_matter_eq_primalReference contact,
    contact_gravityConnection_origin_eq_primalReference contact,
    contact_gaugeConnection_origin_eq_primalReference contact]

private theorem contact_primalActionLaw_origin (contact : BasePoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (Contact contact) 0
      (holonomicMatterCovariantDerivative (Contact contact) 0
        canonicalLorentzianTimeDirection) := by
  have generated := primalReference_actionLaw_origin contact
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
    holonomicDiracDualCurrentCoframeMatterKnownVector at generated ⊢
  rw [contact_coframe_eq_primalReference contact,
    contact_scalar_origin_eq_primalReference contact,
    contact_matter_eq_primalReference contact,
    contact_matterCovariantDerivative_origin_eq_primalReference contact]
  exact generated

private theorem contact_conjugateMatter_eq_temporal (contact : BasePoint) :
    (Contact contact).conjugateMatter = (Temporal contact).conjugateMatter :=
  rfl

private theorem contact_conjugateMatterCoordinates_differentiableAt_origin
    (contact : BasePoint) :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates (Contact contact)) 0 := by
  have baseRegular : ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates (Recentered contact)) 0 :=
    (holonomicConjugateMatterCoordinates_contDiff
      (Recentered contact) (recentered_smooth contact)).contDiffAt.of_le
        (by norm_num)
  have correctionRegular : ContDiffAt ℝ 1
      (completeJointAdjointTemporalCoordinateCorrection Source
        (Recentered contact)) 0 :=
    (completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
      Source (Recentered contact) (recentered_smooth contact) 0
      (recentered_nondegenerate contact 0)
      (recentered_noncharacteristic contact 0)).of_le (by norm_num)
  have primitiveRegular : ContDiffAt ℝ 1
      (canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source
          (Recentered contact))) 0 :=
    canonicalTimePrimitive_contDiffAt_of_contDiffAt _ correctionRegular
  have coordinateEq :
      holonomicConjugateMatterCoordinates (Contact contact) =
        holonomicConjugateMatterCoordinates (Recentered contact) +
          canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection Source
              (Recentered contact)) := by
    rw [show holonomicConjugateMatterCoordinates (Contact contact) =
        holonomicConjugateMatterCoordinates (Temporal contact) by
      unfold holonomicConjugateMatterCoordinates
      rw [contact_conjugateMatter_eq_temporal contact]]
    funext point
    simp only [Temporal,
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_conjugateMatter,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter,
      holonomicConjugateMatterCoordinates, matterDualCoordinates_add,
      matterDualCoordinates_matterDualOfCoordinates]
    rfl
  rw [coordinateEq]
  exact (baseRegular.add primitiveRegular).differentiableAt (by norm_num)

private theorem contact_nondegenerate_origin (contact : BasePoint) :
    Matrix.det ((Contact contact).coframe 0) ≠ 0 := by
  change Matrix.det ((PreEC contact).coframe 0) ≠ 0
  exact preEC_nondegenerate_origin contact

private theorem contact_noncharacteristic_origin (contact : BasePoint) :
    coframeTemporalPrincipalScalar ((Contact contact).coframe 0) ≠ 0 := by
  rw [contact_coframe_eq_recentered contact]
  exact recentered_noncharacteristic contact 0

private theorem acceptedContact_adjointActionLaw_origin (contact : BasePoint) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (AcceptedContact contact) 0
      (holonomicConjugateMatterDerivativeDual
        (AcceptedContact contact) 0 canonicalLorentzianTimeDirection) := by
  exact
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw_of_coordinateDifferentiableAt
      (Contact contact)
      (contact_conjugateMatterCoordinates_differentiableAt_origin contact)
      (contact_nondegenerate_origin contact)
      (contact_noncharacteristic_origin contact)

private theorem acceptedContact_coframe_differentiableAt_origin
    (contact : BasePoint) :
    DifferentiableAt ℝ (AcceptedContact contact).coframe 0 := by
  change DifferentiableAt ℝ (Contact contact).coframe 0
  exact
    ((contact_coframe_smooth contact).differentiable (by simp)).differentiableAt

private theorem
    acceptedContact_conjugateMatterCoordinates_differentiableAt_origin
    (contact : BasePoint) :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates (AcceptedContact contact)) 0 := by
  have baseDifferentiable :=
    contact_conjugateMatterCoordinates_differentiableAt_origin contact
  have responseDifferentiable : DifferentiableAt ℝ
      (conjugateMatterLinearTimeCoordinateWrite
        (liveCoframeConjugateMatterTimeResponseWrite (Contact contact))) 0 :=
    ((conjugateMatterLinearTimeCoordinateWrite_contDiff _).differentiable
      (by simp)).differentiableAt
  have coordinateEq :
      holonomicConjugateMatterCoordinates (AcceptedContact contact) =
        holonomicConjugateMatterCoordinates (Contact contact) +
          conjugateMatterLinearTimeCoordinateWrite
            (liveCoframeConjugateMatterTimeResponseWrite
              (Contact contact)) := by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        (Contact contact)
        (liveCoframeConjugateMatterTimeResponseWrite (Contact contact)) point
  rw [coordinateEq]
  exact baseDifferentiable.add responseDifferentiable

private theorem acceptedContact_matterResidual_origin_zero (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (AcceptedContact contact) 0).matter = 0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source
        (AcceptedContact contact) direction 0 = 0
  exact
    holonomicDiracDualMatterEulerLagrange_eq_zero_of_liveCoframeActionLaw
      Source (AcceptedContact contact) 0
      (acceptedContact_coframe_differentiableAt_origin contact)
      (acceptedContact_conjugateMatterCoordinates_differentiableAt_origin
        contact)
      (by simpa [AcceptedContact] using contact_nondegenerate_origin contact)
      (acceptedContact_adjointActionLaw_origin contact) direction

private theorem acceptedContact_primalActionLaw_origin (contact : BasePoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (AcceptedContact contact) 0
      (holonomicMatterCovariantDerivative (AcceptedContact contact) 0
        canonicalLorentzianTimeDirection) := by
  have generated := contact_primalActionLaw_origin contact
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
    holonomicDiracDualCurrentCoframeMatterKnownVector at generated ⊢
  simpa [AcceptedContact, holonomicMatterCovariantDerivative] using generated

private theorem acceptedContact_conjugateMatterResidual_origin_zero
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (AcceptedContact contact) 0).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source
        (AcceptedContact contact) direction 0 = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    Source (AcceptedContact contact) 0
    (acceptedContact_primalActionLaw_origin contact)]
  simp

private theorem contact_conjugateMatterResidual_origin_zero
    (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (Contact contact) 0).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source
        (Contact contact) direction 0 = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    Source (Contact contact) 0 (contact_primalActionLaw_origin contact)]
  simp

/-- Before the final live-adjoint leg, the exact EC contact has already
settled every mother-action channel except the adjoint-controlled matter
Euler read.  This is an exhaustive residual readout, not a producer. -/
theorem contact_jointResidual_origin_eq_matterRead
    (contact : BasePoint) :
    diracDualFormNativePointwiseJointResidual Source (Contact contact) 0 =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        matter :=
          (diracDualFormNativePointwiseJointResidual Source
            (Contact contact) 0).matter } := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · change formNativeGravityMultiplierEulerResidual
      (toContinuumPointField (Contact contact) 0) = 0
    exact
      (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
        (contact_simplicity contact 0)
  · change formNativeGravityAuxiliaryEulerResidual
      (toContinuumPointField (Contact contact) 0) = 0
    exact congrFun (contact_auxiliaryEquation contact) 0
  · exact contact_p286AuxiliaryResidual_origin_zero contact
  · exact contact_lorentzResidual_origin_zero contact
  · exact contact_p286Connection_origin_zero contact
  · exact contact_scalarResidual_origin_zero contact
  · rfl
  · exact contact_conjugateMatterResidual_origin_zero contact
  · exact contact_coframeEuler_origin_zero contact

private theorem acceptedContact_pointField_origin_eq_contact
    (contact : BasePoint) :
    toContinuumPointField (AcceptedContact contact) 0 =
      toContinuumPointField (Contact contact) 0 :=
  actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin
    (Contact contact)

private theorem acceptedContact_gravityAuxiliaryExterior_origin_eq_contact
    (contact : BasePoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (AcceptedContact contact) 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative
        (Contact contact) 0 := by
  have connectionEq :
      (AcceptedContact contact).gravityConnection =
        (Contact contact).gravityConnection :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityConnection
      (Contact contact)
  have auxiliaryEq :
      (AcceptedContact contact).gravityAuxiliary =
        (Contact contact).gravityAuxiliary :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gravityAuxiliary
      (Contact contact)
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [connectionEq, auxiliaryEq]

private theorem acceptedContact_p286AuxiliaryExterior_origin_eq_contact
    (contact : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (AcceptedContact contact) 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (Contact contact) 0 := by
  have connectionEq :
      (AcceptedContact contact).gaugeConnection =
        (Contact contact).gaugeConnection :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gaugeConnection
      (Contact contact)
  have auxiliaryEq :
      (AcceptedContact contact).gaugeAuxiliary =
        (Contact contact).gaugeAuxiliary :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gaugeAuxiliary
      (Contact contact)
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [connectionEq, auxiliaryEq]

private theorem acceptedContact_lorentzResidual_origin_zero
    (contact : BasePoint) :
    holonomicFormNativeLorentzEulerThreeForm Source 0
        (AcceptedContact contact) 0 = 0 := by
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [acceptedContact_gravityAuxiliaryExterior_origin_eq_contact contact,
    acceptedContact_pointField_origin_eq_contact contact]
  exact contact_lorentzResidual_origin_zero contact

private theorem acceptedContact_p286Connection_origin_zero
    (contact : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (AcceptedContact contact) 0 = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [acceptedContact_p286AuxiliaryExterior_origin_eq_contact contact,
    acceptedContact_pointField_origin_eq_contact contact]
  exact contact_p286Connection_origin_zero contact

private theorem acceptedContact_scalarCovariantDerivative_eq_contact
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative (AcceptedContact contact) =
      holonomicScalarCovariantDerivative (Contact contact) := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rfl

private theorem acceptedContact_scalarDifferentialMomentum_eq_contact
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source (AcceptedContact contact) direction
        derivativeDirection =
      scalarDifferentialMomentum Source (Contact contact) direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [acceptedContact_scalarCovariantDerivative_eq_contact contact]
  rfl

private theorem
    acceptedContact_scalarDifferentialMomentumDivergence_eq_contact
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source (AcceptedContact contact)
        direction =
      scalarDifferentialMomentumDivergence Source (Contact contact)
        direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [acceptedContact_scalarDifferentialMomentum_eq_contact]

private theorem acceptedContact_scalarAlgebraic_origin_eq_contact
    (contact : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient Source
        (AcceptedContact contact) direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient Source
        (Contact contact) direction 0 := by
  have coframeEq :
      (AcceptedContact contact).coframe = (Contact contact).coframe :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_coframe
      (Contact contact)
  have scalarEq :
      (AcceptedContact contact).scalar = (Contact contact).scalar :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_scalar
      (Contact contact)
  have matterEq :
      (AcceptedContact contact).matter = (Contact contact).matter :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter
      (Contact contact)
  have conjugateMatterEq :
      (AcceptedContact contact).conjugateMatter 0 =
        (Contact contact).conjugateMatter 0 :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
      (Contact contact)
  have gaugeConnectionEq :
      (AcceptedContact contact).gaugeConnection =
        (Contact contact).gaugeConnection :=
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_gaugeConnection
      (Contact contact)
  have variationEq :
      holonomicScalarVariationAlgebraicDirection
          (AcceptedContact contact) direction 0 =
        holonomicScalarVariationAlgebraicDirection
          (Contact contact) direction 0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [gaugeConnectionEq]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [coframeEq, scalarEq, matterEq, conjugateMatterEq,
    acceptedContact_scalarCovariantDerivative_eq_contact contact,
    variationEq]

private theorem acceptedContact_scalarResidual_origin_zero (contact : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      (AcceptedContact contact) 0).scalar = 0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source
        (AcceptedContact contact) direction 0 = 0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [acceptedContact_scalarAlgebraic_origin_eq_contact contact,
    congrFun
      (acceptedContact_scalarDifferentialMomentumDivergence_eq_contact
        contact direction) 0]
  exact congrFun (contact_scalarResidual_origin_zero contact) direction

private theorem acceptedContact_gravityMultiplierResidual_origin_zero
    (contact : BasePoint) :
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField (AcceptedContact contact) 0) = 0 := by
  calc
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField (AcceptedContact contact) 0) =
        formNativeGravityMultiplierEulerResidual
          (toContinuumPointField (Contact contact) 0) :=
      congrArg formNativeGravityMultiplierEulerResidual
        (acceptedContact_pointField_origin_eq_contact contact)
    _ = 0 :=
      (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
        (contact_simplicity contact 0)

private theorem acceptedContact_gravityAuxiliaryResidual_origin_zero
    (contact : BasePoint) :
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField (AcceptedContact contact) 0) = 0 := by
  calc
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField (AcceptedContact contact) 0) =
        formNativeGravityAuxiliaryEulerResidual
          (toContinuumPointField (Contact contact) 0) :=
      congrArg formNativeGravityAuxiliaryEulerResidual
        (acceptedContact_pointField_origin_eq_contact contact)
    _ = 0 := congrFun (contact_auxiliaryEquation contact) 0

private theorem acceptedContact_p286AuxiliaryResidual_origin_zero
    (contact : BasePoint) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (AcceptedContact contact) 0) = 0 := by
  calc
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField (AcceptedContact contact) 0) =
        formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (toContinuumPointField (Contact contact) 0) :=
      congrArg
        (formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings Source))
        (acceptedContact_pointField_origin_eq_contact contact)
    _ = 0 := contact_p286AuxiliaryResidual_origin_zero contact

private theorem acceptedContact_coframeResidual_origin_zero
    (contact : BasePoint) :
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField (AcceptedContact contact) 0) = 0 := by
  calc
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField (AcceptedContact contact) 0) =
        diracDualFormNativeCoframeEulerCovector Source 0
          (toContinuumPointField (Contact contact) 0) :=
      congrArg (diracDualFormNativeCoframeEulerCovector Source 0)
        (acceptedContact_pointField_origin_eq_contact contact)
    _ = 0 := contact_coframeEuler_origin_zero contact

theorem acceptedContact_jointZeroFiber_origin (contact : BasePoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber Source
      (AcceptedContact contact) 0 := by
  apply
    (onDiracDualFormNativePointwiseJointZeroFiber_iff_components
      Source (AcceptedContact contact) 0).2
  exact
    ⟨acceptedContact_gravityMultiplierResidual_origin_zero contact,
      acceptedContact_gravityAuxiliaryResidual_origin_zero contact,
      acceptedContact_p286AuxiliaryResidual_origin_zero contact,
      acceptedContact_lorentzResidual_origin_zero contact,
      acceptedContact_p286Connection_origin_zero contact,
      acceptedContact_scalarResidual_origin_zero contact,
      acceptedContact_matterResidual_origin_zero contact,
      acceptedContact_conjugateMatterResidual_origin_zero contact,
      acceptedContact_coframeResidual_origin_zero contact⟩

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeArbitraryCoframeJointZeroFiber
