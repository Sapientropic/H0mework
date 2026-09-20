import H0mework.Physics.GaugeAction.FullSynchronizedCompleteP286ActionResponseOperator
import H0mework.Physics.MatterCurrent.P286PrincipalFirstGermP286ConnectionSpatialCauchyClosure

/-!
# C3h186a: canonical-origin full-action replay of the complete first germ

The already generated exact P506/L0 complete matter first-germ actual
`U****` is fed back through the dependency-ordered full synchronized action
producer and then through the complete P286 response.  Re-evaluating the
inner action graph returns the C3h181 synchronized actual `U**`; `U****` and
`U**` have the same actual eleven-sector point field at the canonical origin,
and the outer P286 producer preserves that point field.  Hence the composed
producer gives one genuine canonical-origin local actual lift of `U****`.

The proof follows the action graph forward: source/current spin, unique
contorsion, canonical matter/adjoint germ, non-gravity stress, coframe,
multiplier, curvature, and finally the P286 response.  No residual is used to
reconstruct an endpoint.  No event, branch, scheduler, response witness,
stationarity receipt, or source-time evolution is accepted or produced.

The replay equalities are producer-soundness/consistency.  They are not new
independent Euler--Lagrange constraints.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalOriginActionReplay

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeSectorStress
open StageNineConjugateMatterActionTimeVelocity
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermP286ConnectionSpatialCauchyClosure
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterCompleteFirstGermResponse
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalMatterTemporalFirstGermResponse

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev BaseActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual

private abbrev SynchronizedActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual

private abbrev CompleteFirstGermActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentCompleteFirstGermResponseActual

abbrev positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual :
    StageNineHolonomicConfiguration :=
  fullSynchronizedCompleteP286ActionResponseOperator
    positiveSmoothUnifiedSource CompleteFirstGermActual

private theorem contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem completeFirstGerm_originField_eq_synchronized :
    toContinuumPointField CompleteFirstGermActual 0 =
      toContinuumPointField SynchronizedActual 0 :=
  positiveP506MatterCurrentCompleteFirstGermResponseActual_originField.trans
    positiveP506MatterCurrentTemporalFirstGermResponseActual_originField

private theorem completeFirstGerm_coframe_origin_eq_base :
    CompleteFirstGermActual.coframe 0 = BaseActual.coframe 0 := by
  have contactEq := congrArg StageNineContinuumPointField.coframe
    completeFirstGerm_originField_eq_synchronized
  change
    CompleteFirstGermActual.coframe 0 = SynchronizedActual.coframe 0
    at contactEq
  calc
    CompleteFirstGermActual.coframe 0 =
        SynchronizedActual.coframe 0 := contactEq
    _ = BaseActual.coframe 0 := rfl

private theorem completeFirstGerm_matter_origin_eq_base :
    CompleteFirstGermActual.matter 0 = BaseActual.matter 0 := by
  have contactEq := congrArg StageNineContinuumPointField.matter
    completeFirstGerm_originField_eq_synchronized
  change
    CompleteFirstGermActual.matter 0 = SynchronizedActual.matter 0
    at contactEq
  calc
    CompleteFirstGermActual.matter 0 =
        SynchronizedActual.matter 0 := contactEq
    _ = BaseActual.matter 0 := by
      exact fullSynchronizedActionResponseOperator_preserves_matter_origin
        positiveSmoothUnifiedSource BaseActual

private theorem completeFirstGerm_conjugateMatter_origin_eq_base :
    CompleteFirstGermActual.conjugateMatter 0 =
      BaseActual.conjugateMatter 0 := by
  have contactEq := congrArg StageNineContinuumPointField.conjugateMatter
    completeFirstGerm_originField_eq_synchronized
  change
    CompleteFirstGermActual.conjugateMatter 0 =
      SynchronizedActual.conjugateMatter 0 at contactEq
  calc
    CompleteFirstGermActual.conjugateMatter 0 =
        SynchronizedActual.conjugateMatter 0 := contactEq
    _ = BaseActual.conjugateMatter 0 := by
      exact
        fullSynchronizedActionResponseOperator_preserves_conjugateMatter_origin
          positiveSmoothUnifiedSource BaseActual

private theorem completeFirstGerm_spin_eq_base :
    fullSynchronizedActionSpin positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionSpin positiveSmoothUnifiedSource BaseActual := by
  unfold fullSynchronizedActionSpin
  exact actualMatterSpinActionCoordinates_eq_of_origin_fields
    positiveSmoothUnifiedSource CompleteFirstGermActual BaseActual
    completeFirstGerm_coframe_origin_eq_base
    completeFirstGerm_matter_origin_eq_base
    completeFirstGerm_conjugateMatter_origin_eq_base

private theorem completeFirstGerm_contorsion_eq_base :
    fullSynchronizedActionContorsion positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionContorsion positiveSmoothUnifiedSource
        BaseActual := by
  unfold fullSynchronizedActionContorsion
  rw [completeFirstGerm_spin_eq_base]

private theorem completeFirstGerm_lorentzOrigin_eq_base :
    fullSynchronizedActionLorentzOrigin positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionLorentzOrigin positiveSmoothUnifiedSource
        BaseActual := by
  unfold fullSynchronizedActionLorentzOrigin
  rw [completeFirstGerm_contorsion_eq_base]

private theorem completeFirstGerm_curvature_origin_eq_baseResponse :
    holonomicGravityCurvature CompleteFirstGermActual 0 =
      fullSynchronizedActionGravityCurvature positiveSmoothUnifiedSource
        BaseActual := by
  have contactEq := congrArg StageNineContinuumPointField.gravityCurvature
    completeFirstGerm_originField_eq_synchronized
  calc
    holonomicGravityCurvature CompleteFirstGermActual 0 =
        holonomicGravityCurvature SynchronizedActual 0 := by
      simpa [toContinuumPointField] using contactEq
    _ = fullSynchronizedActionGravityCurvature positiveSmoothUnifiedSource
          BaseActual := by
      exact fullSynchronizedActionResponseOperator_curvature_origin _ _

private theorem completeFirstGerm_lorentzActual_gravityConnection_eq_synchronized :
    (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).gravityConnection =
      SynchronizedActual.gravityConnection := by
  unfold fullSynchronizedActionLorentzActual SynchronizedActual
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
    fullSynchronizedActionResponseOperator
  rw [completeFirstGerm_lorentzOrigin_eq_base,
    completeFirstGerm_curvature_origin_eq_baseResponse]

private theorem completeFirstGerm_actionMatterCauchyState_matter_constant :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  exact
    positiveP506MatterCurrentCompleteFirstGermResponseActual_matter_canonicalZeroSlice
      space

private theorem completeFirstGerm_actionMatterCauchyState_conjugateMatter_constant :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).conjugateMatter =
      fun _ =>
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier) := by
  funext space
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  exact
    positiveP506MatterCurrentCompleteFirstGermResponseActual_conjugateMatter_canonicalZeroSlice
      space

private theorem completeFirstGerm_actionMatterCauchyState_matter_eq_base :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).matter =
      (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
        BaseActual).matter := by
  rw [completeFirstGerm_actionMatterCauchyState_matter_constant,
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_actionMatterCauchyState_matter_constant]

private theorem completeFirstGerm_actionMatterCauchyState_conjugateMatter_eq_base :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).conjugateMatter =
      (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
        BaseActual).conjugateMatter := by
  rw [completeFirstGerm_actionMatterCauchyState_conjugateMatter_constant,
    positiveP506MatterCurrentCompleteActionPrincipalSecondJetActual_actionMatterCauchyState_conjugateMatter_constant]

private theorem completeFirstGerm_actionMatterCauchyState_gravityConnection_origin_eq_base :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).gravityConnection 0 =
      (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
        BaseActual).gravityConnection 0 := by
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).gravityConnection
        (canonicalCauchySlicePoint 0 0) =
      (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
        BaseActual).gravityConnection (canonicalCauchySlicePoint 0 0)
  rw [contactZero]
  rw [completeFirstGerm_lorentzActual_gravityConnection_eq_synchronized]
  change
    (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
      BaseActual).gravityConnection 0 =
      (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
        BaseActual).gravityConnection 0
  rw [fullSynchronizedActionResponseOperator_connection_origin]
  exact
    (normalizedAffineLorentzConnectionField_zero
      (fullSynchronizedActionLorentzOrigin positiveSmoothUnifiedSource
        BaseActual)
      (holonomicGravityCurvature BaseActual 0)).symm

private theorem completeFirstGerm_actionMatterCauchyState_gaugeConnection_origin_eq_base :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).gaugeConnection 0 =
      (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
        BaseActual).gaugeConnection 0 := by
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    CompleteFirstGermActual.gaugeConnection
        (canonicalCauchySlicePoint 0 0) =
      BaseActual.gaugeConnection (canonicalCauchySlicePoint 0 0)
  rw [contactZero]
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeConnection,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeConnection]
  rfl

private theorem completeFirstGerm_actionMatterCauchyState_scalar_origin_eq_base :
    (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
      CompleteFirstGermActual).scalar 0 =
      (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
        BaseActual).scalar 0 := by
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    CompleteFirstGermActual.scalar (canonicalCauchySlicePoint 0 0) =
      BaseActual.scalar (canonicalCauchySlicePoint 0 0)
  rw [contactZero]
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_scalar,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_scalar]
  rfl

private theorem actionGeneratedMatterLocalField_eq_of_state_contact
    (first second : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matterEq : first.matter = second.matter)
    (gravityConnectionEq :
      first.gravityConnection space = second.gravityConnection space)
    (gaugeConnectionEq :
      first.gaugeConnection space = second.gaugeConnection space)
    (scalarEq : first.scalar space = second.scalar space) :
    actionGeneratedMatterLocalField first space =
      actionGeneratedMatterLocalField second space := by
  funext point
  apply matterCoordinateEquiv.injective
  unfold actionGeneratedMatterLocalField actionGeneratedMatterLocalCoordinate
    actionGeneratedMatterLocalIncrement actionGeneratedMatterLocalJetCoordinate
    actionGeneratedMatterRawTimeVelocity
    actionGeneratedMatterTimeCovariantDerivative
    actionGeneratedMatterKnownVector cauchyMatterSpatialCovariantDerivative
    cauchyMatterSpatialDerivativeCoordinate cauchyMatterConnectionAction
  rw [matterEq, gravityConnectionEq, gaugeConnectionEq, scalarEq]

private theorem actionGeneratedConjugateMatterLocalField_eq_of_state_contact
    (first second : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (conjugateMatterEq : first.conjugateMatter = second.conjugateMatter)
    (gravityConnectionEq :
      first.gravityConnection space = second.gravityConnection space)
    (gaugeConnectionEq :
      first.gaugeConnection space = second.gaugeConnection space)
    (scalarEq : first.scalar space = second.scalar space) :
    actionGeneratedConjugateMatterLocalField first space =
      actionGeneratedConjugateMatterLocalField second space := by
  funext point
  unfold actionGeneratedConjugateMatterLocalField
    actionGeneratedConjugateMatterLocalJet
    actionGeneratedConjugateMatterTimeDerivative
    actionGeneratedConjugateMatterKnownDual
    actionGeneratedMatterAlgebraicOperator
    actionGeneratedConjugateMatterSpatialTransport
    cauchyConjugateMatterSpatialDerivative
    cauchyConjugateMatterSpatialDerivativeCoordinate
    cauchyMatterVariationConnectionOperator
  rw [conjugateMatterEq, gravityConnectionEq, gaugeConnectionEq, scalarEq]

private theorem completeFirstGerm_actionMatterField_eq_base :
    actionGeneratedMatterLocalField
        (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
          CompleteFirstGermActual) 0 =
      actionGeneratedMatterLocalField
        (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
          BaseActual) 0 := by
  exact actionGeneratedMatterLocalField_eq_of_state_contact _ _ 0
    completeFirstGerm_actionMatterCauchyState_matter_eq_base
    completeFirstGerm_actionMatterCauchyState_gravityConnection_origin_eq_base
    completeFirstGerm_actionMatterCauchyState_gaugeConnection_origin_eq_base
    completeFirstGerm_actionMatterCauchyState_scalar_origin_eq_base

private theorem completeFirstGerm_actionConjugateMatterField_eq_base :
    actionGeneratedConjugateMatterLocalField
        (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
          CompleteFirstGermActual) 0 =
      actionGeneratedConjugateMatterLocalField
        (fullSynchronizedActionMatterCauchyState positiveSmoothUnifiedSource
          BaseActual) 0 := by
  exact actionGeneratedConjugateMatterLocalField_eq_of_state_contact _ _ 0
    completeFirstGerm_actionMatterCauchyState_conjugateMatter_eq_base
    completeFirstGerm_actionMatterCauchyState_gravityConnection_origin_eq_base
    completeFirstGerm_actionMatterCauchyState_gaugeConnection_origin_eq_base
    completeFirstGerm_actionMatterCauchyState_scalar_origin_eq_base

private theorem completeFirstGerm_coframe_eq_base :
    CompleteFirstGermActual.coframe = BaseActual.coframe := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_coframe,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_coframe]
  rfl

private theorem completeFirstGerm_gravityAuxiliary_eq_base :
    CompleteFirstGermActual.gravityAuxiliary =
      BaseActual.gravityAuxiliary := by
  rfl

private theorem completeFirstGerm_gaugeConnection_eq_base :
    CompleteFirstGermActual.gaugeConnection = BaseActual.gaugeConnection := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_gaugeConnection,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_gaugeConnection]
  rfl

private theorem completeFirstGerm_gaugeAuxiliary_eq_base :
    CompleteFirstGermActual.gaugeAuxiliary = BaseActual.gaugeAuxiliary := by
  rfl

private theorem completeFirstGerm_scalar_eq_base :
    CompleteFirstGermActual.scalar = BaseActual.scalar := by
  rw [positiveP506MatterCurrentCompleteFirstGermResponseActual_scalar,
    positiveP506MatterCurrentTemporalFirstGermResponseActual_scalar]
  rfl

private theorem completeFirstGerm_actionMatterActual_coframe_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).coframe =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).coframe := by
  exact completeFirstGerm_coframe_eq_base

private theorem completeFirstGerm_actionMatterActual_gravityConnection_origin_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).gravityConnection 0 =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).gravityConnection 0 := by
  change
    (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).gravityConnection 0 =
      (fullSynchronizedActionLorentzActual positiveSmoothUnifiedSource
        BaseActual).gravityConnection 0
  rw [completeFirstGerm_lorentzActual_gravityConnection_eq_synchronized]
  change
    (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
      BaseActual).gravityConnection 0 = _
  rw [fullSynchronizedActionResponseOperator_connection_origin]
  exact
    (normalizedAffineLorentzConnectionField_zero
      (fullSynchronizedActionLorentzOrigin positiveSmoothUnifiedSource
        BaseActual)
      (holonomicGravityCurvature BaseActual 0)).symm

private theorem completeFirstGerm_actionMatterActual_gaugeConnection_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).gaugeConnection =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).gaugeConnection := by
  exact completeFirstGerm_gaugeConnection_eq_base

private theorem completeFirstGerm_actionMatterActual_gaugeAuxiliary_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).gaugeAuxiliary =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).gaugeAuxiliary := by
  exact completeFirstGerm_gaugeAuxiliary_eq_base

private theorem completeFirstGerm_actionMatterActual_scalar_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).scalar =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).scalar := by
  exact completeFirstGerm_scalar_eq_base

private theorem completeFirstGerm_actionMatterActual_matter_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).matter =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).matter :=
  completeFirstGerm_actionMatterField_eq_base

private theorem completeFirstGerm_actionMatterActual_conjugateMatter_eq_base :
    (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
      CompleteFirstGermActual).conjugateMatter =
      (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
        BaseActual).conjugateMatter :=
  completeFirstGerm_actionConjugateMatterField_eq_base

private abbrev CompleteFirstGermMatterOriginField :
    StageNineContinuumPointField :=
  fullSynchronizedActionMatterOriginField positiveSmoothUnifiedSource
    CompleteFirstGermActual

private abbrev BaseMatterOriginField : StageNineContinuumPointField :=
  fullSynchronizedActionMatterOriginField positiveSmoothUnifiedSource
    BaseActual

private theorem completeFirstGerm_matterOrigin_coframe_eq_base :
    CompleteFirstGermMatterOriginField.coframe =
      BaseMatterOriginField.coframe := by
  exact congrFun completeFirstGerm_actionMatterActual_coframe_eq_base 0

private theorem completeFirstGerm_matterOrigin_gaugeCurvature_eq_base :
    CompleteFirstGermMatterOriginField.gaugeCurvature =
      BaseMatterOriginField.gaugeCurvature := by
  change
    holonomicGaugeCurvature
        (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
          CompleteFirstGermActual) 0 =
      holonomicGaugeCurvature
        (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
          BaseActual) 0
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [completeFirstGerm_actionMatterActual_gaugeConnection_eq_base]

private theorem completeFirstGerm_matterOrigin_gaugeAuxiliary_eq_base :
    CompleteFirstGermMatterOriginField.gaugeAuxiliary =
      BaseMatterOriginField.gaugeAuxiliary := by
  exact congrFun
    completeFirstGerm_actionMatterActual_gaugeAuxiliary_eq_base 0

private theorem completeFirstGerm_matterOrigin_scalar_eq_base :
    CompleteFirstGermMatterOriginField.scalar =
      BaseMatterOriginField.scalar := by
  exact congrFun completeFirstGerm_actionMatterActual_scalar_eq_base 0

private theorem completeFirstGerm_matterOrigin_scalarCovariantDerivative_eq_base :
    CompleteFirstGermMatterOriginField.scalarCovariantDerivative =
      BaseMatterOriginField.scalarCovariantDerivative := by
  change
    holonomicScalarCovariantDerivative
        (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
          CompleteFirstGermActual) 0 =
      holonomicScalarCovariantDerivative
        (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
          BaseActual) 0
  unfold holonomicScalarCovariantDerivative
  rw [completeFirstGerm_actionMatterActual_scalar_eq_base,
    completeFirstGerm_actionMatterActual_gaugeConnection_eq_base]

private theorem completeFirstGerm_matterOrigin_matter_eq_base :
    CompleteFirstGermMatterOriginField.matter =
      BaseMatterOriginField.matter := by
  exact congrFun completeFirstGerm_actionMatterActual_matter_eq_base 0

private theorem completeFirstGerm_matterOrigin_matterCovariantDerivative_eq_base :
    CompleteFirstGermMatterOriginField.matterCovariantDerivative =
      BaseMatterOriginField.matterCovariantDerivative := by
  change
    holonomicMatterCovariantDerivative
        (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
          CompleteFirstGermActual) 0 =
      holonomicMatterCovariantDerivative
        (fullSynchronizedActionMatterActual positiveSmoothUnifiedSource
          BaseActual) 0
  unfold holonomicMatterCovariantDerivative
  rw [completeFirstGerm_actionMatterActual_matter_eq_base,
    completeFirstGerm_actionMatterActual_gravityConnection_origin_eq_base,
    completeFirstGerm_actionMatterActual_gaugeConnection_eq_base]

private theorem completeFirstGerm_matterOrigin_conjugateMatter_eq_base :
    CompleteFirstGermMatterOriginField.conjugateMatter =
      BaseMatterOriginField.conjugateMatter := by
  exact congrFun
    completeFirstGerm_actionMatterActual_conjugateMatter_eq_base 0

private theorem completeFirstGerm_gaugeDensity_eq_base
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        CompleteFirstGermMatterOriginField candidate =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        BaseMatterOriginField candidate := by
  unfold coframeGaugeSectorLocalDensity
  simp only [StageNineCoframeVariation.withCoframe, generatedVolumeDensity]
  rw [completeFirstGerm_matterOrigin_gaugeCurvature_eq_base,
    completeFirstGerm_matterOrigin_gaugeAuxiliary_eq_base]

private theorem completeFirstGerm_scalarDensity_eq_base
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        CompleteFirstGermMatterOriginField candidate =
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        BaseMatterOriginField candidate := by
  unfold coframeScalarSectorLocalDensity generatedScalarKineticDensity
  simp only [StageNineCoframeVariation.withCoframe, generatedVolumeDensity]
  rw [completeFirstGerm_matterOrigin_scalar_eq_base,
    completeFirstGerm_matterOrigin_scalarCovariantDerivative_eq_base]

private theorem completeFirstGerm_matterDensity_eq_base
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        CompleteFirstGermMatterOriginField candidate =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        BaseMatterOriginField candidate := by
  unfold coframeMatterSectorLocalDensity generatedContinuumMatterDensity
    generatedContinuumMatterVector
  simp only [StageNineCoframeVariation.withCoframe, generatedVolumeDensity]
  rw [completeFirstGerm_matterOrigin_scalar_eq_base,
    completeFirstGerm_matterOrigin_matter_eq_base,
    completeFirstGerm_matterOrigin_matterCovariantDerivative_eq_base,
    completeFirstGerm_matterOrigin_conjugateMatter_eq_base]

private theorem completeFirstGerm_gaugeStress_eq_base :
    coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
        CompleteFirstGermMatterOriginField =
      coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
        BaseMatterOriginField := by
  unfold coframeGaugeSectorStressCovector
  rw [show
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        CompleteFirstGermMatterOriginField =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        BaseMatterOriginField by
    funext candidate
    exact completeFirstGerm_gaugeDensity_eq_base candidate]
  rw [completeFirstGerm_matterOrigin_coframe_eq_base]

private theorem completeFirstGerm_scalarStress_eq_base :
    coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
        CompleteFirstGermMatterOriginField =
      coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
        BaseMatterOriginField := by
  unfold coframeScalarSectorStressCovector
  rw [show
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        CompleteFirstGermMatterOriginField =
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        BaseMatterOriginField by
    funext candidate
    exact completeFirstGerm_scalarDensity_eq_base candidate]
  rw [completeFirstGerm_matterOrigin_coframe_eq_base]

private theorem completeFirstGerm_matterStress_eq_base :
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        CompleteFirstGermMatterOriginField =
      coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        BaseMatterOriginField := by
  unfold coframeMatterSectorStressCovector
  rw [show
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        CompleteFirstGermMatterOriginField =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        BaseMatterOriginField by
    funext candidate
    exact completeFirstGerm_matterDensity_eq_base candidate]
  rw [completeFirstGerm_matterOrigin_coframe_eq_base]

private theorem completeFirstGerm_nonGravityStress_eq_base :
    fullSynchronizedActionNonGravityCoframeStress
        positiveSmoothUnifiedSource CompleteFirstGermActual =
      fullSynchronizedActionNonGravityCoframeStress
        positiveSmoothUnifiedSource BaseActual := by
  unfold fullSynchronizedActionNonGravityCoframeStress
  rw [completeFirstGerm_gaugeStress_eq_base,
    completeFirstGerm_scalarStress_eq_base,
    completeFirstGerm_matterStress_eq_base]

private theorem completeFirstGerm_coframeResponse_eq_base :
    fullSynchronizedActionCoframeResponse positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionCoframeResponse positiveSmoothUnifiedSource
        BaseActual := by
  unfold fullSynchronizedActionCoframeResponse
  rw [completeFirstGerm_nonGravityStress_eq_base]

private theorem completeFirstGerm_gravityMultiplierResponse_eq_base :
    fullSynchronizedActionGravityMultiplier positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionGravityMultiplier positiveSmoothUnifiedSource
        BaseActual := by
  unfold fullSynchronizedActionGravityMultiplier
  rw [completeFirstGerm_coframeResponse_eq_base]

private theorem completeFirstGerm_gravityCurvatureResponse_eq_base :
    fullSynchronizedActionGravityCurvature positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionGravityCurvature positiveSmoothUnifiedSource
        BaseActual := by
  unfold fullSynchronizedActionGravityCurvature
  rw [completeFirstGerm_coframeResponse_eq_base]

theorem
    positiveP506MatterCurrentCompleteFirstGerm_fullSynchronizedActionResponseOperator_replays_synchronizedActual :
    fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual =
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual := by
  change
    fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        CompleteFirstGermActual =
      fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        BaseActual
  unfold fullSynchronizedActionResponseOperator
  apply StageNineHolonomicConfiguration.ext
  · exact completeFirstGerm_coframe_eq_base
  · rw [completeFirstGerm_lorentzOrigin_eq_base,
      completeFirstGerm_gravityCurvatureResponse_eq_base]
  · exact completeFirstGerm_gravityAuxiliary_eq_base
  · funext point
    exact completeFirstGerm_gravityMultiplierResponse_eq_base
  · exact completeFirstGerm_gaugeConnection_eq_base
  · exact completeFirstGerm_gaugeAuxiliary_eq_base
  · exact completeFirstGerm_scalar_eq_base
  · exact completeFirstGerm_actionMatterField_eq_base
  · exact completeFirstGerm_actionConjugateMatterField_eq_base

theorem
    positiveP506MatterCurrentCompleteFirstGerm_fullSynchronizedActionResponseOperator_pointField_origin :
    toContinuumPointField
        (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteFirstGermResponseActual) 0 =
      toContinuumPointField
        positiveP506MatterCurrentCompleteFirstGermResponseActual 0 := by
  rw [positiveP506MatterCurrentCompleteFirstGerm_fullSynchronizedActionResponseOperator_replays_synchronizedActual]
  exact completeFirstGerm_originField_eq_synchronized.symm

theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual_pointField_origin :
    toContinuumPointField
        positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual 0 =
      toContinuumPointField
        positiveP506MatterCurrentCompleteFirstGermResponseActual 0 := by
  rw [fullSynchronizedCompleteP286ActionResponseOperator_pointField_origin]
  exact
    positiveP506MatterCurrentCompleteFirstGerm_fullSynchronizedActionResponseOperator_pointField_origin

private theorem completeFirstGerm_innerResponse_coframe_one
    (point : BasePoint) :
    (fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermResponseActual).coframe point =
      1 := by
  rw [positiveP506MatterCurrentCompleteFirstGerm_fullSynchronizedActionResponseOperator_replays_synchronizedActual]
  exact
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_coframe_one
      point

/-- Re-substitution of the outer P286 response at the common origin.  This is
producer consistency, not an independent constraint. -/
theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual_p286ConnectionEulerLagrange_origin_producerConsistency
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual
        direction 0 =
      0 := by
  exact
    fullSynchronizedCompleteP286ActionResponseOperator_connectionProducerConsistency
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentCompleteFirstGermResponseActual
      completeFirstGerm_innerResponse_coframe_one direction

/-! ## No-premise checkpoint bundle -/

structure
    PositiveP506MatterCurrentCompleteFirstGermCanonicalOriginActionReplayLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization.canonicalP506SourceAffineL0ObservableLineageReference
  faithfulCompleteMatterZeroFiber :
    positiveP506MatterCurrentCompleteFirstGermResponseActual =
          positiveP506MatterCurrentCompleteFirstGermBaseActual ↔
      positiveP506MatterCurrentCompleteDiracYukawaFirstGermResidual = 0
  innerFullActionReplay :
    fullSynchronizedActionResponseOperator positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermResponseActual =
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
  canonicalOriginPointFieldReplay :
    toContinuumPointField
        positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual 0 =
      toContinuumPointField
        positiveP506MatterCurrentCompleteFirstGermResponseActual 0
  producerP286OriginConsistency : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual
        direction 0 =
      0

theorem
    positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual_realizes_C3h186a :
    PositiveP506MatterCurrentCompleteFirstGermCanonicalOriginActionReplayLaw := by
  exact
    { exactP506L0Lineage :=
        positiveP506MatterCurrentCompleteFirstGermResponseActual_exactP506L0Lineage
      faithfulCompleteMatterZeroFiber :=
        positiveP506MatterCurrentCompleteFirstGermResponseActual_eq_base_iff
      innerFullActionReplay :=
        positiveP506MatterCurrentCompleteFirstGerm_fullSynchronizedActionResponseOperator_replays_synchronizedActual
      canonicalOriginPointFieldReplay :=
        positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual_pointField_origin
      producerP286OriginConsistency :=
        positiveP506MatterCurrentCompleteFirstGermCanonicalOriginReplayActual_p286ConnectionEulerLagrange_origin_producerConsistency }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalOriginActionReplay
