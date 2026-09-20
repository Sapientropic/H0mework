import H0mework.Physics.SynchronizedJoint.FixedRadialFirstJet
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality
import H0mework.Physics.Holonomic.HolonomicGaugeCurvatureTransport

/-!
# Fixed P506/L0 synchronized Lorentz-path action-jet naturality

The exact path occurrence has already emitted one global actual and its
all-point radial connection first jet.  This module compares that final
action jet with the native Cartan--EC contact generated from the same
occurrence prefix.  Seven typed seams exhaust the coordinates that the
Lorentz path and live reaction can change; every other primitive/read slot
is proved identical.

The seam is evaluated only after both action jets exist.  It is a transporter
and residual normal form, not an input to either writer and not a source of a
correction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetNaturality

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicGaugeCurvatureTransport
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor
private abbrev Base : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact
    Source Input point

private theorem coframe_point_eq (point : BasePoint) :
    Final.coframe point = (Contact point).coframe 0 := by
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
  change 1 =
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
      Source (fullyRecenterHolonomicConfiguration Base point) 0).coframe 0
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  rw [fullyRecenterHolonomicConfiguration_coframe_origin]
  exact congrFun
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one
    point |>.symm

private theorem gravityAuxiliary_point_eq (point : BasePoint) :
    Final.gravityAuxiliary point = (Contact point).gravityAuxiliary 0 := by
  rw [show Final.gravityAuxiliary point = Base.gravityAuxiliary point by rfl]
  change Base.gravityAuxiliary point =
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
      Source (fullyRecenterHolonomicConfiguration Base point) 0
      ).gravityAuxiliary 0
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_auxiliary]
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  rw [fullyRecenterHolonomicConfiguration_coframe_origin]
  exact fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_simplicity point

private theorem gaugeConnection_point_eq (point : BasePoint) :
    Final.gaugeConnection point = (Contact point).gaugeConnection 0 := by
  change Base.gaugeConnection point =
    (fullyRecenterHolonomicConfiguration Base point).gaugeConnection 0
  exact (fullyRecenterHolonomicConfiguration_gaugeConnection_origin Base point).symm

private theorem scalar_point_eq (point : BasePoint) :
    Final.scalar point = (Contact point).scalar 0 := by
  change Base.scalar point =
    (fullyRecenterHolonomicConfiguration Base point).scalar 0
  exact (fullyRecenterHolonomicConfiguration_scalar_origin Base point).symm

private theorem matter_point_eq (point : BasePoint) :
    Final.matter point = (Contact point).matter 0 := by
  change Base.matter point =
    (fullyRecenterHolonomicConfiguration Base point).matter 0
  exact (fullyRecenterHolonomicConfiguration_matter_origin Base point).symm

private theorem conjugateMatter_point_eq (point : BasePoint) :
    Final.conjugateMatter point = (Contact point).conjugateMatter 0 := by
  change Base.conjugateMatter point =
    (fullyRecenterHolonomicConfiguration Base point).conjugateMatter 0
  exact (fullyRecenterHolonomicConfiguration_conjugateMatter_origin Base point).symm

private theorem contact_gravityConnection_point_eq_base
    (point : BasePoint) :
    (Contact point).gravityConnection 0 = Base.gravityConnection point := by
  rw [
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact_connection_normalForm,
    normalizedAffineLorentzConnectionField_zero,
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileOrigin_eq_base]
  rfl

private theorem final_gaugeConnection_eq_base :
    Final.gaugeConnection = Base.gaugeConnection := by
  change
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeConnection =
      Base.gaugeConnection
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gaugeConnection
      Source Input

private theorem contact_gaugeConnection_eq_recenter
    (point : BasePoint) :
    (Contact point).gaugeConnection =
      (fullyRecenterHolonomicConfiguration Base point).gaugeConnection := by
  unfold Contact
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact_eq_nativeActionWrite]
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection]

private theorem final_gaugeAuxiliary_eq_base :
    Final.gaugeAuxiliary = Base.gaugeAuxiliary := by
  change
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeAuxiliary =
      Base.gaugeAuxiliary
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gaugeAuxiliary
      Source Input

private theorem contact_gaugeAuxiliary_eq_recenter
    (point : BasePoint) :
    (Contact point).gaugeAuxiliary =
      (fullyRecenterHolonomicConfiguration Base point).gaugeAuxiliary := by
  unfold Contact
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact_eq_nativeActionWrite]
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary]

private theorem gaugeAuxiliary_point_eq (point : BasePoint) :
    Final.gaugeAuxiliary point = (Contact point).gaugeAuxiliary 0 := by
  calc
    Final.gaugeAuxiliary point = Base.gaugeAuxiliary point :=
      congrFun final_gaugeAuxiliary_eq_base point
    _ = (fullyRecenterHolonomicConfiguration Base point).gaugeAuxiliary 0 :=
      (fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin Base point).symm
    _ = (Contact point).gaugeAuxiliary 0 :=
      (congrFun (contact_gaugeAuxiliary_eq_recenter point) 0).symm

private theorem gaugeCurvature_point_eq (point : BasePoint) :
    holonomicGaugeCurvature Final point =
      holonomicGaugeCurvature (Contact point) 0 := by
  calc
    holonomicGaugeCurvature Final point =
        holonomicGaugeCurvature Base point :=
      holonomicGaugeCurvature_eq_of_connection_eq Final Base
        final_gaugeConnection_eq_base point
    _ = holonomicGaugeCurvature
        (fullyRecenterHolonomicConfiguration Base point) 0 :=
      (fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
        Base point).symm
    _ = holonomicGaugeCurvature (Contact point) 0 :=
      (holonomicGaugeCurvature_eq_of_connection_eq (Contact point)
        (fullyRecenterHolonomicConfiguration Base point)
        (contact_gaugeConnection_eq_recenter point) 0).symm

private theorem scalarCovariantDerivative_point_eq (point : BasePoint) :
    holonomicScalarCovariantDerivative Final point =
      holonomicScalarCovariantDerivative (Contact point) 0 := by
  calc
    holonomicScalarCovariantDerivative Final point =
        holonomicScalarCovariantDerivative Base point := by
      unfold holonomicScalarCovariantDerivative
      rw [show Final.scalar = Base.scalar by
        change
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.scalar =
            Base.scalar
        rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
        exact
          sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_scalar
            Source Input]
      rw [final_gaugeConnection_eq_base]
    _ = holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration Base point) 0 :=
      (fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
        Base point).symm
    _ = holonomicScalarCovariantDerivative (Contact point) 0 := by
      unfold holonomicScalarCovariantDerivative
      rw [show (Contact point).scalar =
          (fullyRecenterHolonomicConfiguration Base point).scalar by
        unfold Contact
        rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzProfileContact_eq_nativeActionWrite]
        rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar]]
      rw [contact_gaugeConnection_eq_recenter point]

private theorem p286GaugeAuxiliaryExteriorCovariantDerivative_point_eq
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Final point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (Contact point) 0 := by
  calc
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Final point =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Base point := by
      unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        p286GaugeAuxiliaryDirectionalDerivative
        holonomicP286GaugeConnectionCoordinate
        holonomicP286GaugeAuxiliaryCoordinate
      rw [final_gaugeConnection_eq_base, final_gaugeAuxiliary_eq_base]
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (fullyRecenterHolonomicConfiguration Base point) 0 :=
      (fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
        Base point).symm
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (Contact point) 0 := by
      unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        p286GaugeAuxiliaryDirectionalDerivative
        holonomicP286GaugeConnectionCoordinate
        holonomicP286GaugeAuxiliaryCoordinate
      rw [contact_gaugeConnection_eq_recenter point,
        contact_gaugeAuxiliary_eq_recenter point]

@[ext] structure LorentzPathActionJetSeam where
  gravityConnection : PointwiseLorentzSpinConnection
  gravityCurvature : PhysicalBivector
  gravitySimplicityMultiplier : PhysicalBivector
  matterCovariantDerivative :
    LorentzianIndex → DiracExteriorMatterCarrier
  gravityAuxiliaryExteriorCovariantDerivative : PhysicalBivectorThreeForm
  scalarDifferentialMomentumDivergence : ScalarCoordinateCarrier → ℝ
  matterDifferentialMomentumDivergence : MatterCoordinateCarrier → ℝ

def lorentzPathActionJetSeam
    (finalJet contactJet : DiracDualFormNativePointwiseActionJetCarrier) :
    LorentzPathActionJetSeam :=
  { gravityConnection :=
      finalJet.gravityConnection - contactJet.gravityConnection
    gravityCurvature :=
      finalJet.pointField.gravityCurvature -
        contactJet.pointField.gravityCurvature
    gravitySimplicityMultiplier :=
      finalJet.pointField.gravitySimplicityMultiplier -
        contactJet.pointField.gravitySimplicityMultiplier
    matterCovariantDerivative :=
      finalJet.pointField.matterCovariantDerivative -
        contactJet.pointField.matterCovariantDerivative
    gravityAuxiliaryExteriorCovariantDerivative :=
      finalJet.gravityAuxiliaryExteriorCovariantDerivative -
        contactJet.gravityAuxiliaryExteriorCovariantDerivative
    scalarDifferentialMomentumDivergence :=
      finalJet.scalarDifferentialMomentumDivergence -
        contactJet.scalarDifferentialMomentumDivergence
    matterDifferentialMomentumDivergence :=
      finalJet.matterDifferentialMomentumDivergence -
        contactJet.matterDifferentialMomentumDivergence }

def pointwiseActionJetWithLorentzPathSeam
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : LorentzPathActionJetSeam) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  { contactJet with
    pointField :=
      { contactJet.pointField with
        gravityCurvature :=
          seam.gravityCurvature + contactJet.pointField.gravityCurvature
        gravitySimplicityMultiplier :=
          seam.gravitySimplicityMultiplier +
            contactJet.pointField.gravitySimplicityMultiplier
        matterCovariantDerivative :=
          seam.matterCovariantDerivative +
            contactJet.pointField.matterCovariantDerivative }
    gravityConnection :=
      seam.gravityConnection + contactJet.gravityConnection
    gravityAuxiliaryExteriorCovariantDerivative :=
      seam.gravityAuxiliaryExteriorCovariantDerivative +
        contactJet.gravityAuxiliaryExteriorCovariantDerivative
    scalarDifferentialMomentumDivergence :=
      seam.scalarDifferentialMomentumDivergence +
        contactJet.scalarDifferentialMomentumDivergence
    matterDifferentialMomentumDivergence :=
      seam.matterDifferentialMomentumDivergence +
        contactJet.matterDifferentialMomentumDivergence }

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_actionJet_naturality
    (point : BasePoint) :
    let finalJet :=
      generatedDiracDualFormNativePointwiseActionJet Source Final point
    let contactJet :=
      generatedDiracDualFormNativePointwiseActionJet Source (Contact point) 0
    finalJet =
      pointwiseActionJetWithLorentzPathSeam contactJet
        (lorentzPathActionJetSeam finalJet contactJet) := by
  dsimp only
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · exact coframe_point_eq point
    · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]
    · exact gravityAuxiliary_point_eq point
    · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]
    · exact gaugeCurvature_point_eq point
    · exact gaugeAuxiliary_point_eq point
    · exact scalar_point_eq point
    · exact scalarCovariantDerivative_point_eq point
    · exact matter_point_eq point
    · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]
    · exact conjugateMatter_point_eq point
  · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]
  · exact gaugeConnection_point_eq point
  · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]
  · exact p286GaugeAuxiliaryExteriorCovariantDerivative_point_eq point
  · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]
  · simp [pointwiseActionJetWithLorentzPathSeam, lorentzPathActionJetSeam]

/-- Recover the ordinary primitive derivative from the occurrence-owned
lowered radial first jet.  The Lorentz sign is involutive, so no inverse or
variance certificate is supplied. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityConnectionDerivative_eq_radialFirstJet
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    gravityConnectionDerivative Final point derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) =
      minkowskiInternalSign (pairFirst internalPair) *
        completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
          Source Input point (coordinateDirection derivativeDirection)
          formDirection internalPair := by
  have lowered :=
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_loweredConnectionFirstJet_eq_radialFirstJet
      point derivativeDirection formDirection internalPair
  fin_cases internalPair <;>
    simp [minkowskiInternalSign, pairFirst, pairSecond] at lowered ⊢ <;>
    linarith

/-- Curvature read from the emitted primitive path, expressed entirely by
its generated radial first jet and its own point value. -/
def
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureNormalForm
    (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let sign := minkowskiInternalSign internalOut
    sign *
      (sign *
          completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
            Source Input point (coordinateDirection first) second internalPair -
        sign *
          completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
            Source Input point (coordinateDirection second) first internalPair +
        ∑ middle : LorentzianIndex,
          (Final.gravityConnection point first internalOut middle *
              Final.gravityConnection point second middle internalIn -
            Final.gravityConnection point second internalOut middle *
              Final.gravityConnection point first middle internalIn))

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityCurvature_normalForm
    (point : BasePoint) :
    holonomicGravityCurvature Final point =
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureNormalForm
        point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureNormalForm
  dsimp only
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityConnectionDerivative_eq_radialFirstJet,
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityConnectionDerivative_eq_radialFirstJet]

/-- Point-value seam of the emitted path relative to the exact native contact
origin.  The right side contains only the source-owned radial write and the
pre-path prefix field. -/
def
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialConnectionValueSeam
    (point : BasePoint) : PointwiseLorentzSpinConnection :=
  completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField
      Source Input point -
    Base.gravityConnection point

/-- Curvature seam obtained by applying `dω + ω∧ω` to the generated radial
first jet and comparing it with the same-occurrence native contact. -/
def
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureSeam
    (point : BasePoint) : PhysicalBivector :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureNormalForm
      point -
    holonomicGravityCurvature (Contact point) 0

def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
    (point : BasePoint) :
    LorentzPathActionJetSeam :=
  lorentzPathActionJetSeam
    (generatedDiracDualFormNativePointwiseActionJet Source Final point)
    (generatedDiracDualFormNativePointwiseActionJet Source (Contact point) 0)

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam_gravityConnection
    (point : BasePoint) :
    (fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
      point).gravityConnection =
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialConnectionValueSeam
        point := by
  unfold
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
    lorentzPathActionJetSeam
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialConnectionValueSeam
  change
    Final.gravityConnection point - (Contact point).gravityConnection 0 = _
  rw [show Final.gravityConnection =
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField
        Source Input by
    change
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gravityConnection = _
    rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gravityConnection
        Source Input]
  rw [contact_gravityConnection_point_eq_base]

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam_gravityCurvature
    (point : BasePoint) :
    (fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
      point).gravityCurvature =
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureSeam
        point := by
  unfold
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
    lorentzPathActionJetSeam
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathRadialGravityCurvatureSeam
  change
    holonomicGravityCurvature Final point -
        holonomicGravityCurvature (Contact point) 0 = _
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityCurvature_normalForm]

def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetNormalForm
    (point : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  pointwiseActionJetWithLorentzPathSeam
    (generatedDiracDualFormNativePointwiseActionJet Source (Contact point) 0)
    (fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetSeam
      point)

def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathPointwiseJointResidualNormalForm
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualOfActionJet Source point
    (fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetNormalForm
      point)

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_pointwiseJointResidual_normalForm
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual Source Final point =
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathPointwiseJointResidualNormalForm
        point := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_actionJet_naturality]
  rfl

/-- The multiplier/simplicity coordinate vanishes globally on the emitted
path actual. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityMultiplierResidual_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point
      ).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField Final point) = 0
  apply
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
  exact
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_simplicity
      point

/-- The final live-reaction leg globally settles the gravity-auxiliary
coordinate on the same emitted actual. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_gravityAuxiliaryResidual_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point
      ).gravityAuxiliary = 0 := by
  change holonomicFormNativeGravityAuxiliaryEulerResidual Final point = 0
  exact congrFun
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gravityAuxiliaryEquation
      Source Input)
    point

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_pointwiseZeroFiber_iff_normalForm_zero
    (point : BasePoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber Source Final point ↔
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathPointwiseJointResidualNormalForm
        point = 0 := by
  unfold OnDiracDualFormNativePointwiseJointZeroFiber
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPath_pointwiseJointResidual_normalForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetNaturality
