import H0mework.Physics.GravityTail.FixedCurvatureIntegrabilityFactor
import H0mework.Physics.GravityResponse.AwayCurvatureNoGo
import H0mework.Physics.Holonomic.HolonomicGravityCurvatureFirstGermCongruence
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Constraint/Cauchy gravity-tail all-point residual normal form

The source/current-only gravity-tail occurrence has already emitted one
global actual.  This file compares its complete pointwise action jet with the
matching recentered native contact.  The normal form is defined only after
the output exists and is used solely as a whole-carrier readout.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseAwayCurvatureNoGo
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureFirstGermCongruence
open StageNineLorentzConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Current

private abbrev OriginConnection : PointwiseLorentzSpinConnection :=
  Current.gravityConnection 0

private abbrev OriginTarget : PhysicalBivector :=
  diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual

private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailProfileContact Source Current point

private theorem base_gaugeConnection_eq_current :
    Base.gaugeConnection = Current.gaugeConnection := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
      Source Current 0

private theorem base_gaugeAuxiliary_eq_current :
    Base.gaugeAuxiliary = Current.gaugeAuxiliary := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
      Source Current 0

private theorem base_scalar_eq_current : Base.scalar = Current.scalar := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar
      Source Current 0

private theorem base_matter_eq_current : Base.matter = Current.matter := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter
      Source Current 0

private theorem base_conjugateMatter_eq_current :
    Base.conjugateMatter = Current.conjugateMatter := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
      Source Current 0

private theorem output_gaugeConnection_eq_base :
    Output.gaugeConnection = Base.gaugeConnection := by
  calc
    Output.gaugeConnection = Current.gaugeConnection := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          Source Current).gaugeConnection = Current.gaugeConnection
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeConnection
          Source Current
    _ = Base.gaugeConnection := base_gaugeConnection_eq_current.symm

private theorem output_gaugeAuxiliary_eq_base :
    Output.gaugeAuxiliary = Base.gaugeAuxiliary := by
  calc
    Output.gaugeAuxiliary = Current.gaugeAuxiliary := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          Source Current).gaugeAuxiliary = Current.gaugeAuxiliary
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeAuxiliary
          Source Current
    _ = Base.gaugeAuxiliary := base_gaugeAuxiliary_eq_current.symm

private theorem output_scalar_eq_base : Output.scalar = Base.scalar := by
  calc
    Output.scalar = Current.scalar := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          Source Current).scalar = Current.scalar
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_scalar
          Source Current
    _ = Base.scalar := base_scalar_eq_current.symm

private theorem output_matter_eq_base : Output.matter = Base.matter := by
  calc
    Output.matter = Current.matter := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          Source Current).matter = Current.matter
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_matter
          Source Current
    _ = Base.matter := base_matter_eq_current.symm

private theorem output_conjugateMatter_eq_base :
    Output.conjugateMatter = Base.conjugateMatter := by
  calc
    Output.conjugateMatter = Current.conjugateMatter := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          Source Current).conjugateMatter = Current.conjugateMatter
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_conjugateMatter
          Source Current
    _ = Base.conjugateMatter := base_conjugateMatter_eq_current.symm

private theorem contact_gaugeConnection_eq_recenter (point : BasePoint) :
    (Contact point).gaugeConnection =
      (fullyRecenterHolonomicConfiguration Base point).gaugeConnection := by
  unfold Contact
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
      Source (fullyRecenterHolonomicConfiguration Base point) 0

private theorem contact_gaugeAuxiliary_eq_recenter (point : BasePoint) :
    (Contact point).gaugeAuxiliary =
      (fullyRecenterHolonomicConfiguration Base point).gaugeAuxiliary := by
  unfold Contact
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
      Source (fullyRecenterHolonomicConfiguration Base point) 0

private theorem gaugeConnection_point_eq (point : BasePoint) :
    Output.gaugeConnection point = (Contact point).gaugeConnection 0 := by
  calc
    Output.gaugeConnection point = Base.gaugeConnection point :=
      congrFun output_gaugeConnection_eq_base point
    _ = (fullyRecenterHolonomicConfiguration Base point).gaugeConnection 0 :=
      (fullyRecenterHolonomicConfiguration_gaugeConnection_origin Base point).symm
    _ = (Contact point).gaugeConnection 0 :=
      (congrFun (contact_gaugeConnection_eq_recenter point) 0).symm

private theorem gaugeAuxiliary_point_eq (point : BasePoint) :
    Output.gaugeAuxiliary point = (Contact point).gaugeAuxiliary 0 := by
  calc
    Output.gaugeAuxiliary point = Base.gaugeAuxiliary point :=
      congrFun output_gaugeAuxiliary_eq_base point
    _ = (fullyRecenterHolonomicConfiguration Base point).gaugeAuxiliary 0 :=
      (fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin Base point).symm
    _ = (Contact point).gaugeAuxiliary 0 :=
      (congrFun (contact_gaugeAuxiliary_eq_recenter point) 0).symm

private theorem scalar_point_eq (point : BasePoint) :
    Output.scalar point = (Contact point).scalar 0 := by
  calc
    Output.scalar point = Base.scalar point := congrFun output_scalar_eq_base point
    _ = (fullyRecenterHolonomicConfiguration Base point).scalar 0 :=
      (fullyRecenterHolonomicConfiguration_scalar_origin Base point).symm
    _ = (Contact point).scalar 0 := by rfl

private theorem matter_point_eq (point : BasePoint) :
    Output.matter point = (Contact point).matter 0 := by
  calc
    Output.matter point = Base.matter point := congrFun output_matter_eq_base point
    _ = (fullyRecenterHolonomicConfiguration Base point).matter 0 :=
      (fullyRecenterHolonomicConfiguration_matter_origin Base point).symm
    _ = (Contact point).matter 0 := by rfl

private theorem conjugateMatter_point_eq (point : BasePoint) :
    Output.conjugateMatter point = (Contact point).conjugateMatter 0 := by
  calc
    Output.conjugateMatter point = Base.conjugateMatter point :=
      congrFun output_conjugateMatter_eq_base point
    _ = (fullyRecenterHolonomicConfiguration Base point).conjugateMatter 0 :=
      (fullyRecenterHolonomicConfiguration_conjugateMatter_origin Base point).symm
    _ = (Contact point).conjugateMatter 0 := by rfl

private theorem gaugeCurvature_point_eq (point : BasePoint) :
    holonomicGaugeCurvature Output point =
      holonomicGaugeCurvature (Contact point) 0 := by
  calc
    holonomicGaugeCurvature Output point =
        holonomicGaugeCurvature Base point :=
      holonomicGaugeCurvature_eq_of_connection_eq Output Base
        output_gaugeConnection_eq_base point
    _ = holonomicGaugeCurvature
        (fullyRecenterHolonomicConfiguration Base point) 0 :=
      (fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
        Base point).symm
    _ = holonomicGaugeCurvature (Contact point) 0 :=
      (holonomicGaugeCurvature_eq_of_connection_eq (Contact point)
        (fullyRecenterHolonomicConfiguration Base point)
        (contact_gaugeConnection_eq_recenter point) 0).symm

private theorem scalarCovariantDerivative_point_eq (point : BasePoint) :
    holonomicScalarCovariantDerivative Output point =
      holonomicScalarCovariantDerivative (Contact point) 0 := by
  calc
    holonomicScalarCovariantDerivative Output point =
        holonomicScalarCovariantDerivative Base point := by
      unfold holonomicScalarCovariantDerivative
      rw [output_scalar_eq_base, output_gaugeConnection_eq_base]
    _ = holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration Base point) 0 :=
      (fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
        Base point).symm
    _ = holonomicScalarCovariantDerivative (Contact point) 0 := by
      unfold holonomicScalarCovariantDerivative
      rw [show (Contact point).scalar =
          (fullyRecenterHolonomicConfiguration Base point).scalar by rfl]
      rw [contact_gaugeConnection_eq_recenter point]

private theorem p286GaugeAuxiliaryExterior_point_eq (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (Contact point) 0 := by
  calc
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output point =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Base point := by
      unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        p286GaugeAuxiliaryDirectionalDerivative
        holonomicP286GaugeConnectionCoordinate
        holonomicP286GaugeAuxiliaryCoordinate
      rw [output_gaugeConnection_eq_base, output_gaugeAuxiliary_eq_base]
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

/-- The exhaustive action-jet difference generated after both the emitted
global path and its occurrence-local native contact exist. -/
@[ext] structure GravityTailActionJetSeam where
  coframe : LorentzianCoframe
  gravityCurvature : PhysicalBivector
  gravityAuxiliary : PhysicalBivector
  gravitySimplicityMultiplier : PhysicalBivector
  matterCovariantDerivative :
    LorentzianIndex → DiracExteriorMatterCarrier
  gravityConnection : PointwiseLorentzSpinConnection
  gravityAuxiliaryExteriorCovariantDerivative : PhysicalBivectorThreeForm
  scalarDifferentialMomentumDivergence : ScalarCoordinateCarrier → ℝ
  matterDifferentialMomentumDivergence : MatterCoordinateCarrier → ℝ

instance : Zero GravityTailActionJetSeam where
  zero :=
    { coframe := 0
      gravityCurvature := 0
      gravityAuxiliary := 0
      gravitySimplicityMultiplier := 0
      matterCovariantDerivative := 0
      gravityConnection := 0
      gravityAuxiliaryExteriorCovariantDerivative := 0
      scalarDifferentialMomentumDivergence := 0
      matterDifferentialMomentumDivergence := 0 }

@[simp] theorem gravityTailActionJetSeam_zero_coframe :
    (0 : GravityTailActionJetSeam).coframe = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_gravityCurvature :
    (0 : GravityTailActionJetSeam).gravityCurvature = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_gravityAuxiliary :
    (0 : GravityTailActionJetSeam).gravityAuxiliary = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_gravitySimplicityMultiplier :
    (0 : GravityTailActionJetSeam).gravitySimplicityMultiplier = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_matterCovariantDerivative :
    (0 : GravityTailActionJetSeam).matterCovariantDerivative = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_gravityConnection :
    (0 : GravityTailActionJetSeam).gravityConnection = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_gravityAuxiliaryExterior :
    (0 : GravityTailActionJetSeam
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_scalarDivergence :
    (0 : GravityTailActionJetSeam
      ).scalarDifferentialMomentumDivergence = 0 := rfl

@[simp] theorem gravityTailActionJetSeam_zero_matterDivergence :
    (0 : GravityTailActionJetSeam
      ).matterDifferentialMomentumDivergence = 0 := rfl

/-- Subtract two already generated action jets in exactly the coordinates
that the joint coframe/connection occurrence can change. -/
def gravityTailActionJetSeam
    (outputJet contactJet : DiracDualFormNativePointwiseActionJetCarrier) :
    GravityTailActionJetSeam :=
  { coframe := outputJet.pointField.coframe - contactJet.pointField.coframe
    gravityCurvature :=
      outputJet.pointField.gravityCurvature -
        contactJet.pointField.gravityCurvature
    gravityAuxiliary :=
      outputJet.pointField.gravityAuxiliary -
        contactJet.pointField.gravityAuxiliary
    gravitySimplicityMultiplier :=
      outputJet.pointField.gravitySimplicityMultiplier -
        contactJet.pointField.gravitySimplicityMultiplier
    matterCovariantDerivative :=
      outputJet.pointField.matterCovariantDerivative -
        contactJet.pointField.matterCovariantDerivative
    gravityConnection :=
      outputJet.gravityConnection - contactJet.gravityConnection
    gravityAuxiliaryExteriorCovariantDerivative :=
      outputJet.gravityAuxiliaryExteriorCovariantDerivative -
        contactJet.gravityAuxiliaryExteriorCovariantDerivative
    scalarDifferentialMomentumDivergence :=
      outputJet.scalarDifferentialMomentumDivergence -
        contactJet.scalarDifferentialMomentumDivergence
    matterDifferentialMomentumDivergence :=
      outputJet.matterDifferentialMomentumDivergence -
        contactJet.matterDifferentialMomentumDivergence }

/-- Reinstall an already generated seam on its exact local contact.  This is
a readout reconstruction, not a physical writer. -/
def pointwiseActionJetWithGravityTailSeam
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (seam : GravityTailActionJetSeam) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  { contactJet with
    pointField :=
      { contactJet.pointField with
        coframe := seam.coframe + contactJet.pointField.coframe
        gravityCurvature :=
          seam.gravityCurvature + contactJet.pointField.gravityCurvature
        gravityAuxiliary :=
          seam.gravityAuxiliary + contactJet.pointField.gravityAuxiliary
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

@[simp] theorem pointwiseActionJetWithGravityTailSeam_zero
    (contactJet : DiracDualFormNativePointwiseActionJetCarrier) :
    pointwiseActionJetWithGravityTailSeam contactJet 0 = contactJet := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext <;>
      simp [pointwiseActionJetWithGravityTailSeam]
  all_goals simp [pointwiseActionJetWithGravityTailSeam]

private def OutputJet (point : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet Source Output point

private def ContactJet (point : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet Source (Contact point) 0

def fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam
    (point : BasePoint) : GravityTailActionJetSeam :=
  gravityTailActionJetSeam (OutputJet point) (ContactJet point)

/-- Value-level coframe defect generated by the emitted radial path against
the exact endpoint of the same occurrence-native profile. -/
def fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect
    (point : BasePoint) : LorentzianCoframe :=
  cartanECSynchronizedGravityTailCoframePathField Source Current point -
    Base.coframe point

/-- Value-level connection defect generated by the emitted radial path
against the matching local native contact. -/
def fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
    (point : BasePoint) : PointwiseLorentzSpinConnection :=
  cartanECSynchronizedGravityTailPathConnectionField Source Current point -
    (Contact point).gravityConnection 0

private theorem base_curvature_eq_normalizedAffine
    (point : BasePoint) :
    holonomicGravityCurvature Base point =
      holonomicGravityCurvature
        (normalizedAffineConfiguration OriginConnection OriginTarget) point := by
  apply holonomicGravityCurvature_eq_of_connection_firstGermAt
  · intro formDirection internalOut internalIn
    rw [
      fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]
    rfl
  · intro derivativeDirection formDirection internalOut internalIn
    unfold gravityConnectionDerivative
    have componentEq :
        (fun candidate =>
          Base.gravityConnection candidate formDirection internalOut internalIn) =
          fun candidate =>
            (normalizedAffineConfiguration OriginConnection OriginTarget
              ).gravityConnection candidate formDirection internalOut internalIn := by
      funext candidate
      rw [
        fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]
      rfl
    rw [componentEq]

private theorem base_curvature_eq_originTarget_add_bracketDrift
    (point : BasePoint) :
    holonomicGravityCurvature Base point =
      OriginTarget - originLorentzBracketCurvature OriginConnection +
        originLorentzBracketCurvature (Base.gravityConnection point) := by
  rw [base_curvature_eq_normalizedAffine,
    holonomicGravityCurvature_normalizedAffineConfiguration_at,
    fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]

private theorem baseContactTarget_eq_curvature_iff_coframeECBalance
    (contact : BasePoint) :
    diracDualFormNativeCoframeECContactCurvatureTarget Source Base contact =
        holonomicGravityCurvature Base contact ↔
      coframeDiracDualECCurvatureObservation
          (Base.coframe contact)
          (holonomicGravityCurvature Base contact) +
        diracDualFormNativeCoframeECContactLoad Source Base contact = 0 := by
  have nondegenerate : Matrix.det (Base.coframe contact) ≠ 0 := by
    rw [fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    norm_num
  constructor
  · intro targetEq
    have observed := congrArg
      (coframeDiracDualECCurvatureObservation (Base.coframe contact)) targetEq
    unfold diracDualFormNativeCoframeECContactCurvatureTarget at observed
    rw [coframeDiracDualECCurvatureObservation_target
      (Base.coframe contact) nondegenerate] at observed
    change
      -diracDualFormNativeCoframeECContactLoad Source Base contact =
        coframeDiracDualECCurvatureObservation
          (Base.coframe contact)
          (holonomicGravityCurvature Base contact) at observed
    rw [← observed]
    abel
  · intro balance
    unfold diracDualFormNativeCoframeECContactCurvatureTarget
      coframeDiracDualECCurvatureTarget
      coframeDiracDualECCurvatureKernelPart
    change
      holonomicGravityCurvature Base contact -
          coframeDiracDualECCurvatureNormalSection (Base.coframe contact)
            (coframeDiracDualECCurvatureObservation
              (Base.coframe contact)
              (holonomicGravityCurvature Base contact)) +
        coframeDiracDualECCurvatureNormalSection (Base.coframe contact)
          (-diracDualFormNativeCoframeECContactLoad Source Base contact) =
        holonomicGravityCurvature Base contact
    have observedEq :
        coframeDiracDualECCurvatureObservation
            (Base.coframe contact)
            (holonomicGravityCurvature Base contact) =
          -diracDualFormNativeCoframeECContactLoad Source Base contact :=
      eq_neg_of_add_eq_zero_left balance
    rw [observedEq]
    abel

/-- The typed connection-profile drift is zero exactly when the generated
gravity base itself satisfies the source-native EC coframe equation at that
point.  This is an all-point residual normal form, not a zero premise for the
writer. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift_zero_iff_baseCoframeECBalance
    (contact : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
          contact = 0 ↔
      coframeDiracDualECCurvatureObservation
          (Base.coframe contact)
          (holonomicGravityCurvature Base contact) +
        diracDualFormNativeCoframeECContactLoad Source Base contact = 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift_zero_iff_target_eq_originTarget_add_bracketDrift,
    fixedP506L0CartanECConstraintCauchyGravityTailProfileTarget_eq_baseContactTarget,
    cartanECSynchronizedGravityTailProfileOrigin_eq_base,
    ← base_curvature_eq_originTarget_add_bracketDrift,
    baseContactTarget_eq_curvature_iff_coframeECBalance]

/-- The two value-level primitive factors vanish exactly when the radial
increments emitted by the same source/current occurrence realize the
coframe and connection displacement of its generated gravity base.  This
is a producer-facing potential equation, not a supplied target or a zero
receipt. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailValueDefects_zero_iff_radialPotentialRealization
    (point : BasePoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        0 ∧
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
        point = 0) ↔
      (cartanECSynchronizedGravityTailCoframeRadialIncrement
          Source Current point = Base.coframe point - Base.coframe 0 ∧
        lorentzSkewConnectionOfBivectorOneForm
            (cartanECSynchronizedGravityTailRadialIncrement
              Source Current point) =
          Base.gravityConnection point - Base.gravityConnection 0) := by
  have coframeNormalForm :
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect point =
        cartanECSynchronizedGravityTailCoframeRadialIncrement
            Source Current point -
          (Base.coframe point - Base.coframe 0) := by
    unfold fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect
      cartanECSynchronizedGravityTailCoframePathField
      cartanECSynchronizedGravityTailCoframePathAnchor
    abel
  have connectionNormalForm :
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
          point =
        lorentzSkewConnectionOfBivectorOneForm
            (cartanECSynchronizedGravityTailRadialIncrement
              Source Current point) -
          (Base.gravityConnection point - Base.gravityConnection 0) := by
    unfold fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
      cartanECSynchronizedGravityTailPathConnectionField
      cartanECSynchronizedGravityTailPathAnchor
    rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm,
      normalizedAffineLorentzConnectionField_zero,
      cartanECSynchronizedGravityTailProfileOrigin_eq_base]
    abel
  rw [coframeNormalForm, connectionNormalForm, sub_eq_zero, sub_eq_zero]

/-- The coframe coordinate of the whole-action seam is exactly the generated
coframe value defect. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_eq_valueDefect
    (point : BasePoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).coframe =
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect
        point := by
  unfold fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam
    gravityTailActionJetSeam
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect
  change
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.coframe
          point -
        (cartanECSynchronizedGravityTailProfileContact
          Source Current point).coframe 0 =
      cartanECSynchronizedGravityTailCoframePathField Source Current point -
        Base.coframe point
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe]
  unfold cartanECSynchronizedGravityTailProfileContact
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  exact congrArg (fun coframe =>
    cartanECSynchronizedGravityTailCoframePathField Source Current point - coframe)
    (fullyRecenterHolonomicConfiguration_coframe_origin Base point)

/-- The actual gravity-tail seam has no coframe value defect anywhere on the
initial Cauchy slice.  This consumes the fixed source/current radial
realization directly; no zero equation or settlement receipt is supplied. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam
      (canonicalCauchySlicePoint 0 space)).coframe = 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_coframe_eq_valueDefect]
  unfold fixedP506L0CartanECConstraintCauchyGravityTailCoframeValueDefect
    cartanECSynchronizedGravityTailCoframePathField
    cartanECSynchronizedGravityTailCoframePathAnchor
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialIncrement_zeroSlice,
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
  simp

/-- The connection coordinate of the whole-action seam is exactly the
generated connection value defect. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityConnection_eq_valueDefect
    (point : BasePoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityConnection =
      fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
        point := by
  unfold fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam
    gravityTailActionJetSeam
    fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
  change
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.gravityConnection
          point -
        (cartanECSynchronizedGravityTailProfileContact
          Source Current point).gravityConnection 0 = _
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection]

/-- Independent whole-action consumer of the fixed connection producer.  The
gravity-connection coordinate of the emitted occurrence is exactly the skew
image of its source-native profile-jet drift along the same radial path; the
normalized-affine geometric part has already cancelled. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityConnection_eq_profileLorentzJetDrift
    (point : BasePoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityConnection =
      lorentzSkewConnectionOfBivectorOneForm
        (fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
          point) := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityConnection_eq_valueDefect]
  unfold fixedP506L0CartanECConstraintCauchyGravityTailConnectionValueDefect
    cartanECSynchronizedGravityTailPathConnectionField
    cartanECSynchronizedGravityTailPathAnchor
  rw [cartanECSynchronizedGravityTailProfileContact_connection_normalForm,
    normalizedAffineLorentzConnectionField_zero,
    cartanECSynchronizedGravityTailProfileOrigin_eq_base]
  rw [show
      Base.gravityConnection 0 +
            lorentzSkewConnectionOfBivectorOneForm
              (cartanECSynchronizedGravityTailRadialIncrement
                Source Current point) -
          Base.gravityConnection point =
        lorentzSkewConnectionOfBivectorOneForm
              (cartanECSynchronizedGravityTailRadialIncrement
                Source Current point) -
          (Base.gravityConnection point - Base.gravityConnection 0) by
    abel]
  exact
    fixedP506L0CartanECConstraintCauchyGravityTailRadialConnectionDisplacementDefect_eq_profileLorentzJetDrift
      point

/-- Whole-carrier readout after the output and local contact already exist. -/
def fixedP506L0CartanECConstraintCauchyGravityTailActionJetNormalForm
    (point : BasePoint) : DiracDualFormNativePointwiseActionJetCarrier :=
  pointwiseActionJetWithGravityTailSeam (ContactJet point)
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point)

theorem pointwiseActionJetWithGravityTailSeam_reconstruct
    (outputJet contactJet : DiracDualFormNativePointwiseActionJetCarrier)
    (gaugeCurvature : outputJet.pointField.gaugeCurvature =
      contactJet.pointField.gaugeCurvature)
    (gaugeAuxiliary : outputJet.pointField.gaugeAuxiliary =
      contactJet.pointField.gaugeAuxiliary)
    (scalar : outputJet.pointField.scalar = contactJet.pointField.scalar)
    (scalarCovariantDerivative :
      outputJet.pointField.scalarCovariantDerivative =
        contactJet.pointField.scalarCovariantDerivative)
    (matter : outputJet.pointField.matter = contactJet.pointField.matter)
    (conjugateMatter : outputJet.pointField.conjugateMatter =
      contactJet.pointField.conjugateMatter)
    (p286GaugeConnection : outputJet.p286GaugeConnection =
      contactJet.p286GaugeConnection)
    (p286GaugeAuxiliaryExterior :
      outputJet.p286GaugeAuxiliaryExteriorCovariantDerivative =
        contactJet.p286GaugeAuxiliaryExteriorCovariantDerivative) :
    outputJet = pointwiseActionJetWithGravityTailSeam contactJet
      (gravityTailActionJetSeam outputJet contactJet) := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · simp [pointwiseActionJetWithGravityTailSeam,
        gravityTailActionJetSeam]
    · simp [pointwiseActionJetWithGravityTailSeam,
        gravityTailActionJetSeam]
    · simp [pointwiseActionJetWithGravityTailSeam,
        gravityTailActionJetSeam]
    · simp [pointwiseActionJetWithGravityTailSeam,
        gravityTailActionJetSeam]
    · exact gaugeCurvature
    · exact gaugeAuxiliary
    · exact scalar
    · exact scalarCovariantDerivative
    · exact matter
    · simp [pointwiseActionJetWithGravityTailSeam,
        gravityTailActionJetSeam]
    · exact conjugateMatter
  · simp [pointwiseActionJetWithGravityTailSeam,
      gravityTailActionJetSeam]
  · exact p286GaugeConnection
  · simp [pointwiseActionJetWithGravityTailSeam,
      gravityTailActionJetSeam]
  · exact p286GaugeAuxiliaryExterior
  · simp [pointwiseActionJetWithGravityTailSeam,
      gravityTailActionJetSeam]
  · simp [pointwiseActionJetWithGravityTailSeam,
      gravityTailActionJetSeam]

/-- Every source-generated gravity-tail output admits an exact whole-carrier
reconstruction from its dependent seam and matching occurrence-local contact.
The seam is not supplied by the caller: both it and the contact are read from
the same `source/current` occurrence after the output has been generated. -/
theorem sourceActionGeneratedGravityTail_actionJet_naturality
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
          source current) point =
      pointwiseActionJetWithGravityTailSeam
        (generatedDiracDualFormNativePointwiseActionJet source
          (cartanECSynchronizedGravityTailProfileContact
            source current point) 0)
        (gravityTailActionJetSeam
          (generatedDiracDualFormNativePointwiseActionJet source
            (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
              source current) point)
          (generatedDiracDualFormNativePointwiseActionJet source
            (cartanECSynchronizedGravityTailProfileContact
              source current point) 0)) := by
  let Base := cartanECSynchronizedGravityTailBase source current
  let Output :=
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
      source current
  let Contact :=
    cartanECSynchronizedGravityTailProfileContact source current point
  have baseGaugeConnection : Base.gaugeConnection = current.gaugeConnection := by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
        source current 0
  have baseGaugeAuxiliary : Base.gaugeAuxiliary = current.gaugeAuxiliary := by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
        source current 0
  have baseScalar : Base.scalar = current.scalar := by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_scalar
        source current 0
  have baseMatter : Base.matter = current.matter := by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_matter
        source current 0
  have baseConjugateMatter : Base.conjugateMatter = current.conjugateMatter := by
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
        source current 0
  have outputGaugeConnection : Output.gaugeConnection = Base.gaugeConnection := by
    calc
      Output.gaugeConnection = current.gaugeConnection := by
        exact
          sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeConnection
            source current
      _ = Base.gaugeConnection := baseGaugeConnection.symm
  have outputGaugeAuxiliary : Output.gaugeAuxiliary = Base.gaugeAuxiliary := by
    calc
      Output.gaugeAuxiliary = current.gaugeAuxiliary := by
        exact
          sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gaugeAuxiliary
            source current
      _ = Base.gaugeAuxiliary := baseGaugeAuxiliary.symm
  have outputScalar : Output.scalar = Base.scalar := by
    calc
      Output.scalar = current.scalar := by
        exact
          sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_scalar
            source current
      _ = Base.scalar := baseScalar.symm
  have outputMatter : Output.matter = Base.matter := by
    calc
      Output.matter = current.matter := by
        exact
          sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_matter
            source current
      _ = Base.matter := baseMatter.symm
  have outputConjugateMatter : Output.conjugateMatter = Base.conjugateMatter := by
    calc
      Output.conjugateMatter = current.conjugateMatter := by
        exact
          sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_conjugateMatter
            source current
      _ = Base.conjugateMatter := baseConjugateMatter.symm
  have contactGaugeConnection :
      Contact.gaugeConnection =
        (fullyRecenterHolonomicConfiguration Base point).gaugeConnection := by
    dsimp [Contact, Base]
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
        source
        (fullyRecenterHolonomicConfiguration
          (cartanECSynchronizedGravityTailBase source current) point) 0
  have contactGaugeAuxiliary :
      Contact.gaugeAuxiliary =
        (fullyRecenterHolonomicConfiguration Base point).gaugeAuxiliary := by
    dsimp [Contact, Base]
    exact
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
        source
        (fullyRecenterHolonomicConfiguration
          (cartanECSynchronizedGravityTailBase source current) point) 0
  have gaugeConnectionAt :
      Output.gaugeConnection point = Contact.gaugeConnection 0 := by
    calc
      Output.gaugeConnection point = Base.gaugeConnection point :=
        congrFun outputGaugeConnection point
      _ = (fullyRecenterHolonomicConfiguration Base point).gaugeConnection 0 :=
        (fullyRecenterHolonomicConfiguration_gaugeConnection_origin Base point).symm
      _ = Contact.gaugeConnection 0 :=
        (congrFun contactGaugeConnection 0).symm
  have gaugeAuxiliaryAt :
      Output.gaugeAuxiliary point = Contact.gaugeAuxiliary 0 := by
    calc
      Output.gaugeAuxiliary point = Base.gaugeAuxiliary point :=
        congrFun outputGaugeAuxiliary point
      _ = (fullyRecenterHolonomicConfiguration Base point).gaugeAuxiliary 0 :=
        (fullyRecenterHolonomicConfiguration_gaugeAuxiliary_origin Base point).symm
      _ = Contact.gaugeAuxiliary 0 :=
        (congrFun contactGaugeAuxiliary 0).symm
  have scalarAt : Output.scalar point = Contact.scalar 0 := by
    calc
      Output.scalar point = Base.scalar point := congrFun outputScalar point
      _ = (fullyRecenterHolonomicConfiguration Base point).scalar 0 :=
        (fullyRecenterHolonomicConfiguration_scalar_origin Base point).symm
      _ = Contact.scalar 0 := by rfl
  have matterAt : Output.matter point = Contact.matter 0 := by
    calc
      Output.matter point = Base.matter point := congrFun outputMatter point
      _ = (fullyRecenterHolonomicConfiguration Base point).matter 0 :=
        (fullyRecenterHolonomicConfiguration_matter_origin Base point).symm
      _ = Contact.matter 0 := by rfl
  have conjugateMatterAt :
      Output.conjugateMatter point = Contact.conjugateMatter 0 := by
    calc
      Output.conjugateMatter point = Base.conjugateMatter point :=
        congrFun outputConjugateMatter point
      _ = (fullyRecenterHolonomicConfiguration Base point).conjugateMatter 0 :=
        (fullyRecenterHolonomicConfiguration_conjugateMatter_origin Base point).symm
      _ = Contact.conjugateMatter 0 := by rfl
  have gaugeCurvatureAt :
      holonomicGaugeCurvature Output point =
        holonomicGaugeCurvature Contact 0 := by
    calc
      holonomicGaugeCurvature Output point =
          holonomicGaugeCurvature Base point :=
        holonomicGaugeCurvature_eq_of_connection_eq Output Base
          outputGaugeConnection point
      _ = holonomicGaugeCurvature
          (fullyRecenterHolonomicConfiguration Base point) 0 :=
        (fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
          Base point).symm
      _ = holonomicGaugeCurvature Contact 0 :=
        (holonomicGaugeCurvature_eq_of_connection_eq Contact
          (fullyRecenterHolonomicConfiguration Base point)
          contactGaugeConnection 0).symm
  have scalarCovariantDerivativeAt :
      holonomicScalarCovariantDerivative Output point =
        holonomicScalarCovariantDerivative Contact 0 := by
    calc
      holonomicScalarCovariantDerivative Output point =
          holonomicScalarCovariantDerivative Base point := by
        unfold holonomicScalarCovariantDerivative
        rw [outputScalar, outputGaugeConnection]
      _ = holonomicScalarCovariantDerivative
          (fullyRecenterHolonomicConfiguration Base point) 0 :=
        (fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
          Base point).symm
      _ = holonomicScalarCovariantDerivative Contact 0 := by
        unfold holonomicScalarCovariantDerivative
        rw [show Contact.scalar =
            (fullyRecenterHolonomicConfiguration Base point).scalar by rfl]
        rw [contactGaugeConnection]
  have p286GaugeAuxiliaryExteriorAt :
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output point =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Contact 0 := by
    calc
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output point =
          holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Base point := by
        unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          p286GaugeAuxiliaryDirectionalDerivative
          holonomicP286GaugeConnectionCoordinate
          holonomicP286GaugeAuxiliaryCoordinate
        rw [outputGaugeConnection, outputGaugeAuxiliary]
      _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (fullyRecenterHolonomicConfiguration Base point) 0 :=
        (fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
          Base point).symm
      _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Contact 0 := by
        unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          p286GaugeAuxiliaryDirectionalDerivative
          holonomicP286GaugeConnectionCoordinate
          holonomicP286GaugeAuxiliaryCoordinate
        rw [contactGaugeConnection, contactGaugeAuxiliary]
  change
    generatedDiracDualFormNativePointwiseActionJet source Output point =
      pointwiseActionJetWithGravityTailSeam
        (generatedDiracDualFormNativePointwiseActionJet source Contact 0)
        (gravityTailActionJetSeam
          (generatedDiracDualFormNativePointwiseActionJet source Output point)
          (generatedDiracDualFormNativePointwiseActionJet source Contact 0))
  apply pointwiseActionJetWithGravityTailSeam_reconstruct
  · exact gaugeCurvatureAt
  · exact gaugeAuxiliaryAt
  · exact scalarAt
  · exact scalarCovariantDerivativeAt
  · exact matterAt
  · exact conjugateMatterAt
  · exact gaugeConnectionAt
  · exact p286GaugeAuxiliaryExteriorAt

theorem fixedP506L0CartanECConstraintCauchyGravityTail_actionJet_naturality
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet Source Output point =
      fixedP506L0CartanECConstraintCauchyGravityTailActionJetNormalForm point := by
  change OutputJet point =
    pointwiseActionJetWithGravityTailSeam (ContactJet point)
      (gravityTailActionJetSeam (OutputJet point) (ContactJet point))
  apply pointwiseActionJetWithGravityTailSeam_reconstruct
  · change holonomicGaugeCurvature Output point =
      holonomicGaugeCurvature (Contact point) 0
    exact gaugeCurvature_point_eq point
  · change Output.gaugeAuxiliary point = (Contact point).gaugeAuxiliary 0
    exact gaugeAuxiliary_point_eq point
  · change Output.scalar point = (Contact point).scalar 0
    exact scalar_point_eq point
  · change holonomicScalarCovariantDerivative Output point =
      holonomicScalarCovariantDerivative (Contact point) 0
    exact scalarCovariantDerivative_point_eq point
  · change Output.matter point = (Contact point).matter 0
    exact matter_point_eq point
  · change Output.conjugateMatter point = (Contact point).conjugateMatter 0
    exact conjugateMatter_point_eq point
  · change Output.gaugeConnection point = (Contact point).gaugeConnection 0
    exact gaugeConnection_point_eq point
  · change
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output point =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (Contact point) 0
    exact p286GaugeAuxiliaryExterior_point_eq point

/-- The curvature coordinate of the exhaustive action-jet seam is exactly
the generated radial integrability factor, not an additional premise. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityCurvature_eq_integrabilityFactor
    (point : BasePoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityCurvature =
      fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor
        point := by
  change
    holonomicGravityCurvature Output point -
        holonomicGravityCurvature (Contact point) 0 = _
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTail_gravityCurvature_eq_target_add_integrabilityFactor,
    fixedP506L0CartanECConstraintCauchyGravityTailProfileContact_curvature_eq_target]
  abel

/-- The independent whole-action curvature consumer now reads the same typed
connection drift as the value seam.  Its only additional term is the
source-generated transverse exactification defect. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityCurvature_eq_profileLorentzJetDriftBracket_add_transverseDefect
    (point : BasePoint) :
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point
      ).gravityCurvature =
      (originLorentzBracketCurvature
          (Base.gravityConnection point +
            lorentzSkewConnectionOfBivectorOneForm
              (fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
                point)) -
        originLorentzBracketCurvature (Base.gravityConnection point)) +
      fixedP506L0CartanECConstraintCauchyGravityTailTransverseCurvatureDefect
        point := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_gravityCurvature_eq_integrabilityFactor,
    fixedP506L0CartanECConstraintCauchyGravityTailCurvatureIntegrabilityFactor_eq_profileLorentzJetDriftBracket_add_transverseDefect]

/-- Exact equality criterion for the emitted whole action jet and its local
native contact.  No equality field is supplied to either producer. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam_zero_iff_actionJet_eq_contact
    (point : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam point = 0 ↔
      OutputJet point = ContactJet point := by
  constructor
  · intro seamZero
    have naturality :=
      fixedP506L0CartanECConstraintCauchyGravityTail_actionJet_naturality point
    change OutputJet point =
      fixedP506L0CartanECConstraintCauchyGravityTailActionJetNormalForm point
      at naturality
    rw [fixedP506L0CartanECConstraintCauchyGravityTailActionJetNormalForm,
      seamZero, pointwiseActionJetWithGravityTailSeam_zero] at naturality
    exact naturality
  · intro actionJetEq
    unfold fixedP506L0CartanECConstraintCauchyGravityTailActionJetSeam
      gravityTailActionJetSeam
    rw [actionJetEq]
    apply GravityTailActionJetSeam.ext <;> simp

def fixedP506L0CartanECConstraintCauchyGravityTailPointwiseResidualNormalForm
    (point : BasePoint) : DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualOfActionJet Source point
    (fixedP506L0CartanECConstraintCauchyGravityTailActionJetNormalForm point)

theorem fixedP506L0CartanECConstraintCauchyGravityTail_residual_normalForm
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual Source Output point =
      fixedP506L0CartanECConstraintCauchyGravityTailPointwiseResidualNormalForm point := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    fixedP506L0CartanECConstraintCauchyGravityTail_actionJet_naturality]
  rfl

theorem fixedP506L0CartanECConstraintCauchyGravityTail_zeroFiber_iff_normalForm_zero :
    DiracDualFormNativeJointZeroFiber Source Output ↔
      ∀ point,
        fixedP506L0CartanECConstraintCauchyGravityTailPointwiseResidualNormalForm
          point = 0 := by
  rw [diracDualFormNativeJointZeroFiber_iff_pointwise]
  unfold OnDiracDualFormNativePointwiseJointZeroFiber
  constructor
  · intro zero point
    rw [← fixedP506L0CartanECConstraintCauchyGravityTail_residual_normalForm]
    exact zero point
  · intro zero point
    rw [fixedP506L0CartanECConstraintCauchyGravityTail_residual_normalForm]
    exact zero point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm
