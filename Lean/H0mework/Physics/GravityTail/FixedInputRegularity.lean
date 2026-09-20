import H0mework.Physics.SynchronizedJoint.FixedCartanECSynchronizedGravityTailLorentzPath
import H0mework.Physics.QuarticDynamics.FixedConstitutiveRegularity
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity

/-!
# Fixed action-selected gravity-tail input regularity

This module proves the missing whole-spacetime regularity of the exact
non-gravity current consumed by the gravity-only tail.  The live P286
auxiliary is differentiated through its source/action-generated radial
connection and branch-free constitutive formula.  It is not replaced by a
regularity proxy and no output certificate is supplied to the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailInputRegularity

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorScalarReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveRegularity
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286RadialQuarticActionPrincipal
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open DiracExteriorMatterAction
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

attribute [local instance] actionSelectedMatterBasePointNormedAddCommGroup
attribute [local instance] actionSelectedMatterBasePointNormedSpace

local instance inputRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance inputRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance inputRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source Input

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev OldRadial : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConnectionActual

private abbrev OldConstitutive : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConstitutiveActual

private abbrev Radial : StageNineHolonomicConfiguration :=
  completeJointActionSelectedRadialConnectionActual Source Current

private abbrev Constitutive : StageNineHolonomicConfiguration :=
  completeJointActionSelectedRadialConstitutiveActual Source Current

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev GravityBase : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Coupled

private theorem algebraic_gaugeConnection_eq_input :
    Algebraic.gaugeConnection = Input.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source
        (completeJointGlobalTemporalCurrent Source Input) 0 by
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem current_gaugeConnection_eq_u6 :
    Current.gaugeConnection = U6.gaugeConnection := by
  calc
    Current.gaugeConnection = Input.gaugeConnection :=
      final_gaugeConnection_eq_input
    _ = Algebraic.gaugeConnection :=
      algebraic_gaugeConnection_eq_input.symm
    _ = U6.gaugeConnection :=
      fixedP506L0U6_gaugeConnection_eq_algebraic.symm

private theorem radial_gaugeConnection_eq_old :
    Radial.gaugeConnection = OldRadial.gaugeConnection := by
  unfold Radial completeJointActionSelectedRadialConnectionActual
    completeJointActionSelectedRadialConnection
    OldRadial fixedP506L0U6RadialQuarticConnectionActual
  have chargeEq :
      completeJointActionSelectedRadialCharge Source Current =
        fixedP506L0U6OccurrenceP286MotherActionCharge :=
    fixedP506L0LorentzPathActionSelectedRadialCharge_eq_motherActionCharge
  rw [chargeEq]
  change
    (varyP286GaugeConnectionCoordinate Current
      (p286RadialQuarticTemporalConnection
        fixedP506L0U6OccurrenceP286MotherActionCharge) 1).gaugeConnection =
    (varyP286GaugeConnectionCoordinate U6
      (p286RadialQuarticTemporalConnection
        fixedP506L0U6OccurrenceP286MotherActionCharge) 1).gaugeConnection
  funext point direction
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeConnectionCoordinate
        (varyP286GaugeConnectionCoordinate Current
          (p286RadialQuarticTemporalConnection
            fixedP506L0U6OccurrenceP286MotherActionCharge) 1)
        point direction =
      holonomicP286GaugeConnectionCoordinate
        (varyP286GaugeConnectionCoordinate U6
          (p286RadialQuarticTemporalConnection
            fixedP506L0U6OccurrenceP286MotherActionCharge) 1)
        point direction
  rw [holonomicP286GaugeConnectionCoordinate_vary,
    holonomicP286GaugeConnectionCoordinate_vary]
  simp only [one_smul, Pi.add_apply]
  rw [show holonomicP286GaugeConnectionCoordinate Current point direction =
      holonomicP286GaugeConnectionCoordinate U6 point direction by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [current_gaugeConnection_eq_u6]]

private theorem radial_coframe_eq_one :
    Radial.coframe = fun _ => (1 : LorentzianCoframe) := by
  change Current.coframe = _
  exact
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one

private theorem radial_curvatureCoordinate_contDiff :
    ContDiff ℝ ∞ (holonomicP286GaugeCurvatureCoordinate Radial) := by
  have connectionEq :
      Radial.gaugeConnection = OldConstitutive.gaugeConnection := by
    simpa [OldConstitutive,
      fixedP506L0U6RadialQuarticConstitutiveActual,
      diracDualFormNativeConstitutiveWrittenCurrent] using
      radial_gaugeConnection_eq_old
  rw [show holonomicP286GaugeCurvatureCoordinate Radial =
      holonomicP286GaugeCurvatureCoordinate OldConstitutive by
    funext point pair
    change
      p286CoordinateEquiv (holonomicGaugeCurvature Radial point pair) =
        p286CoordinateEquiv
          (holonomicGaugeCurvature OldConstitutive point pair)
    rw [holonomicGaugeCurvature_eq_of_connection_eq
      Radial OldConstitutive connectionEq point]]
  exact
    fixedP506L0U6RadialQuarticConstitutiveActual_gaugeCurvatureCoordinate_contDiff

private theorem constitutive_auxiliaryCoordinate_eq_formula :
    holonomicP286GaugeAuxiliaryCoordinate Constitutive =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (Radial.coframe point)
          (holonomicP286GaugeCurvatureCoordinate Radial point) := by
  funext point pair
  unfold Constitutive completeJointActionSelectedRadialConstitutiveActual
    holonomicP286GaugeAuxiliaryCoordinate
    diracDualFormNativeConstitutiveWrittenCurrent
    diracDualFormNativeConstitutiveAuxiliaryField
  change
    (formNativeP286GaugeActualToCoordinateLinear
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Radial.coframe point)
        (holonomicGaugeCurvature Radial point))) pair = _
  unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
  rw [show holonomicP286GaugeCurvatureCoordinate Radial point =
      formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature Radial point) by rfl]
  rw [formNativeP286GaugeActual_coordinate_actual]

/-- The exact action-selected carry's live constitutive auxiliary is
globally smooth on the whole spacetime carrier. -/
theorem fixedP506L0ActionSelectedCarry_gaugeAuxiliaryCoordinate_contDiff :
    ∀ pair : Fin 6,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv (Carry.gaugeAuxiliary point pair) := by
  intro pair
  change ContDiff ℝ ∞ fun point =>
    holonomicP286GaugeAuxiliaryCoordinate Constitutive point pair
  rw [show
    (fun point =>
      holonomicP286GaugeAuxiliaryCoordinate Constitutive point pair) =
      fun point =>
        (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (Radial.coframe point)
          (holonomicP286GaugeCurvatureCoordinate Radial point)) pair by
    funext point
    rw [congrFun constitutive_auxiliaryCoordinate_eq_formula point]]
  rw [contDiff_iff_contDiffAt]
  intro point
  have nondegenerate : Matrix.det (Radial.coframe point) ≠ 0 := by
    rw [radial_coframe_eq_one]
    norm_num
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings Source)
      (Radial.coframe point) nondegenerate
      (holonomicP286GaugeCurvatureCoordinate Radial point)
  have outerOne : ContDiffAt ℝ ∞
      (fun joint :
          LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source) joint.1 joint.2)
      (Radial.coframe point,
        holonomicP286GaugeCurvatureCoordinate Radial point) :=
    outer
  let outputAtPair :
      (LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) →
        P286CoordinateCarrier :=
    fun joint =>
      (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings Source) joint.1 joint.2) pair
  have outerPair : ContDiffAt ℝ ∞
      outputAtPair
      (Radial.coframe point,
        holonomicP286GaugeCurvatureCoordinate Radial point) :=
    (contDiffAt_pi.mp outerOne pair : _)
  have coframeRegular : ContDiffAt ℝ ∞ Radial.coframe point := by
    rw [radial_coframe_eq_one]
    exact contDiff_const.contDiffAt
  let innerFunction : BasePoint →
      LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm :=
    fun candidate =>
      (Radial.coframe candidate,
        holonomicP286GaugeCurvatureCoordinate Radial candidate)
  have inner : ContDiffAt ℝ ∞ innerFunction point :=
    coframeRegular.prodMk
      radial_curvatureCoordinate_contDiff.contDiffAt
  have composed := ContDiffAt.comp
    (g := outputAtPair) (f := innerFunction) point outerPair inner
  simpa [outputAtPair, innerFunction, Function.comp_def] using composed

/-! ## The exact synchronized gravity prefix is globally smooth -/

private theorem gravityBase_coframe_contDiff :
    ContDiff ℝ ∞ GravityBase.coframe := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
      Source Coupled 0

private theorem gravityBase_connection_component_contDiff
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      GravityBase.gravityConnection point direction internalOut internalIn := by
  change ContDiff ℝ ∞ fun point =>
    coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
        _ _ point direction internalOut internalIn
  simpa [coframeECContactCenteredNormalizedAffineLorentzConnectionField] using
    normalizedAffineLorentzConnectionField_smooth _ _
      direction internalOut internalIn

private theorem gravityBase_auxiliary_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      GravityBase.gravityAuxiliary point internalPair spacetimePair := by
  have auxiliarySmooth : ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector (GravityBase.coframe point) :=
    physicalIIPlusBivector_contDiff.comp gravityBase_coframe_contDiff
  change ContDiff ℝ ∞ fun point =>
    physicalIIPlusBivector (GravityBase.coframe point)
      internalPair spacetimePair
  exact contDiff_pi.mp (contDiff_pi.mp auxiliarySmooth internalPair)
    spacetimePair

private theorem gravityConnectionDerivative_contDiff_of_components
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction internalOut internalIn)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      gravityConnectionDerivative configuration point derivativeDirection
        formDirection internalOut internalIn := by
  let connectionCoordinate : BasePoint → ℝ := fun point =>
    configuration.gravityConnection point formDirection internalOut internalIn
  have coordinateSmooth : ContDiff ℝ ∞ connectionCoordinate :=
    connectionSmooth formDirection internalOut internalIn
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => connectionCoordinate)) :=
    coordinateSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ connectionCoordinate point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  unfold gravityConnectionDerivative
  change ContDiff ℝ ∞ fun point =>
    fderiv ℝ connectionCoordinate point
      (coordinateDirection derivativeDirection)
  exact derivativeSmooth.clm_apply contDiff_const

private theorem gravityCurvature_component_contDiff_of_components
    (configuration : StageNineHolonomicConfiguration)
    (connectionSmooth : ∀ direction internalOut internalIn,
      ContDiff ℝ ∞ fun point =>
        configuration.gravityConnection point direction internalOut internalIn)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      holonomicGravityCurvature configuration point
        internalPair spacetimePair := by
  unfold holonomicGravityCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact gravityConnectionDerivative_contDiff_of_components
        configuration connectionSmooth
        (pairFirst spacetimePair) (pairSecond spacetimePair)
        (pairFirst internalPair) (pairSecond internalPair)
    · exact gravityConnectionDerivative_contDiff_of_components
        configuration connectionSmooth
        (pairSecond spacetimePair) (pairFirst spacetimePair)
        (pairFirst internalPair) (pairSecond internalPair)
  · apply ContDiff.sum
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

private theorem gravityBase_multiplier_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      GravityBase.gravitySimplicityMultiplier point
        internalPair spacetimePair := by
  let prepared :=
    diracDualFormNativeCartanECSynchronizedCoframePreparedActual
      Source Coupled 0
  change ContDiff ℝ ∞ fun point =>
    formNativeGravityReactionField prepared point
      internalPair spacetimePair
  unfold formNativeGravityReactionField
  have dualSmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (prepared.gravityAuxiliary point) := by
    change ContDiff ℝ ∞ fun point =>
      gravityInternalDualLinear (prepared.gravityAuxiliary point)
    apply gravityInternalDualLinear.toContinuousLinearMap.contDiff.comp
    apply contDiff_pi'
    intro first
    apply contDiff_pi'
    intro second
    exact gravityBase_auxiliary_component_contDiff first second
  have curvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature prepared point
        internalPair spacetimePair := by
    exact contDiff_const.mul
      (gravityCurvature_component_contDiff_of_components prepared
        (by
          intro direction internalOut internalIn
          exact gravityBase_connection_component_contDiff
            direction internalOut internalIn)
        internalPair spacetimePair)
  exact
    (contDiff_pi.mp (contDiff_pi.mp dualSmooth internalPair)
      spacetimePair).sub curvatureSmooth

private theorem gravityBase_conjugateMatter_eq_coupled :
    GravityBase.conjugateMatter = Coupled.conjugateMatter := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
      Source Coupled 0

private theorem conjugateMatter_apply_contDiff_of_coordinates
    (adjoint : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (coordinatesSmooth :
      ContDiff ℝ ∞ fun point => matterDualCoordinates (adjoint point))
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      adjoint point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index 1)) := by
  change ContDiff ℝ ∞ fun point =>
    matterDualCoordinates (adjoint point) index
  exact (contDiff_piLp 2).mp coordinatesSmooth index

/-- The exact first leg of the gravity-tail occurrence is one globally
smooth nine-field actual.  Its four gravity fields are generated by the
synchronized affine action write; its five non-gravity fields retain the
already generated action-selected current. -/
theorem fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_smooth :
    GravityBase.Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact contDiff_pi.mp (contDiff_pi.mp gravityBase_coframe_contDiff row)
      column
  · exact gravityBase_connection_component_contDiff
  · exact gravityBase_auxiliary_component_contDiff
  · exact gravityBase_multiplier_component_contDiff
  · intro direction
    change ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Carry.gaugeConnection point direction)
    exact actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction
  · intro pair
    change ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Carry.gaugeAuxiliary point pair)
    exact
      fixedP506L0ActionSelectedCarry_gaugeAuxiliaryCoordinate_contDiff pair
  · exact actionSelectedCoupled_scalar_contDiff
  · exact actionSelectedCoupled_matterCoordinates_contDiff
  · intro index
    rw [gravityBase_conjugateMatter_eq_coupled]
    apply conjugateMatter_apply_contDiff_of_coordinates
    change ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
    exact actionSelectedCoupled_conjugateMatterCoordinates_contDiff

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailInputRegularity
