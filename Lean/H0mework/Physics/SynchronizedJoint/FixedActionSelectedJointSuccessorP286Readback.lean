import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessor
import H0mework.Physics.JointVariation.SectionFixedScalarAssemblyNormalForm
import H0mework.Physics.ElectricJoint.ElectricECOccurrenceOperator
import H0mework.Physics.FixedJoint.FixedJointP286AlgebraicConnectionChangedRead
import H0mework.Physics.FinalJoint.FixedTimeAxisP286ConstitutiveKernel
import H0mework.Physics.FixedJoint.FixedConstitutiveFirstJet
import H0mework.Physics.ActionForcing.FixedMotherActionChargeScalarPairing
import H0mework.Physics.QuarticDynamics.FixedScalarMomentumCarry
import H0mework.Physics.ConnectionJets.P286ColorCartanQuadraticConnectionJet
import H0mework.Physics.GaugeAction.P286GaugeConnectionMomentumRegularity

/-!
# P286 readback of the Lorentz-path action-selected joint successor

The source/current-only action-selected producer first installs the radial
P286 connection response, then the constitutive auxiliary, scalar momentum
carry, and coupled temporal scalar/matter/adjoint action data before invoking
the existing five-leg joint compiler.  This module proves that the resulting
single successor settles the exact P286 `(123)` changed read on the whole
canonical zero slice.

The proof transports primitive fields through the actual compiler and derives
the zero read from the supplied action data.  No residual value, support
coordinate, target equation, or branch witness enters the constructor.  The
old five-leg nonzero theorem is retained as the negative regression; the new
zero theorem is therefore producer soundness for the stronger common write,
not a second independent constraint.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506ScalarAssemblyNormalForm
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286ConstitutiveKernel
open StageNineDiracDualFormNativeFixedP506P286RadialRequiredExteriorAnchor
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECP286AllPointSettlement
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveRegularity
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6MotherActionChargeScalarPairing
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineConjugateMatterVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
open StageNineScalarActionTemporalMomentumLegendreVelocity
open StageNineScalarActionSecondJetLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance readbackP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance readbackP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance readbackP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Raw : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source Input

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

private abbrev OldCarry : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

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
        fixedP506L0U6OccurrenceP286MotherActionCharge := by
    exact
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

private theorem radial_coframe_zeroSlice_eq_old
    (space : StageNineSpatialPoint) :
    Radial.coframe (canonicalCauchySlicePoint 0 space) =
      OldRadial.coframe (canonicalCauchySlicePoint 0 space) := by
  change
    Current.coframe (canonicalCauchySlicePoint 0 space) =
      U6.coframe (canonicalCauchySlicePoint 0 space)
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
  rw [congrFun fixedP506L0U6_coframe_eq_algebraic
    (canonicalCauchySlicePoint 0 space)]
  exact (fixedP506L0Algebraic_coframe_zeroSlice space).symm

private theorem radial_curvature_eq_old
    (point : BasePoint) :
    holonomicGaugeCurvature Radial point =
      holonomicGaugeCurvature OldRadial point :=
  holonomicGaugeCurvature_eq_of_connection_eq Radial OldRadial
    radial_gaugeConnection_eq_old point

private theorem constitutive_auxiliary_zeroSlice_eq_old
    (space : StageNineSpatialPoint) :
    Constitutive.gaugeAuxiliary (canonicalCauchySlicePoint 0 space) =
      OldConstitutive.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Radial.coframe point) (holonomicGaugeCurvature Radial point) =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (OldRadial.coframe point)
        (holonomicGaugeCurvature OldRadial point)
  rw [radial_coframe_zeroSlice_eq_old space,
    radial_curvature_eq_old point]

private theorem radial_coframe_eq_one :
    Radial.coframe = fun _ => (1 : LorentzianCoframe) := by
  change Current.coframe = _
  exact
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one

private theorem radial_curvatureCoordinate_eq_oldConstitutive :
    holonomicP286GaugeCurvatureCoordinate Radial =
      holonomicP286GaugeCurvatureCoordinate OldConstitutive := by
  have connectionEq :
      Radial.gaugeConnection = OldConstitutive.gaugeConnection := by
    simpa [OldConstitutive,
      fixedP506L0U6RadialQuarticConstitutiveActual,
      diracDualFormNativeConstitutiveWrittenCurrent] using
      radial_gaugeConnection_eq_old
  funext point pair
  change
    p286CoordinateEquiv (holonomicGaugeCurvature Radial point pair) =
      p286CoordinateEquiv
        (holonomicGaugeCurvature OldConstitutive point pair)
  rw [holonomicGaugeCurvature_eq_of_connection_eq
    Radial OldConstitutive connectionEq point]

private theorem radial_curvatureCoordinate_contDiff :
    ContDiff ℝ ∞ (holonomicP286GaugeCurvatureCoordinate Radial) := by
  rw [radial_curvatureCoordinate_eq_oldConstitutive]
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

private theorem constitutive_auxiliaryCoordinate_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate Constitutive)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have nondegenerate : Matrix.det (Radial.coframe point) ≠ 0 := by
    rw [radial_coframe_eq_one]
    norm_num
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings Source)
      (Radial.coframe point) nondegenerate
      (holonomicP286GaugeCurvatureCoordinate Radial point)
  have coframeRegular : ContDiffAt ℝ ∞ Radial.coframe point := by
    rw [radial_coframe_eq_one]
    exact contDiff_const.contDiffAt
  have inner : ContDiffAt ℝ ∞
      (fun candidate =>
        (Radial.coframe candidate,
          holonomicP286GaugeCurvatureCoordinate Radial candidate)) point :=
    coframeRegular.prodMk radial_curvatureCoordinate_contDiff.contDiffAt
  rw [constitutive_auxiliaryCoordinate_eq_formula]
  have composed := outer.comp point inner
  change ContDiffAt ℝ ∞
    (fun candidate =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Radial.coframe candidate)
        (holonomicP286GaugeCurvatureCoordinate Radial candidate)) point
      at composed
  simpa [point] using composed

private theorem constitutive_auxiliaryCoordinate_zeroSlice_eq_old
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate Constitutive
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate OldConstitutive
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [constitutive_auxiliary_zeroSlice_eq_old space]

private theorem fderiv_canonicalCauchySlicePoint_spatial_p286
    (field : BasePoint → P286GaugeTwoForm)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint 0 space)) :
    fderiv ℝ (field ∘ canonicalCauchySlicePoint 0) space
        (canonicalSpatialCoordinateDirection direction) =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  have derivative :=
    differentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

private theorem constitutive_auxiliaryDirectionalDerivative_spatial_eq_old
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286GaugeAuxiliaryDirectionalDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) direction.succ =
      p286GaugeAuxiliaryDirectionalDerivative OldConstitutive
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  unfold p286GaugeAuxiliaryDirectionalDerivative
  rw [← fderiv_canonicalCauchySlicePoint_spatial_p286
      (holonomicP286GaugeAuxiliaryCoordinate Constitutive) space direction
      ((constitutive_auxiliaryCoordinate_contDiffAt_zeroSlice space
        ).differentiableAt (by simp)),
    ← fderiv_canonicalCauchySlicePoint_spatial_p286
      (holonomicP286GaugeAuxiliaryCoordinate OldConstitutive) space direction
      (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_differentiableAt_zeroSlice
        space)]
  rw [show
      holonomicP286GaugeAuxiliaryCoordinate Constitutive ∘
          canonicalCauchySlicePoint 0 =
        holonomicP286GaugeAuxiliaryCoordinate OldConstitutive ∘
          canonicalCauchySlicePoint 0 by
    funext candidateSpace
    exact constitutive_auxiliaryCoordinate_zeroSlice_eq_old candidateSpace]

private theorem constitutive_gaugeConnection_eq_oldConstitutive :
    Constitutive.gaugeConnection = OldConstitutive.gaugeConnection := by
  change Radial.gaugeConnection = OldRadial.gaugeConnection
  exact radial_gaugeConnection_eq_old

private theorem constitutive_p286Geometric_123_eq_old
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative OldConstitutive
        (canonicalCauchySlicePoint 0 space) 3 := by
  let point := canonicalCauchySlicePoint 0 space
  have connectionEq :
      holonomicP286GaugeConnectionCoordinate Constitutive point =
        holonomicP286GaugeConnectionCoordinate OldConstitutive point := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [constitutive_gaugeConnection_eq_oldConstitutive]
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate Constitutive point =
        holonomicP286GaugeAuxiliaryCoordinate OldConstitutive point :=
    constitutive_auxiliaryCoordinate_zeroSlice_eq_old space
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  rw [connectionEq, auxiliaryEq]
  unfold pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [threeFormFirst, threeFormSecond, threeFormThird]
  simp
  have derivativeOne :
      p286GaugeAuxiliaryDirectionalDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) 1 =
        p286GaugeAuxiliaryDirectionalDerivative OldConstitutive
          (canonicalCauchySlicePoint 0 space) 1 := by
    simpa using
      constitutive_auxiliaryDirectionalDerivative_spatial_eq_old space 0
  have derivativeTwo :
      p286GaugeAuxiliaryDirectionalDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) 2 =
        p286GaugeAuxiliaryDirectionalDerivative OldConstitutive
          (canonicalCauchySlicePoint 0 space) 2 := by
    simpa using
      constitutive_auxiliaryDirectionalDerivative_spatial_eq_old space 1
  have derivativeThree :
      p286GaugeAuxiliaryDirectionalDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) 3 =
        p286GaugeAuxiliaryDirectionalDerivative OldConstitutive
          (canonicalCauchySlicePoint 0 space) 3 := by
    simpa using
      constitutive_auxiliaryDirectionalDerivative_spatial_eq_old space 2
  rw [derivativeOne, derivativeTwo, derivativeThree]

private theorem current_coframe_zeroSlice_eq_temporal
    (space : StageNineSpatialPoint) :
    Current.coframe (canonicalCauchySlicePoint 0 space) =
      Temporal.coframe (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
  change (1 : LorentzianCoframe) =
    Input.coframe (canonicalCauchySlicePoint 0 space)
  rw [← fixedP506L0CompleteJointGlobalDevelopmentActual_coframe,
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice]

private theorem current_scalar_zeroSlice_eq_temporal
    (space : StageNineSpatialPoint) :
    Current.scalar (canonicalCauchySlicePoint 0 space) =
      Temporal.scalar (canonicalCauchySlicePoint 0 space) := by
  change Raw.scalar (canonicalCauchySlicePoint 0 space) =
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source Input).scalar (canonicalCauchySlicePoint 0 space)
  rw [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice]
  rw [fixedP506L0CompleteJointActionSpacetimeSection_scalar_normalForm]
  simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  simp [scalarQuadraticTimeCorrection, scalarQuadraticTimeCoefficient,
    canonicalCauchySlicePoint, canonicalLorentzianTimeDirection]

private theorem current_matter_zeroSlice_eq_temporal
    (space : StageNineSpatialPoint) :
    Current.matter (canonicalCauchySlicePoint 0 space) =
      Temporal.matter (canonicalCauchySlicePoint 0 space) := by
  apply matterCoordinateEquiv.injective
  change matterCoordinateEquiv
      (Raw.matter (canonicalCauchySlicePoint 0 space)) =
    matterCoordinateEquiv
      ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source Input).matter (canonicalCauchySlicePoint 0 space))
  rw [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice]
  rw [fixedP506L0CompleteJointActionSpacetimeSection_matter_normalForm]
  simp

private theorem current_conjugateMatter_zeroSlice_eq_temporal
    (space : StageNineSpatialPoint) :
    Current.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      Temporal.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  apply matterDualCoordinates_injective
  change matterDualCoordinates
      (Raw.conjugateMatter (canonicalCauchySlicePoint 0 space)) =
    matterDualCoordinates
      ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source Input).conjugateMatter (canonicalCauchySlicePoint 0 space))
  rw [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice]
  rw [fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_normalForm]
  simp

private theorem temporal_scalar_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ Temporal.scalar
      (canonicalCauchySlicePoint 0 space) := by
  change DifferentiableAt ℝ
    (fun point =>
      Input.scalar point +
        canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Input) point)
    (canonicalCauchySlicePoint 0 space)
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      |>.differentiable (by simp) |>.differentiableAt).add
      ((fixedP506L0CompleteJointScalarSecondPrimitive_contDiffAt 1 0 space
        (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space)
        ).differentiableAt (by norm_num))

private theorem current_scalarCovariantDerivative_zeroSlice_eq_temporal
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative Current
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative Temporal
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicScalarCovariantDerivative Current
          (canonicalCauchySlicePoint 0 space) =
        holonomicScalarCovariantDerivative Input
          (canonicalCauchySlicePoint 0 space) := by
      change holonomicScalarCovariantDerivative Raw
          (canonicalCauchySlicePoint 0 space) = _
      exact
        fixedP506L0CompleteJointActionSpacetimeSection_scalarCovariantDerivative_zeroSlice_eq_input
          space
    _ = holonomicScalarCovariantDerivative Temporal
          (canonicalCauchySlicePoint 0 space) := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      change
        fieldDirectionalDerivative Input.scalar
              (canonicalCauchySlicePoint 0 space) direction +
            scalarMotherLieAction
              (p286LieBlockEmbed
                (Input.gaugeConnection
                  (canonicalCauchySlicePoint 0 space) direction))
              (Input.scalar (canonicalCauchySlicePoint 0 space)) =
          fieldDirectionalDerivative
              (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
                Source Input).scalar
              (canonicalCauchySlicePoint 0 space) direction +
            scalarMotherLieAction
              (p286LieBlockEmbed
                ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
                  Source Input).gaugeConnection
                  (canonicalCauchySlicePoint 0 space) direction))
              ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
                Source Input).scalar (canonicalCauchySlicePoint 0 space))
      rw [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        Source Input space
        (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
          |>.differentiable (by simp) |>.differentiableAt)
        (temporal_scalar_differentiableAt_zeroSlice space)]
      rw [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice]
      rfl

/-- On the complete canonical zero slice, the Lorentz-path section and the
old algebraic stage present exactly the same charged action data.  The later
radial write therefore settles the section assembly support without changing
the physical charge read. -/
theorem current_chargedGaugeThreeForm_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Current
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Algebraic
          (canonicalCauchySlicePoint 0 space)) := by
  calc
    formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Current
            (canonicalCauchySlicePoint 0 space)) =
        formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Temporal
            (canonicalCauchySlicePoint 0 space)) := by
      apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
      · exact current_coframe_zeroSlice_eq_temporal space
      · exact current_scalar_zeroSlice_eq_temporal space
      · exact current_scalarCovariantDerivative_zeroSlice_eq_temporal space
      · exact current_matter_zeroSlice_eq_temporal space
      · exact current_conjugateMatter_zeroSlice_eq_temporal space
    _ = formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Algebraic
            (canonicalCauchySlicePoint 0 space)) :=
      (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_chargedGaugeThreeForm_eq_temporal
        (canonicalCauchySlicePoint 0 space)).symm

private theorem algebraic_scalar_eq_temporal :
    Algebraic.scalar = Temporal.scalar := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 by
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_gaugeConnection_eq_temporal :
    Algebraic.gaugeConnection = Temporal.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 by
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem algebraic_scalarCovariantDerivative_eq_temporal
    (point : BasePoint) :
    holonomicScalarCovariantDerivative Algebraic point =
      holonomicScalarCovariantDerivative Temporal point := by
  unfold holonomicScalarCovariantDerivative
  rw [algebraic_scalar_eq_temporal, algebraic_gaugeConnection_eq_temporal]

private theorem constitutive_scalar_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    Constitutive.scalar (canonicalCauchySlicePoint 0 space) =
      Algebraic.scalar (canonicalCauchySlicePoint 0 space) := by
  change Current.scalar (canonicalCauchySlicePoint 0 space) = _
  rw [current_scalar_zeroSlice_eq_temporal,
    congrFun algebraic_scalar_eq_temporal]

private theorem oldConstitutive_scalar_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    OldConstitutive.scalar (canonicalCauchySlicePoint 0 space) =
      Algebraic.scalar (canonicalCauchySlicePoint 0 space) := by
  calc
    OldConstitutive.scalar (canonicalCauchySlicePoint 0 space) =
        OldCarry.scalar (canonicalCauchySlicePoint 0 space) := by
      symm
      exact
        scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_zeroSlice
          Source Algebraic OldConstitutive space
    _ = Algebraic.scalar (canonicalCauchySlicePoint 0 space) :=
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic
        space

private theorem current_scalarTemporalCovariantVelocity_eq_algebraic
    (space : StageNineSpatialPoint) :
    scalarTemporalCovariantVelocityOfMomentum Source Current
        (canonicalCauchySlicePoint 0 space) =
      scalarTemporalCovariantVelocityOfMomentum Source Algebraic
        (canonicalCauchySlicePoint 0 space) := by
  rw [scalarTemporalCovariantVelocityOfMomentum_eq Source Current
      (canonicalCauchySlicePoint 0 space) (by
        rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]),
    scalarTemporalCovariantVelocityOfMomentum_eq Source Algebraic
      (canonicalCauchySlicePoint 0 space)
      (fixedP506L0Algebraic_coframe_zeroSlice space),
    current_scalarCovariantDerivative_zeroSlice_eq_temporal,
    algebraic_scalarCovariantDerivative_eq_temporal]

private theorem carryVelocity_eq_old
    (space : StageNineSpatialPoint) :
    scalarActionTemporalMomentumCarryVelocity Source Current Constitutive
        space =
      scalarActionTemporalMomentumCarryVelocity Source Algebraic
        OldConstitutive space := by
  unfold scalarActionTemporalMomentumCarryVelocity
  dsimp only
  rw [current_scalarTemporalCovariantVelocity_eq_algebraic]
  rw [show Constitutive.gaugeConnection = OldConstitutive.gaugeConnection from
      constitutive_gaugeConnection_eq_oldConstitutive]
  rw [constitutive_scalar_zeroSlice_eq_algebraic,
    oldConstitutive_scalar_zeroSlice_eq_algebraic]

private theorem carry_scalar_eq_old :
    Carry.scalar = OldCarry.scalar := by
  funext point
  unfold Carry completeJointActionSelectedScalarMomentumCarryActual
    OldCarry fixedP506L0U6RadialQuarticScalarMomentumCarryActual
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
  change
    Constitutive.scalar
          (canonicalCauchySlicePoint 0
            (canonicalSpatialProjection point)) +
        canonicalTimeProjection point •
          scalarActionTemporalMomentumCarryVelocity Source Current
            Constitutive (canonicalSpatialProjection point) =
      OldConstitutive.scalar
          (canonicalCauchySlicePoint 0
            (canonicalSpatialProjection point)) +
        canonicalTimeProjection point •
          scalarActionTemporalMomentumCarryVelocity Source Algebraic
            OldConstitutive (canonicalSpatialProjection point)
  rw [constitutive_scalar_zeroSlice_eq_algebraic,
    oldConstitutive_scalar_zeroSlice_eq_algebraic,
    carryVelocity_eq_old]

private theorem carry_scalar_contDiff :
    ContDiff ℝ ∞ Carry.scalar := by
  rw [carry_scalar_eq_old]
  exact
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_contDiff

private theorem algebraic_coframe_eq_temporal :
    Algebraic.coframe = Temporal.coframe := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 by
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_matter_eq_temporal :
    Algebraic.matter = Temporal.matter := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 by
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem algebraic_conjugateMatter_eq_temporal :
    Algebraic.conjugateMatter = Temporal.conjugateMatter := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 by
    exact
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rfl

private theorem carry_gaugeConnection_eq_oldCarry :
    Carry.gaugeConnection = OldCarry.gaugeConnection := by
  change Constitutive.gaugeConnection = OldConstitutive.gaugeConnection
  exact constitutive_gaugeConnection_eq_oldConstitutive

private theorem carry_scalarCovariantDerivative_zeroSlice_eq_oldCarry
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative Carry
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative OldCarry
        (canonicalCauchySlicePoint 0 space) := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [carry_scalar_eq_old, carry_gaugeConnection_eq_oldCarry]

private theorem carry_coframe_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    Carry.coframe (canonicalCauchySlicePoint 0 space) =
      Algebraic.coframe (canonicalCauchySlicePoint 0 space) := by
  change Current.coframe (canonicalCauchySlicePoint 0 space) = _
  rw [current_coframe_zeroSlice_eq_temporal,
    congrFun algebraic_coframe_eq_temporal]

private theorem carry_matter_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    Carry.matter (canonicalCauchySlicePoint 0 space) =
      Algebraic.matter (canonicalCauchySlicePoint 0 space) := by
  change Current.matter (canonicalCauchySlicePoint 0 space) = _
  rw [current_matter_zeroSlice_eq_temporal,
    congrFun algebraic_matter_eq_temporal]

private theorem carry_conjugateMatter_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    Carry.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      Algebraic.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  change Current.conjugateMatter (canonicalCauchySlicePoint 0 space) = _
  rw [current_conjugateMatter_zeroSlice_eq_temporal,
    congrFun algebraic_conjugateMatter_eq_temporal]

private theorem carry_scalar_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    Carry.scalar (canonicalCauchySlicePoint 0 space) =
      Algebraic.scalar (canonicalCauchySlicePoint 0 space) := by
  rw [carry_scalar_eq_old]
  exact
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic
      space

private theorem carry_scalarCovariantDerivative_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative Carry
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative Algebraic
        (canonicalCauchySlicePoint 0 space) := by
  rw [carry_scalarCovariantDerivative_zeroSlice_eq_oldCarry]
  exact
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalarCovariantDerivative_zeroSlice
      space

/-- The lifted radial-plus-momentum current carries exactly the original
mother-action charge on the complete zero slice. -/
theorem carry_chargedGaugeThreeForm_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Carry
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Algebraic
          (canonicalCauchySlicePoint 0 space)) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact carry_coframe_zeroSlice_eq_algebraic space
  · exact carry_scalar_zeroSlice_eq_algebraic space
  · exact carry_scalarCovariantDerivative_zeroSlice_eq_algebraic space
  · exact carry_matter_zeroSlice_eq_algebraic space
  · exact carry_conjugateMatter_zeroSlice_eq_algebraic space

private theorem carry_p286Geometric_eq_constitutive
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Carry point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive
        point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [show Carry.gaugeConnection = Constitutive.gaugeConnection by
      exact
        scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gaugeConnection
          Source Current Constitutive,
    show Carry.gaugeAuxiliary = Constitutive.gaugeAuxiliary by
      exact
        scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_gaugeAuxiliary
          Source Current Constitutive]

private theorem oldCarry_p286Geometric_eq_oldConstitutive
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative OldCarry point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative OldConstitutive
        point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeConnection_eq_postAB,
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeAuxiliary_eq_postAB]

private theorem carry_p286Geometric_123_eq_oldCarry
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Carry
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative OldCarry
        (canonicalCauchySlicePoint 0 space) 3 := by
  calc
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Carry
          (canonicalCauchySlicePoint 0 space) 3 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive
          (canonicalCauchySlicePoint 0 space) 3 := by
      rw [carry_p286Geometric_eq_constitutive]
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative OldConstitutive
          (canonicalCauchySlicePoint 0 space) 3 :=
      constitutive_p286Geometric_123_eq_old space
    _ = holonomicP286GaugeAuxiliaryExteriorCovariantDerivative OldCarry
          (canonicalCauchySlicePoint 0 space) 3 := by
      rw [oldCarry_p286Geometric_eq_oldConstitutive]

/-- The action-selected radial principal and scalar-momentum carry settle the
previous `(123)` changed read on the same Lorentz-path source occurrence. -/
theorem carry_p286Euler123_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Carry
        (canonicalCauchySlicePoint 0 space) 3 = 0 := by
  have oldZero :=
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_p286Euler123_zeroSlice
      space
  have oldCharged :=
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_chargedGaugeThreeForm_zeroSlice_eq_algebraic
      space
  unfold holonomicFormNativeP286GaugeEulerThreeForm at oldZero ⊢
  simp only [Pi.add_apply] at oldZero ⊢
  rw [carry_p286Geometric_123_eq_oldCarry,
    carry_chargedGaugeThreeForm_zeroSlice_eq_algebraic]
  rw [oldCharged] at oldZero
  exact oldZero

private theorem carry_coframe_eq_one :
    Carry.coframe = fun _ => (1 : LorentzianCoframe) := by
  calc
    Carry.coframe = Constitutive.coframe :=
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_coframe
        Source Current Constitutive
    _ = Radial.coframe := rfl
    _ = fun _ => (1 : LorentzianCoframe) := radial_coframe_eq_one

private theorem carry_matter_eq_current :
    Carry.matter = Current.matter := by
  rfl

private theorem carry_conjugateMatter_eq_current :
    Carry.conjugateMatter = Current.conjugateMatter := by
  rfl

private theorem current_matter_eq_raw :
    Current.matter = Raw.matter := by
  rfl

private theorem current_conjugateMatter_eq_raw :
    Current.conjugateMatter = Raw.conjugateMatter := by
  rfl

private theorem carry_gaugeConnection_normalForm
    (point : BasePoint) (direction : LorentzianIndex) :
    Carry.gaugeConnection point direction =
      Input.gaugeConnection point direction +
        p286CoordinateEquiv.symm
          (p286RadialQuarticTemporalConnection
            fixedP506L0U6OccurrenceP286MotherActionCharge point direction) := by
  change
    (varyP286GaugeConnectionCoordinate Current
      (p286RadialQuarticTemporalConnection
        (completeJointActionSelectedRadialCharge Source Current)) 1
      ).gaugeConnection point direction = _
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    show completeJointActionSelectedRadialCharge Source Current =
        fixedP506L0U6OccurrenceP286MotherActionCharge by
      exact
        fixedP506L0LorentzPathActionSelectedRadialCharge_eq_motherActionCharge,
    congrFun final_gaugeConnection_eq_input point]
  simp only [one_smul]

private theorem carry_gaugeConnectionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Carry.gaugeConnection point direction) := by
  rw [show
      (fun point =>
        p286CoordinateEquiv (Carry.gaugeConnection point direction)) =
        fun point =>
          p286CoordinateEquiv (Input.gaugeConnection point direction) +
            p286RadialQuarticTemporalConnection
              fixedP506L0U6OccurrenceP286MotherActionCharge point direction by
    funext point
    rw [carry_gaugeConnection_normalForm, map_add,
      p286CoordinateEquiv.apply_symm_apply]]
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
      direction).add
      (contDiff_pi.mp
        (p286RadialQuarticTemporalConnection_contDiff
          fixedP506L0U6OccurrenceP286MotherActionCharge) direction)

private abbrev RadialProxy : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate Input
    (p286RadialQuarticTemporalConnection
      fixedP506L0U6OccurrenceP286MotherActionCharge) 1

private theorem radial_gaugeConnection_eq_proxy :
    Radial.gaugeConnection = RadialProxy.gaugeConnection := by
  funext point direction
  apply p286CoordinateEquiv.injective
  change
    p286CoordinateEquiv (Carry.gaugeConnection point direction) =
      holonomicP286GaugeConnectionCoordinate RadialProxy point direction
  rw [carry_gaugeConnection_normalForm,
    holonomicP286GaugeConnectionCoordinate_vary]
  simp only [map_add, p286CoordinateEquiv.apply_symm_apply, one_smul,
    Pi.add_apply]
  rfl

private theorem input_gaugeConnectionCoordinate_line
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate Input point direction =
      (-c3h181FullConnectionCoefficient (-point) direction) •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  rw [congrFun
    (fixedP506FormNativeJointActionSolvedSuccessor_connection_eq_neg_source_neg_point
      point) direction]
  simp only [Pi.neg_apply]
  rw [positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line]
  simp only [neg_smul]

private theorem motherActionCharge_bracket_neg_currentGaussLine_zero
    (coefficient : ℝ) :
    p286CoordinateLieBracket
        fixedP506L0U6OccurrenceP286MotherActionCharge
        (-(coefficient •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)) = 0 := by
  rw [← neg_smul, p286CoordinateLieBracket_smul_right,
    fixedP506L0U6OccurrenceP286MotherActionCharge_bracket_currentGaussCharge_zero,
    smul_zero]

private theorem neg_currentGaussLine_bracket_motherActionCharge_zero
    (coefficient : ℝ) :
    p286CoordinateLieBracket
        (-(coefficient •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge))
        fixedP506L0U6OccurrenceP286MotherActionCharge = 0 := by
  rw [← neg_smul, p286CoordinateLieBracket_smul_left,
    currentGaussCharge_bracket_fixedP506L0U6OccurrenceP286MotherActionCharge_zero,
    smul_zero]

private theorem radialProxy_crossBracket_zero
    (point : BasePoint) :
    (fun pair : Fin 6 =>
      p286CoordinateLieBracket
          (p286RadialQuarticTemporalConnection
            fixedP506L0U6OccurrenceP286MotherActionCharge
            point (pairFirst pair))
          (holonomicP286GaugeConnectionCoordinate Input
            point (pairSecond pair)) +
        p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate Input
            point (pairFirst pair))
          (p286RadialQuarticTemporalConnection
            fixedP506L0U6OccurrenceP286MotherActionCharge
            point (pairSecond pair))) = 0 := by
  funext pair
  fin_cases pair <;>
    simp [p286RadialQuarticTemporalConnection,
      p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
      pairFirst, pairSecond, input_gaugeConnectionCoordinate_line,
      p286CoordinateLieBracket_smul_left,
      motherActionCharge_bracket_neg_currentGaussLine_zero]

private theorem radialProxy_linearCurvature_eq_increment
    (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation Input
        (p286RadialQuarticTemporalConnection
          fixedP506L0U6OccurrenceP286MotherActionCharge) point =
      fixedP506L0U6RadialQuarticCurvatureIncrement point := by
  funext pair
  have exteriorEq := congrFun
    (fixedP506L0U6RadialQuarticConnection_exteriorDerivative point) pair
  have crossEq := congrFun (radialProxy_crossBracket_zero point) pair
  simp only [Pi.zero_apply] at crossEq
  unfold p286GaugeConnectionLinearCurvatureVariation
  rw [add_assoc, crossEq, add_zero]
  exact exteriorEq

private theorem radial_curvatureCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate Radial point =
      holonomicP286GaugeCurvatureCoordinate Algebraic point +
        fixedP506L0U6RadialQuarticCurvatureIncrement point := by
  have radialProxyCurvature :
      holonomicP286GaugeCurvatureCoordinate Radial point =
        holonomicP286GaugeCurvatureCoordinate RadialProxy point := by
    unfold holonomicP286GaugeCurvatureCoordinate
    rw [holonomicGaugeCurvature_eq_of_connection_eq
      Radial RadialProxy radial_gaugeConnection_eq_proxy point]
  rw [radialProxyCurvature]
  rw [holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff
    Input fixedP506FormNativeJointActionSolvedSuccessor_smooth
    (p286RadialQuarticTemporalConnection
      fixedP506L0U6OccurrenceP286MotherActionCharge)
    (p286RadialQuarticTemporalConnection_contDiff
      fixedP506L0U6OccurrenceP286MotherActionCharge) 1 point]
  rw [radialProxy_linearCurvature_eq_increment,
    fixedP506L0U6RadialQuarticConnection_quadraticBracket_zero]
  simp only [one_smul, one_pow, smul_zero, add_zero]
  have baseCurvature :
      holonomicP286GaugeCurvatureCoordinate Input point =
        holonomicP286GaugeCurvatureCoordinate Algebraic point := by
    unfold holonomicP286GaugeCurvatureCoordinate
    rw [holonomicGaugeCurvature_eq_of_connection_eq
      Input Algebraic algebraic_gaugeConnection_eq_input.symm point]
  rw [baseCurvature]

private theorem temporal_coframe_eq_input :
    Temporal.coframe = Input.coframe := by
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
      Source Input

private theorem algebraic_coframe_eq_input :
    Algebraic.coframe = Input.coframe :=
  algebraic_coframe_eq_temporal.trans temporal_coframe_eq_input

private theorem algebraic_curvatureCoordinate_eq_input
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate Algebraic point =
      holonomicP286GaugeCurvatureCoordinate Input point := by
  unfold holonomicP286GaugeCurvatureCoordinate
  rw [holonomicGaugeCurvature_eq_of_connection_eq
    Algebraic Input algebraic_gaugeConnection_eq_input point]

private theorem algebraic_auxiliaryCoordinate_eq_liveConstitutive :
    holonomicP286GaugeAuxiliaryCoordinate Algebraic =
      fixedP506FormNativeConstitutiveAuxiliaryCoordinate := by
  funext point
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [← completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
    Source Input point]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
    fixedP506FormNativeConstitutiveAuxiliaryCoordinate
  rw [algebraic_coframe_eq_input,
    holonomicGaugeCurvature_eq_of_connection_eq
      Algebraic Input algebraic_gaugeConnection_eq_input point]
  rfl

/-- Whole-field coordinate normal form of the action-selected constitutive
auxiliary.  It reads the already generated solved-input auxiliary and the
same-source radial action profile; neither term is supplied by a residual. -/
theorem constitutive_auxiliaryCoordinate_global_normalForm :
    holonomicP286GaugeAuxiliaryCoordinate Constitutive =
      fun point =>
        holonomicP286GaugeAuxiliaryCoordinate Input point -
          fixedP506L0P286RadialEulerAuxiliaryProfile point := by
  funext point
  have baseEliminates :
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source) 1
          (holonomicP286GaugeCurvatureCoordinate Algebraic point) =
        holonomicP286GaugeAuxiliaryCoordinate Input point := by
    rw [algebraic_curvatureCoordinate_eq_input]
    exact
      fixedP506FormNativeConstitutiveActionInverse_frozenCoframe point
  have incrementEliminates :
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source) 1
          (fixedP506L0U6RadialQuarticCurvatureIncrement point) =
        -fixedP506L0P286RadialEulerAuxiliaryProfile point := by
    rw [← fixedP506L0U6RadialQuarticCurvatureIncrement_eq_constitutive point]
    exact
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_constitutive
        (sourceGeneratedUnifiedCouplings Source) 1 (by norm_num)
        (-fixedP506L0P286RadialEulerAuxiliaryProfile point)
  rw [constitutive_auxiliaryCoordinate_eq_formula]
  change
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings Source) (Radial.coframe point)
        (holonomicP286GaugeCurvatureCoordinate Radial point) = _
  rw [radial_coframe_eq_one]
  change
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings Source) 1
        (holonomicP286GaugeCurvatureCoordinate Radial point) = _
  rw [radial_curvatureCoordinate_normalForm]
  change
    p286CoframeActionConstitutiveInverseVerticalLinear
        (sourceGeneratedUnifiedCouplings Source) 1
        (holonomicP286GaugeCurvatureCoordinate Algebraic point +
          fixedP506L0U6RadialQuarticCurvatureIncrement point) = _
  rw [map_add]
  simp only [p286CoframeActionConstitutiveInverseVerticalLinear_apply]
  rw [baseEliminates, incrementEliminates]
  simp only [sub_eq_add_neg]

private theorem
    constitutive_auxiliaryDirectionalDerivative_eq_requiredExteriorAnchor_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) direction =
      p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) direction := by
  let point := canonicalCauchySlicePoint 0 space
  have algebraicDerivativeEqInput :
      p286GaugeAuxiliaryDirectionalDerivative Algebraic point direction =
        p286GaugeAuxiliaryDirectionalDerivative Input point direction := by
    unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
    rw [algebraic_auxiliaryCoordinate_eq_liveConstitutive]
    exact
      fixedP506FormNativeConstitutiveAuxiliaryCoordinate_fderiv_eq_input_zeroSlice
        space direction
  rw [fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryDerivative,
    algebraicDerivativeEqInput]
  have inputDifferentiable : DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate Input) point :=
    ((holonomicP286GaugeAuxiliaryCoordinate_contDiff Input
          fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).differentiable (by simp)).differentiableAt
  have radialDifferentiable : DifferentiableAt ℝ
      fixedP506L0P286RadialEulerAuxiliaryProfile point :=
    ((fixedP506L0P286RadialEulerAuxiliaryProfile_contDiff.differentiable
      (by simp))).differentiableAt
  unfold p286GaugeAuxiliaryDirectionalDerivative
  rw [constitutive_auxiliaryCoordinate_global_normalForm]
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RadialEulerPrimitiveActual =
      fixedP506L0P286RadialEulerAuxiliaryProfile by
    funext candidate
    exact fixedP506L0P286RadialEulerPrimitiveActual_auxiliaryCoordinate
      candidate]
  unfold fieldDirectionalDerivative
  have derivativeEquality :=
    fderiv_sub inputDifferentiable radialDifferentiable
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] P286GaugeTwoForm =>
      derivative (coordinateDirection direction)) derivativeEquality
  change
    (fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate Input -
          fixedP506L0P286RadialEulerAuxiliaryProfile)
        (canonicalCauchySlicePoint 0 space))
          (coordinateDirection direction) = _
  simpa [point] using applied

private theorem
    constitutive_exteriorDerivative_eq_requiredExteriorAnchor_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative Constitutive
        (canonicalCauchySlicePoint 0 space) =
      p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) by
    funext direction
    exact
      constitutive_auxiliaryDirectionalDerivative_eq_requiredExteriorAnchor_zeroSlice
        space direction]

private theorem algebraic_auxiliaryCoordinate_normalForm_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate Algebraic
        (canonicalCauchySlicePoint 0 space) =
      c3h181FullAuxiliaryCoordinateNormalForm
        (-(canonicalCauchySlicePoint 0 space)) := by
  rw [algebraic_auxiliaryCoordinate_eq_liveConstitutive]
  rw [fixedP506FormNativeConstitutiveAuxiliaryCoordinate_zeroSlice]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm
      (canonicalCauchySlicePoint 0 space)

private theorem currentGaussCharge_bracket_neg_smul_self_zero
    (coefficient : ℝ) :
    p286CoordinateLieBracket
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        (-(coefficient •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)) = 0 := by
  rw [← neg_smul, p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_self, smul_zero]

private theorem currentGaussCharge_bracket_neg_smul_motherActionCharge_zero
    (coefficient : ℝ) :
    p286CoordinateLieBracket
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        (-(coefficient •
          fixedP506L0U6OccurrenceP286MotherActionCharge)) = 0 := by
  rw [← neg_smul, p286CoordinateLieBracket_smul_right,
    currentGaussCharge_bracket_fixedP506L0U6OccurrenceP286MotherActionCharge_zero,
    smul_zero]

private theorem motherActionCharge_bracket_neg_smul_self_zero
    (coefficient : ℝ) :
    p286CoordinateLieBracket
        fixedP506L0U6OccurrenceP286MotherActionCharge
        (-(coefficient •
          fixedP506L0U6OccurrenceP286MotherActionCharge)) = 0 := by
  rw [← neg_smul, p286CoordinateLieBracket_smul_right,
    p286CoordinateLieBracket_self, smul_zero]

private theorem algebraic_connectionExteriorAction_zero
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate Algebraic
          (canonicalCauchySlicePoint 0 space))
        (holonomicP286GaugeAuxiliaryCoordinate Algebraic
          (canonicalCauchySlicePoint 0 space)) = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  rw [show
      holonomicP286GaugeConnectionCoordinate Algebraic point =
        fun direction =>
          (-c3h181FullConnectionCoefficient (-point) direction) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge by
    funext direction
    rw [show
      holonomicP286GaugeConnectionCoordinate Algebraic point direction =
        holonomicP286GaugeConnectionCoordinate Input point direction by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [algebraic_gaugeConnection_eq_input]]
    exact input_gaugeConnectionCoordinate_line point direction,
    algebraic_auxiliaryCoordinate_normalForm_zeroSlice]
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
    p286GaugeTwoFormAdjoint
  funext triple
  fin_cases triple <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      c3h181FullConnectionCoefficient,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient, Fin.sum_univ_six,
      p286CoordinateLieBracket_smul_left,
      p286CoordinateLieBracket_smul_right,
      currentGaussCharge_bracket_neg_smul_self_zero,
      p286CoordinateLieBracket_self]

private theorem constitutive_connectionCoordinate_normalForm
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate Constitutive point direction =
      (-c3h181FullConnectionCoefficient (-point) direction) •
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge +
        p286RadialQuarticTemporalConnection
          fixedP506L0U6OccurrenceP286MotherActionCharge point direction := by
  change p286CoordinateEquiv (Carry.gaugeConnection point direction) = _
  rw [carry_gaugeConnection_normalForm, map_add,
    p286CoordinateEquiv.apply_symm_apply]
  have inputLine := input_gaugeConnectionCoordinate_line point direction
  change p286CoordinateEquiv (Input.gaugeConnection point direction) = _
    at inputLine
  rw [inputLine]

private theorem constitutive_auxiliaryCoordinate_normalForm_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate Constitutive
        (canonicalCauchySlicePoint 0 space) =
      c3h181FullAuxiliaryCoordinateNormalForm
          (-(canonicalCauchySlicePoint 0 space)) -
        fixedP506L0P286RadialEulerAuxiliaryProfile
          (canonicalCauchySlicePoint 0 space) := by
  rw [congrFun constitutive_auxiliaryCoordinate_global_normalForm
    (canonicalCauchySlicePoint 0 space)]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm]

private theorem constitutive_connectionExteriorAction_zeroSlice
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate Constitutive
          (canonicalCauchySlicePoint 0 space))
        (holonomicP286GaugeAuxiliaryCoordinate Constitutive
          (canonicalCauchySlicePoint 0 space)) = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  rw [show
      holonomicP286GaugeConnectionCoordinate Constitutive point =
        fun direction =>
          (-c3h181FullConnectionCoefficient (-point) direction) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge +
            p286RadialQuarticTemporalConnection
              fixedP506L0U6OccurrenceP286MotherActionCharge point direction by
    funext direction
    exact constitutive_connectionCoordinate_normalForm point direction,
    constitutive_auxiliaryCoordinate_normalForm_zeroSlice]
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
    p286GaugeTwoFormAdjoint
  funext triple
  fin_cases triple <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      c3h181FullConnectionCoefficient,
      fixedP506L0P286RadialEulerAuxiliaryProfile,
      p286RadialQuarticTemporalConnection, p286TemporalGaugeOneForm,
      p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      canonicalLorentzianTimeDirection,
      threeFormFirst, threeFormSecond, threeFormThird,
      orderedP286GaugeTwoFormComponent, pairFirst, pairSecond,
      orientedLorentzBivectorBasisCoefficient,
      Fin.sum_univ_six, Fin.sum_univ_three,
      p286CoordinateLieBracket_add_left,
      p286CoordinateLieBracket_add_right,
      p286CoordinateLieBracket_smul_left,
      p286CoordinateLieBracket_smul_right,
      fixedP506L0U6OccurrenceP286MotherActionCharge_bracket_currentGaussCharge_zero,
      currentGaussCharge_bracket_neg_smul_self_zero,
      currentGaussCharge_bracket_neg_smul_motherActionCharge_zero,
      motherActionCharge_bracket_neg_currentGaussLine_zero,
      motherActionCharge_bracket_neg_smul_self_zero,
      p286CoordinateLieBracket_self,
      sub_eq_add_neg]


private theorem carry_matterCoordinates_contDiff :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (Carry.matter point) := by
  rw [carry_matter_eq_current, current_matter_eq_raw]
  exact fixedP506L0CompleteJointActionSpacetimeSection_matter_contDiff

private theorem carry_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates Carry) := by
  unfold holonomicConjugateMatterCoordinates
  rw [carry_conjugateMatter_eq_current, current_conjugateMatter_eq_raw]
  exact
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatterCoordinates_contDiff

private theorem carry_scalarAccelerationProfile_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞ (completeJointScalarAccelerationProfile Source Carry)
      (canonicalCauchySlicePoint 0 space) := by
  apply completeJointScalarAccelerationProfile_contDiffAt_of_local
  · rw [carry_coframe_eq_one]
    norm_num
  · rw [carry_coframe_eq_one]
    exact contDiff_const.contDiffAt
  · exact carry_scalar_contDiff.contDiffAt
  · exact carry_matterCoordinates_contDiff.contDiffAt
  · exact carry_conjugateMatterCoordinates_contDiff.contDiffAt
  · intro direction
    exact (carry_gaugeConnectionCoordinate_contDiff direction).contDiffAt

private theorem canonicalSpacetimeContactTranslation_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

private theorem carry_scalarAccelerationProfile_recentered_contDiffAt_one
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source Carry ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have profileAtTranslated : ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source Carry)
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa [point, canonicalSpacetimeContactTranslation] using
      (carry_scalarAccelerationProfile_contDiffAt_zeroSlice space).of_le
        (by norm_num)
  exact profileAtTranslated.comp 0
    ((canonicalSpacetimeContactTranslation_contDiff point).contDiffAt.of_le
      (by norm_num))

private theorem coupledScalarSecondPrimitive_recentered_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Carry) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
  rw [
    canonicalTimeSecondPrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice]
  exact canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
    (completeJointScalarAccelerationProfile Source Carry ∘
      canonicalSpacetimeContactTranslation
        (canonicalCauchySlicePoint 0 space))
    (carry_scalarAccelerationProfile_recentered_contDiffAt_one space)

private theorem coupledRecentered_scalar_eq_add_secondPrimitive
    (space : StageNineSpatialPoint) :
    (fullyRecenterHolonomicConfiguration Coupled
        (canonicalCauchySlicePoint 0 space)).scalar =
      (fullyRecenterHolonomicConfiguration Carry
          (canonicalCauchySlicePoint 0 space)).scalar +
        (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Carry) ∘
            canonicalSpacetimeContactTranslation
              (canonicalCauchySlicePoint 0 space)) := by
  funext point
  unfold fullyRecenterHolonomicConfiguration Coupled
    completeJointActionSelectedCoupledTemporalActual
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  rfl

private theorem recenteredCarry_scalar_differentiableAt
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (fullyRecenterHolonomicConfiguration Carry
        (canonicalCauchySlicePoint 0 space)).scalar 0 := by
  change DifferentiableAt ℝ
    (Carry.scalar ∘
      canonicalSpacetimeContactTranslation
        (canonicalCauchySlicePoint 0 space)) 0
  exact
    (carry_scalar_contDiff.comp
      (canonicalSpacetimeContactTranslation_contDiff
        (canonicalCauchySlicePoint 0 space))).differentiable
      (by simp) |>.differentiableAt

/-- The coupled scalar/primal/adjoint producer has zero scalar second-
primitive first jet on the canonical zero slice, so it preserves the
action-selected scalar covariant first jet carried by `Carry`. -/
theorem coupled_scalarCovariantDerivative_zeroSlice_eq_carry
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative Coupled
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative Carry
        (canonicalCauchySlicePoint 0 space) := by
  let contact := canonicalCauchySlicePoint 0 space
  let generatedRecentered :=
    fullyRecenterHolonomicConfiguration Coupled contact
  let currentRecentered := fullyRecenterHolonomicConfiguration Carry contact
  have primitiveDerivative :=
    coupledScalarSecondPrimitive_recentered_hasFDerivAt space
  have primitiveDerivative' :
      HasFDerivAt
        (canonicalTimeSecondPrimitive
            (completeJointScalarAccelerationProfile Source Carry) ∘
          canonicalSpacetimeContactTranslation contact)
        (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
    simpa [contact] using primitiveDerivative
  have currentDifferentiable :
      DifferentiableAt ℝ currentRecentered.scalar 0 := by
    simpa [currentRecentered, contact] using
      recenteredCarry_scalar_differentiableAt space
  have primitiveValueZero :
      (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Carry) ∘
        canonicalSpacetimeContactTranslation contact) 0 = 0 := by
    change canonicalTimeSecondPrimitive
      (completeJointScalarAccelerationProfile Source Carry)
      (canonicalSpacetimeContactTranslation contact 0) = 0
    rw [canonicalSpacetimeContactTranslation_zero]
    exact canonicalTimeSecondPrimitive_zeroSlice
      (completeJointScalarAccelerationProfile Source Carry) space
  have scalarDerivativeEq (direction : LorentzianIndex) :
      fieldDirectionalDerivative generatedRecentered.scalar 0 direction =
        fieldDirectionalDerivative currentRecentered.scalar 0 direction := by
    unfold fieldDirectionalDerivative
    rw [show generatedRecentered.scalar =
        currentRecentered.scalar +
          (canonicalTimeSecondPrimitive
              (completeJointScalarAccelerationProfile Source Carry) ∘
            canonicalSpacetimeContactTranslation contact) by
      simpa [generatedRecentered, currentRecentered, contact] using
        coupledRecentered_scalar_eq_add_secondPrimitive space]
    rw [fderiv_add currentDifferentiable
      primitiveDerivative'.differentiableAt, add_apply,
      primitiveDerivative'.fderiv, zero_apply, add_zero]
  have scalarValueEq : generatedRecentered.scalar 0 =
      currentRecentered.scalar 0 := by
    rw [show generatedRecentered.scalar =
        currentRecentered.scalar +
          (canonicalTimeSecondPrimitive
              (completeJointScalarAccelerationProfile Source Carry) ∘
            canonicalSpacetimeContactTranslation contact) by
      simpa [generatedRecentered, currentRecentered, contact] using
        coupledRecentered_scalar_eq_add_secondPrimitive space]
    rw [Pi.add_apply, primitiveValueZero, add_zero]
  have gaugeConnectionEq (direction : LorentzianIndex) :
      generatedRecentered.gaugeConnection 0 direction =
        currentRecentered.gaugeConnection 0 direction := by
    rfl
  rw [←
    fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
      Coupled contact,
    ←
    fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
      Carry contact]
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [scalarDerivativeEq direction, gaugeConnectionEq direction,
    scalarValueEq]

/-- The coupled temporal action leg preserves the complete charged current
carried by the radial-plus-momentum actual on the canonical zero slice. -/
theorem coupled_chargedGaugeThreeForm_zeroSlice_eq_carry
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Coupled
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Carry
          (canonicalCauchySlicePoint 0 space)) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact congrFun
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
        Source Carry) _
  · exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        Source Carry space
  · exact coupled_scalarCovariantDerivative_zeroSlice_eq_carry space
  · exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        Source Carry space
  · exact
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        Source Carry space

private theorem coupled_p286Geometric_eq_carry
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Coupled point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Carry point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rfl

/-- The complete scalar/primal/adjoint temporal producer preserves the
settled `(123)` P286 action read on every canonical zero-slice occurrence. -/
theorem coupled_p286Euler123_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Coupled
        (canonicalCauchySlicePoint 0 space) 3 = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  simp only [Pi.add_apply]
  rw [coupled_p286Geometric_eq_carry,
    coupled_chargedGaugeThreeForm_zeroSlice_eq_carry]
  exact carry_p286Euler123_zeroSlice space

private theorem coupled_gaugeConnection_eq_carry :
    Coupled.gaugeConnection = Carry.gaugeConnection := by
  rfl

private theorem coupled_gaugeAuxiliary_eq_carry :
    Coupled.gaugeAuxiliary = Carry.gaugeAuxiliary := by
  rfl

private def SmoothGaugeProxy : StageNineHolonomicConfiguration :=
  { Input with gaugeConnection := Coupled.gaugeConnection }

private theorem smoothGaugeProxy_smooth : SmoothGaugeProxy.Smooth := by
  rcases fixedP506FormNativeJointActionSolvedSuccessor_smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, _gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, ?_, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
    conjugateMatterSmooth⟩
  intro direction
  unfold SmoothGaugeProxy
  rw [coupled_gaugeConnection_eq_carry]
  exact carry_gaugeConnectionCoordinate_contDiff direction

private theorem coupled_gaugeConnection_eq_smoothGaugeProxy :
    Coupled.gaugeConnection = SmoothGaugeProxy.gaugeConnection := by
  rfl

private abbrev LocalTemporal (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source
    (fullyRecenterHolonomicConfiguration Coupled point)

private abbrev LocalWrite (point : BasePoint) : P286GaugeOneForm :=
  diracDualFormNativeP286CanonicalGeneratedWrite Source (LocalTemporal point)

private abbrev ProxyRecenter (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration SmoothGaugeProxy point

private abbrev LocalCandidate (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (LocalTemporal point) (LocalWrite point)

private abbrev ProxyCandidate (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (ProxyRecenter point) (LocalWrite point)

private theorem proxyRecenter_smooth (point : BasePoint) :
    (ProxyRecenter point).Smooth :=
  fullyRecenterHolonomicConfiguration_smooth SmoothGaugeProxy
    smoothGaugeProxy_smooth point

private theorem localTemporal_gaugeConnection_eq_proxyRecenter
    (point : BasePoint) :
    (LocalTemporal point).gaugeConnection =
      (ProxyRecenter point).gaugeConnection := by
  funext localPoint
  change
    Coupled.gaugeConnection
        (canonicalSpacetimeContactTranslation point localPoint) =
      SmoothGaugeProxy.gaugeConnection
        (canonicalSpacetimeContactTranslation point localPoint)
  exact congrFun coupled_gaugeConnection_eq_smoothGaugeProxy _

private theorem canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gaugeConnection = second.gaugeConnection)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalConnectionCandidate first write
      ).gaugeConnection =
      (diracDualFormNativeP286CanonicalConnectionCandidate second write
        ).gaugeConnection := by
  funext point direction
  simp only [diracDualFormNativeP286CanonicalConnectionCandidate,
    installP286HolonomicConnectionSecondJet,
    varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate]
  rw [connectionEq]

private theorem localCandidate_gaugeConnection_eq_proxyCandidate
    (point : BasePoint) :
    (LocalCandidate point).gaugeConnection =
      (ProxyCandidate point).gaugeConnection :=
  canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (LocalTemporal point) (ProxyRecenter point)
    (localTemporal_gaugeConnection_eq_proxyRecenter point)
    (LocalWrite point)

private theorem installSecondJet_gaugeCurvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet)
    (parameter : ℝ) :
    holonomicGaugeCurvature
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 = holonomicGaugeCurvature configuration 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (installP286HolonomicConnectionSecondJet_curvature_origin
      configuration smooth jet parameter) pair

private theorem localCandidate_gaugeCurvature_origin_eq_coupled
    (point : BasePoint) :
    holonomicGaugeCurvature (LocalCandidate point) 0 =
      holonomicGaugeCurvature Coupled point := by
  calc
    holonomicGaugeCurvature (LocalCandidate point) 0 =
        holonomicGaugeCurvature (ProxyCandidate point) 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq
        (LocalCandidate point) (ProxyCandidate point)
        (localCandidate_gaugeConnection_eq_proxyCandidate point) 0
    _ = holonomicGaugeCurvature (ProxyRecenter point) 0 := by
      exact installSecondJet_gaugeCurvature_origin
        (ProxyRecenter point) (proxyRecenter_smooth point)
        (p286CanonicalDiagonalResponseSecondJet (LocalWrite point)) 1
    _ = holonomicGaugeCurvature SmoothGaugeProxy point :=
      fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
        SmoothGaugeProxy point
    _ = holonomicGaugeCurvature Coupled point := by
      exact
        (holonomicGaugeCurvature_eq_of_connection_eq Coupled SmoothGaugeProxy
          coupled_gaugeConnection_eq_smoothGaugeProxy point).symm

private theorem localAlgebraic_gaugeCurvature_origin_eq_coupled
    (point : BasePoint) :
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Coupled point)) 0 =
      holonomicGaugeCurvature Coupled point := by
  calc
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Coupled point)) 0 =
        holonomicGaugeCurvature (LocalCandidate point) 0 := by
      apply holonomicGaugeCurvature_eq_of_connection_eq
      rfl
    _ = holonomicGaugeCurvature Coupled point :=
      localCandidate_gaugeCurvature_origin_eq_coupled point

/-- At every action-selected occurrence, the local algebraic P286 leg keeps
the exact gauge curvature of the same coupled whole-field input at its
recentered origin.  This is a first-jet custody theorem, not a supplied
curvature seam. -/
theorem actionSelectedCoupled_localAlgebraic_gaugeCurvature_origin_eq
    (point : BasePoint) :
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
          (fullyRecenterHolonomicConfiguration
            (completeJointActionSelectedCoupledTemporalActual
              positiveSmoothUnifiedSource
              fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
            point)) 0 =
      holonomicGaugeCurvature
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
        point := by
  exact localAlgebraic_gaugeCurvature_origin_eq_coupled point

private theorem canonical_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem localLiveElectric_gaugeAuxiliary_origin_eq_algebraic
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration Coupled point)
      ).gaugeAuxiliary 0 =
      (completeJointGlobalP286AlgebraicCurrent Source
        (fullyRecenterHolonomicConfiguration Coupled point)
      ).gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  have zeroSliceEquality := congrFun
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
      Source (fullyRecenterHolonomicConfiguration Coupled point)
      (0 : StageNineSpatialPoint)) pair
  simpa only [canonical_zero,
    holonomicP286GaugeAuxiliaryCoordinate] using zeroSliceEquality

/-- The common successor's P286 auxiliary is the constitutive field computed
from the same coupled input.  This is a whole-field producer readback, not a
pointwise supplied equation. -/
private theorem successor_gaugeAuxiliary_eq_constitutive :
    Successor.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source Coupled := by
  funext point
  change
    (completeJointLiveElectricECFullOccurrenceContact Source Coupled point
      ).gaugeAuxiliary 0 =
      diracDualFormNativeConstitutiveAuxiliaryField Source Coupled point
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary]
  calc
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration Coupled point)
      ).gaugeAuxiliary 0 =
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Coupled point)
        ).gaugeAuxiliary 0 :=
      localLiveElectric_gaugeAuxiliary_origin_eq_algebraic point
    _ = diracDualFormNativeConstitutiveAuxiliaryField Source Coupled point := by
      rw [← completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary]
      unfold diracDualFormNativeConstitutiveAuxiliaryField
      have coframeEq :
          (completeJointGlobalP286AlgebraicCurrent Source
            (fullyRecenterHolonomicConfiguration Coupled point)
          ).coframe 0 = Coupled.coframe point := by
        change
          (fullyRecenterHolonomicConfiguration Coupled point).coframe 0 =
            Coupled.coframe point
        exact
          fullyRecenterHolonomicConfiguration_coframe_origin Coupled point
      rw [coframeEq, localAlgebraic_gaugeCurvature_origin_eq_coupled]

private theorem coupled_gaugeAuxiliary_eq_constitutive :
    Coupled.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source Coupled := by
  funext point
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Radial.coframe point) (holonomicGaugeCurvature Radial point) =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Coupled.coframe point) (holonomicGaugeCurvature Coupled point)
  have coframeEq : Coupled.coframe = Radial.coframe := by
    rfl
  have connectionEq : Coupled.gaugeConnection = Radial.gaugeConnection := by
    rfl
  rw [congrFun coframeEq point]
  rw [holonomicGaugeCurvature_eq_of_connection_eq Coupled Radial
    connectionEq point]

/-- The final five-leg compiler preserves the already generated constitutive
auxiliary of its coupled input as one whole field. -/
private theorem successor_gaugeAuxiliary_eq_coupled :
    Successor.gaugeAuxiliary = Coupled.gaugeAuxiliary :=
  successor_gaugeAuxiliary_eq_constitutive.trans
    coupled_gaugeAuxiliary_eq_constitutive.symm

/-- All primitive fields read by the P286 connection equation agree between
the coupled action output and the common successor. -/
private theorem successor_p286EulerThreeForm_eq_coupled :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Coupled := by
  apply holonomicFormNativeP286GaugeEulerThreeForm_eq_of_primitiveFields
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source Coupled
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection
        Source Coupled
  · exact successor_gaugeAuxiliary_eq_coupled
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
        Source Coupled
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
        Source Coupled
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
        Source Coupled

/-- Explicit whole-field P286 auxiliary custody for the fixed action-selected
successor.  The statement exposes only public source/current expressions. -/
theorem successor_gaugeAuxiliary_eq_actionSelectedCoupledConstitutive :
    fixedP506L0LorentzPathActionSelectedJointSuccessor.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField
        positiveSmoothUnifiedSource
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual) := by
  exact successor_gaugeAuxiliary_eq_constitutive

/-- The complete P286 connection read of the fixed successor is the read of
the same action-selected coupled input. -/
theorem successor_p286EulerThreeForm_eq_actionSelectedCoupled :
    holonomicFormNativeP286GaugeEulerThreeForm
        positiveSmoothUnifiedSource 0
        fixedP506L0LorentzPathActionSelectedJointSuccessor =
      holonomicFormNativeP286GaugeEulerThreeForm
        positiveSmoothUnifiedSource 0
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual) := by
  exact successor_p286EulerThreeForm_eq_coupled

/-- The source/current-only five-leg compiler preserves the settled P286
read of its action-selected coupled input.  Hence the one common successor
has zero `(123)` connection residual at every canonical zero-slice point. -/
theorem successor_p286Euler123_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
        (canonicalCauchySlicePoint 0 space) 3 = 0 := by
  rw [congrFun successor_p286EulerThreeForm_eq_coupled
    (canonicalCauchySlicePoint 0 space)]
  exact coupled_p286Euler123_zeroSlice space

/-! ## Complete zero-slice P286 support -/

/-- Difference of the two positive P286 geometric action reads that remain
after the selected radial and coupled temporal writes.  This is a diagnostic
three-form assembled after both actuals exist; it is never an input to the
connection writer. -/
def successorP286GeometricDeltaZeroSlice
    (space : StageNineSpatialPoint) : P286GaugeThreeForm :=
  let point := canonicalCauchySlicePoint 0 space
  holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Constitutive point -
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Algebraic point

/-- On the whole canonical zero slice, the action-selected constitutive
auxiliary has the exact required exterior first jet.  Exact commutation of
the inherited Gauss charge with the mother-action charge kills both
connection-action channels, so the full geometric changed read is precisely
the negative radial Euler three-form. -/
theorem successorP286GeometricDeltaZeroSlice_eq_neg_radial
    (space : StageNineSpatialPoint) :
    successorP286GeometricDeltaZeroSlice space =
      -(p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
        p286SpatialVolumeGaugeThreeForm
          fixedP506L0U6OccurrenceP286MotherActionCharge) := by
  dsimp [successorP286GeometricDeltaZeroSlice]
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    constitutive_connectionExteriorAction_zeroSlice,
    algebraic_connectionExteriorAction_zero,
    add_zero, add_zero,
    constitutive_exteriorDerivative_eq_requiredExteriorAnchor_zeroSlice,
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_exteriorDerivative_eq_directRequired,
    pointwiseDirectP286RequiredExteriorDerivative_eq_exterior_sub_euler,
    fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm]
  module

/-- The complete successor P286 read is the known mother-action radial
three-form plus the exact geometric changed read of the same occurrence. -/
theorem successor_p286EulerThreeForm_zeroSlice_eq_radial_add_geometricDelta
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
        (canonicalCauchySlicePoint 0 space) =
      p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
          p286SpatialVolumeGaugeThreeForm
            fixedP506L0U6OccurrenceP286MotherActionCharge +
        successorP286GeometricDeltaZeroSlice space := by
  let point := canonicalCauchySlicePoint 0 space
  calc
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor point =
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Coupled point := by
      exact congrFun successor_p286EulerThreeForm_eq_coupled point
    _ = holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point +
        successorP286GeometricDeltaZeroSlice space := by
      unfold holonomicFormNativeP286GaugeEulerThreeForm
      rw [coupled_p286Geometric_eq_carry,
        coupled_chargedGaugeThreeForm_zeroSlice_eq_carry,
        carry_p286Geometric_eq_constitutive,
        carry_chargedGaugeThreeForm_zeroSlice_eq_algebraic]
      unfold successorP286GeometricDeltaZeroSlice
      module
    _ = _ := by
      rw [fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm]

/-- The source/current-only action-selected successor settles the complete
P286 Euler three-form on every point of the canonical zero slice.  This is a
whole-carrier producer-soundness theorem: the positive radial action read and
the exact constitutive geometric changed read cancel on the same actual. -/
theorem successor_p286EulerThreeForm_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
        (canonicalCauchySlicePoint 0 space) = 0 := by
  rw [successor_p286EulerThreeForm_zeroSlice_eq_radial_add_geometricDelta,
    successorP286GeometricDeltaZeroSlice_eq_neg_radial]
  module

/-- Exact mixed-support carrier of the remaining P286 read.  The spatial
volume coordinate has already been settled by the action-selected radial
principal; the three mixed coordinates retain the geometric delta. -/
def successorP286MixedZeroSliceSupport
    (space : StageNineSpatialPoint) : P286GaugeThreeForm :=
  let delta := successorP286GeometricDeltaZeroSlice space
  ![delta 0, delta 1, delta 2, 0]

theorem successor_p286EulerThreeForm_zeroSlice_eq_mixedSupport
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
        (canonicalCauchySlicePoint 0 space) =
      successorP286MixedZeroSliceSupport space := by
  funext triple
  fin_cases triple
  · have coordinate := congrFun
      (successor_p286EulerThreeForm_zeroSlice_eq_radial_add_geometricDelta
        space) 0
    simpa [successorP286MixedZeroSliceSupport,
      p286SpatialVolumeGaugeThreeForm] using coordinate
  · have coordinate := congrFun
      (successor_p286EulerThreeForm_zeroSlice_eq_radial_add_geometricDelta
        space) 1
    simpa [successorP286MixedZeroSliceSupport,
      p286SpatialVolumeGaugeThreeForm] using coordinate
  · have coordinate := congrFun
      (successor_p286EulerThreeForm_zeroSlice_eq_radial_add_geometricDelta
        space) 2
    simpa [successorP286MixedZeroSliceSupport,
      p286SpatialVolumeGaugeThreeForm] using coordinate
  · simpa [successorP286MixedZeroSliceSupport] using
      successor_p286Euler123_zeroSlice space

/-- Complete P286 zero-fiber criterion on the same successor.  It exposes
three exact mixed geometric reads instead of silently extrapolating the
already settled `(123)` component. -/
theorem successor_p286EulerThreeForm_zeroSlice_eq_zero_iff_mixedDelta_zero
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
        (canonicalCauchySlicePoint 0 space) = 0 ↔
      successorP286GeometricDeltaZeroSlice space 0 = 0 ∧
        successorP286GeometricDeltaZeroSlice space 1 = 0 ∧
        successorP286GeometricDeltaZeroSlice space 2 = 0 := by
  rw [successor_p286EulerThreeForm_zeroSlice_eq_mixedSupport]
  constructor
  · intro supportZero
    exact ⟨
      by
        simpa [successorP286MixedZeroSliceSupport] using
          congrFun supportZero 0,
      by
        simpa [successorP286MixedZeroSliceSupport] using
          congrFun supportZero 1,
      by
        simpa [successorP286MixedZeroSliceSupport] using
          congrFun supportZero 2⟩
  · rintro ⟨zero0, zero1, zero2⟩
    funext triple
    fin_cases triple <;>
      simp [successorP286MixedZeroSliceSupport, zero0, zero1, zero2]

/-! ## Public regularity of the action-selected temporal input

These are exact fixed-lineage readouts of the `Carry` current used by the
coupled temporal producer.  They expose no residual or target derivative;
the downstream matter/adjoint acceptance module uses them only to
differentiate the already generated canonical primitives. -/

/-- The action-selected scalar carry is the same source/action-generated
scalar primitive as the earlier radial-quartic carry.  This is a primitive
field comparison, not a transfer of any residual or closure receipt. -/
theorem actionSelectedCarry_scalar_eq_u6RadialQuarticCarry :
    (completeJointActionSelectedScalarMomentumCarryActual
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
    ).scalar =
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar := by
  exact carry_scalar_eq_old

/-- The action-selected and earlier radial-quartic carries retain the same
source-generated P286 connection primitive. -/
theorem actionSelectedCarry_gaugeConnection_eq_u6RadialQuarticCarry :
    (completeJointActionSelectedScalarMomentumCarryActual
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
    ).gaugeConnection =
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeConnection := by
  exact carry_gaugeConnection_eq_oldCarry

/-- The fixed action-selected carry exposes its source-generated P286
connection on the canonical time axis.  The radial-quartic increment vanishes
there, leaving the exact same-lineage action primitive; no connection target
or comparison datum is accepted from the caller. -/
theorem actionSelectedCarry_gaugeConnectionCoordinate_timeAxis_normalForm
    (time : ℝ) (direction : LorentzianIndex) :
    p286CoordinateEquiv
        ((completeJointActionSelectedScalarMomentumCarryActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
        ).gaugeConnection
          (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
          direction) =
      (-c3h181FullConnectionCoefficient
          (-(canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)))
          direction) •
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  change p286CoordinateEquiv
      (Carry.gaugeConnection (canonicalCauchySlicePoint time 0) direction) = _
  have normal := constitutive_connectionCoordinate_normalForm
    (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) direction
  change p286CoordinateEquiv
      (Carry.gaugeConnection (canonicalCauchySlicePoint time 0) direction) =
        (-c3h181FullConnectionCoefficient
            (-(canonicalCauchySlicePoint time 0)) direction) •
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge +
          p286RadialQuarticTemporalConnection
            fixedP506L0U6OccurrenceP286MotherActionCharge
            (canonicalCauchySlicePoint time 0) direction at normal
  rw [normal]
  simp [p286RadialQuarticTemporalConnection,
    p286SpatialRadialQuarticCoefficient, p286SpatialRadiusSquared,
    p286SpatialMetricCovectorOperator, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- On the canonical zero slice the action-selected constitutive auxiliary
is the same source/action-generated primitive as the earlier radial-quartic
carry.  This exposes a retained primitive field, not an Euler receipt. -/
theorem actionSelectedCarry_gaugeAuxiliary_zeroSlice_eq_u6RadialQuarticCarry
    (space : StageNineSpatialPoint) :
    (completeJointActionSelectedScalarMomentumCarryActual
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
    ).gaugeAuxiliary (canonicalCauchySlicePoint 0 space) =
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) := by
  change
    Constitutive.gaugeAuxiliary (canonicalCauchySlicePoint 0 space) =
      OldConstitutive.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space)
  exact constitutive_auxiliary_zeroSlice_eq_old space

/-- On the canonical zero slice the two source/action-generated carries have
the same coframe, primal matter, and independent-adjoint point data. -/
theorem actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry
    (space : StageNineSpatialPoint) :
    (completeJointActionSelectedScalarMomentumCarryActual
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
    ).coframe (canonicalCauchySlicePoint 0 space) =
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual.coframe
          (canonicalCauchySlicePoint 0 space) ∧
      (completeJointActionSelectedScalarMomentumCarryActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
      ).matter (canonicalCauchySlicePoint 0 space) =
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual.matter
          (canonicalCauchySlicePoint 0 space) ∧
      (completeJointActionSelectedScalarMomentumCarryActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
      ).conjugateMatter (canonicalCauchySlicePoint 0 space) =
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual.conjugateMatter
          (canonicalCauchySlicePoint 0 space) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [carry_coframe_zeroSlice_eq_algebraic,
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_eq_algebraic]
  · rw [carry_matter_zeroSlice_eq_algebraic,
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic]
  · rw [carry_conjugateMatter_zeroSlice_eq_algebraic,
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic]

theorem actionSelectedCarry_coframe_eq_one :
    (completeJointActionSelectedScalarMomentumCarryActual
      positiveSmoothUnifiedSource
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
    ).coframe = fun _ => (1 : LorentzianCoframe) := by
  exact carry_coframe_eq_one

theorem actionSelectedCarry_scalar_contDiff :
    ContDiff ℝ ∞
      (completeJointActionSelectedScalarMomentumCarryActual
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
      ).scalar := by
  exact carry_scalar_contDiff

theorem actionSelectedCarry_matterCoordinates_contDiff :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        ((completeJointActionSelectedScalarMomentumCarryActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
        ).matter point) := by
  exact carry_matterCoordinates_contDiff

theorem actionSelectedCarry_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (completeJointActionSelectedScalarMomentumCarryActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)) := by
  exact carry_conjugateMatterCoordinates_contDiff

theorem actionSelectedCarry_gaugeConnectionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        ((completeJointActionSelectedScalarMomentumCarryActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
        ).gaugeConnection point direction) := by
  exact carry_gaugeConnectionCoordinate_contDiff direction

/-- The prior Lorentz-path five-leg successor remains the explicit negative
regression, while the action-selected common successor settles that exact
unit-spatial changed read. -/
theorem actionSelected_successor_settles_prior_unitSpatial_p286Read :
    (diracDualFormNativePointwiseJointResidual Source
        fixedP506L0LorentzPathFiveLegSuccessor
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1))
      ).p286GaugeConnection ≠ 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Successor
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1))
      ).p286GaugeConnection 3 = 0 := by
  constructor
  · exact
      fixedP506L0LorentzPathFiveLegSuccessor_p286GaugeConnection_unitSpatial_ne_zero
  · change
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) 3 = 0
    exact successor_p286Euler123_zeroSlice (EuclideanSpace.single 0 1)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
