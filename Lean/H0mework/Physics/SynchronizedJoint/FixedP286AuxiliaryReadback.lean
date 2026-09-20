import H0mework.Physics.SynchronizedJoint.FixedActionJetNaturality
import H0mework.Physics.JointVariation.SectionFixedP286AuxiliaryResidual
import H0mework.Physics.JointVariation.SectionFixedGlobalRegularity
import H0mework.Physics.FinalJoint.FixedP286AffineIdentification
import H0mework.Physics.FixedJoint.FixedP286RequiredExteriorDerivativeSpatialRegularity
import H0mework.Physics.ActionForcing.FixedOccurrenceP286ZeroSliceActionProfile

/-!
# Fixed synchronized Lorentz-path P286 auxiliary readback

The exact four-leg source/current occurrence has already emitted one global
actual.  This module reads its P286 auxiliary Euler channel without changing
that actual.  The source-owned identity coframe and the retained P506 gauge
connection/auxiliary close the complete time axis; occurrence naturality and
the solved zero-slice contact law close the complete Cauchy slice.

These theorems isolate any still-unsettled all-point responsibility to a
genuine mixed spacetime assembly term.  No residual coordinate, support,
target field, branch, or zero-fiber witness enters an action writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506P286AuxiliaryResidual
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionJetNaturality
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506P286RequiredExteriorDerivativeSpatialRegularity
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor
private abbrev Raw : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual
private abbrev Base : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- The synchronized Lorentz-path occurrence retains the complete primitive
P286 connection emitted by the fixed solved input. -/
theorem final_gaugeConnection_eq_input :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeConnection =
      FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection := by
  calc
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeConnection =
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.gaugeConnection := by
      rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
      exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gaugeConnection
          Source Input
    _ = fixedP506L0CompleteJointActionSpacetimeSectionActual.gaugeConnection := by
      rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite]
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
          Source fixedP506L0CompleteJointActionSpacetimeSectionActual 0
    _ = FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
        Source Input

/-- The synchronized Lorentz-path and gravity-reaction legs retain the
whole-section P286 auxiliary field exactly. -/
theorem final_gaugeAuxiliary_eq_raw :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeAuxiliary =
      fixedP506L0CompleteJointActionSpacetimeSectionActual.gaugeAuxiliary := by
  calc
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeAuxiliary =
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.gaugeAuxiliary := by
      rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
      exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gaugeAuxiliary
          Source Input
    _ = fixedP506L0CompleteJointActionSpacetimeSectionActual.gaugeAuxiliary := by
      rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite]
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
          Source fixedP506L0CompleteJointActionSpacetimeSectionActual 0

private theorem final_gaugeAuxiliary_timeAxis_eq_input
    (time : ℝ) :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeAuxiliary
        (canonicalCauchySlicePoint time 0) =
      FixedP506FormNativeJointActionSolvedSuccessor.gaugeAuxiliary
        (canonicalCauchySlicePoint time 0) := by
  calc
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeAuxiliary
          (canonicalCauchySlicePoint time 0) =
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.gaugeAuxiliary
          (canonicalCauchySlicePoint time 0) := by
      rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite]
      exact congrFun
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gaugeAuxiliary
          Source Input)
        (canonicalCauchySlicePoint time 0)
    _ = fixedP506L0CompleteJointActionSpacetimeSectionActual.gaugeAuxiliary
          (canonicalCauchySlicePoint time 0) := by
      rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite]
      exact congrFun
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeAuxiliary
          Source fixedP506L0CompleteJointActionSpacetimeSectionActual 0)
        (canonicalCauchySlicePoint time 0)
    _ = (fixedP506L0FinalCommonActionActual 0).gaugeAuxiliary
          (canonicalCauchySlicePoint time 0) := by
      change
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
          Source Input).gaugeAuxiliary (canonicalCauchySlicePoint time 0) = _
      rw [sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeAuxiliary_at]
      change
        (fixedP506L0CompleteJointActionMatchingContact
          (canonicalCauchySlicePoint time 0)).gaugeAuxiliary
            (completeJointActionMatchingContactPoint
              (canonicalCauchySlicePoint time 0)) = _
      rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon]
      simp [completeJointActionMatchingContactPoint]
    _ = FixedP506FormNativeJointActionSolvedSuccessor.gaugeAuxiliary
          (canonicalCauchySlicePoint time 0) := by
      rw [fixedP506L0FinalCommonActionActual_gaugeAuxiliary_eq_solved]

private theorem fixedSource_blockwiseCoupling_same
    (parameter : ℝ) (coordinate : P286CoordinateCarrier) :
    formNativeP286BlockwiseCouplingCoordinateLinear
        parameter parameter parameter coordinate =
      parameter • coordinate := by
  apply p286CoordinateEquiv.symm.injective
  simp [formNativeP286BlockwiseCouplingCoordinateLinear,
    formNativeP286BlockwiseCouplingActualLinear]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

private theorem fixedSource_blockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe
        ((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings Source).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings Source).hyperchargeCouplingSquared : ℝ)
        form =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form := by
  have weakEq :
      ((sourceGeneratedUnifiedCouplings Source).weakCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ) := by
    rfl
  have hyperchargeEq :
      ((sourceGeneratedUnifiedCouplings Source).hyperchargeCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ) := by
    rfl
  rw [weakEq, hyperchargeEq,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum,
    liftGaugeTwoFormOperator_smul_operator_p286]
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  simp_rw [fixedSource_blockwiseCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

theorem final_p286AuxiliaryResidualCoordinate_timeAxis_zero
    (time : ℝ) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings Source) Final
        (canonicalCauchySlicePoint time 0) = 0 := by
  rw [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_eq]
  rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
  rw [fixedSource_blockwiseConstitutive_eq_unified]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    Final Input final_gaugeConnection_eq_input]
  change
    holonomicP286GaugeCurvatureCoordinate Input
        (canonicalCauchySlicePoint time 0) -
      liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (holonomicP286GaugeAuxiliaryCoordinate Final
            (canonicalCauchySlicePoint time 0)) = 0
  rw [fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm]
  rw [show
      holonomicP286GaugeAuxiliaryCoordinate Final
          (canonicalCauchySlicePoint time 0) =
        holonomicP286GaugeAuxiliaryCoordinate Input
          (canonicalCauchySlicePoint time 0) by
    funext pair
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [final_gaugeAuxiliary_timeAxis_eq_input]]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm]
  rw [c3h181FullAuxiliary_hodge_eq_curvature]
  simp

theorem final_p286AuxiliaryResidual_timeAxis_zero
    (time : ℝ) :
    (diracDualFormNativePointwiseJointResidual Source Final
      (canonicalCauchySlicePoint time 0)).p286GaugeAuxiliary = 0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField Final (canonicalCauchySlicePoint time 0)) = 0
  funext pair
  apply p286CoordinateEquiv.injective
  have coordinate := congrFun
    (final_p286AuxiliaryResidualCoordinate_timeAxis_zero time) pair
  simpa [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate,
    formNativeP286GaugeActualToCoordinateLinear] using coordinate

theorem final_p286AuxiliaryResidual_zeroSlice_zero
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Final
      (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have rawZero :
      (diracDualFormNativePointwiseJointResidual Source Raw point
        ).p286GaugeAuxiliary = 0 := by
    have matching :=
      fixedP506L0CompleteJointActionSpacetimeSection_p286GaugeAuxiliary_eq_matching
        point
    have contactZero := congrArg
      (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
        residual.p286GaugeAuxiliary)
      (fixedP506L0CompleteJointActionMatchingContact_residual_origin_zero point)
    rw [show completeJointActionMatchingContactPoint point = 0 by
      simp [point, completeJointActionMatchingContactPoint,
        canonicalCauchySlicePoint_zero_zero_local]] at matching
    exact matching.trans contactZero
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField Final point) = 0
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField Raw point) = 0 at rawZero
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary at ⊢ rawZero
  simp only [toContinuumPointField] at ⊢ rawZero
  rw [show Final.coframe point = Raw.coframe point by
    rw [fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one]
    change (1 : LorentzianCoframe) = Raw.coframe point
    rw [show Raw.coframe = Input.coframe by
      exact
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe
          Source Input]
    exact
      (fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
        space).symm]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    Final Raw
    (final_gaugeConnection_eq_input.trans
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
        Source Input).symm)]
  rw [final_gaugeAuxiliary_eq_raw]
  exact rawZero

private theorem final_gaugeAuxiliaryCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate Final point =
      currentP286OriginAuxiliaryCoordinate
          (recenteredCartanRepairedScalarSecondJetActual
            (canonicalSpatialProjection point)) +
        formNativeP286CanonicalAuxiliaryIncrement
          (formNativeCurrentP286RequiredExteriorDerivative Source
            (recenteredCartanRepairedScalarSecondJetActual
              (canonicalSpatialProjection point)))
          (completeJointActionMatchingContactPoint point) := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [final_gaugeAuxiliary_eq_raw]
  exact
    fixedP506L0CompleteJointActionSpacetimeSection_gaugeAuxiliary_normalForm
      point

private theorem final_gaugeCurvatureCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate Final point =
      c3h181FullCurvatureCoordinateNormalForm (-point) := by
  unfold holonomicP286GaugeCurvatureCoordinate
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    Final Input final_gaugeConnection_eq_input point]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm
      point

theorem final_p286AuxiliaryResidualCoordinate_zeroSlice_zero
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings Source) Final
        (canonicalCauchySlicePoint 0 space) = 0 := by
  unfold holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
  change
    formNativeP286GaugeActualToCoordinateLinear
      ((diracDualFormNativePointwiseJointResidual Source Final
        (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary) = 0
  rw [final_p286AuxiliaryResidual_zeroSlice_zero]
  exact map_zero formNativeP286GaugeActualToCoordinateLinear

/-- Exact remaining P286 auxiliary assembly term after the already proved
time-axis and zero-slice cancellations.  It is computed from the emitted
fields and the action-owned required exterior profile; it is not accepted by
any writer. -/
def fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  c3h181FullCurvatureCoordinateNormalForm (-point) -
    c3h181FullCurvatureCoordinateNormalForm
      (-(canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))) -
    liftGaugeTwoFormOperator
      (c3h181StrongCouplingSquared • coframeGaugeSpacetimeHodgeLinear 1)
      (formNativeP286CanonicalAuxiliaryIncrement
        (formNativeCurrentP286RequiredExteriorDerivative Source
          (recenteredCartanRepairedScalarSecondJetActual
            (canonicalSpatialProjection point)))
        (completeJointActionMatchingContactPoint point))

/-- Whole-channel all-point normal form.  Since both coordinate hyperplanes
already vanish, every possible remaining support is displayed by the one
mixed assembly term above. -/
theorem final_p286AuxiliaryResidualCoordinate_mixedAssembly_normalForm
    (point : BasePoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings Source) Final point =
      fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm point := by
  let zeroPoint :=
    canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)
  have zeroResidual :=
    final_p286AuxiliaryResidualCoordinate_zeroSlice_zero
      (canonicalSpatialProjection point)
  change
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings Source) Final zeroPoint = 0
      at zeroResidual
  rw [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_eq,
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_coframe_eq_one,
    fixedSource_blockwiseConstitutive_eq_unified] at zeroResidual ⊢
  change
    holonomicP286GaugeCurvatureCoordinate Final point -
        liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (holonomicP286GaugeAuxiliaryCoordinate Final point) = _
  change
    holonomicP286GaugeCurvatureCoordinate Final zeroPoint -
        liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (holonomicP286GaugeAuxiliaryCoordinate Final zeroPoint) = 0
      at zeroResidual
  rw [final_gaugeCurvatureCoordinate_normalForm,
    final_gaugeAuxiliaryCoordinate_normalForm] at zeroResidual ⊢
  have zeroSpatial :
      canonicalSpatialProjection zeroPoint =
        canonicalSpatialProjection point := by
    simp [zeroPoint]
  rw [zeroSpatial] at zeroResidual
  change
    c3h181FullCurvatureCoordinateNormalForm (-point) -
        liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (currentP286OriginAuxiliaryCoordinate
              (recenteredCartanRepairedScalarSecondJetActual
                (canonicalSpatialProjection point)) +
            formNativeP286CanonicalAuxiliaryIncrement
              (formNativeCurrentP286RequiredExteriorDerivative Source
                (recenteredCartanRepairedScalarSecondJetActual
                  (canonicalSpatialProjection point)))
              (completeJointActionMatchingContactPoint point)) = _
  change
    c3h181FullCurvatureCoordinateNormalForm (-zeroPoint) -
        liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (currentP286OriginAuxiliaryCoordinate
              (recenteredCartanRepairedScalarSecondJetActual
                (canonicalSpatialProjection point)) +
            formNativeP286CanonicalAuxiliaryIncrement
              (formNativeCurrentP286RequiredExteriorDerivative Source
                (recenteredCartanRepairedScalarSecondJetActual
                  (canonicalSpatialProjection point)))
              (completeJointActionMatchingContactPoint zeroPoint)) = 0
      at zeroResidual
  have matchingZero : completeJointActionMatchingContactPoint zeroPoint = 0 := by
    simp [zeroPoint, completeJointActionMatchingContactPoint,
      canonicalCauchySlicePoint_zero_zero_local]
  rw [matchingZero] at zeroResidual
  simp [formNativeP286CanonicalAuxiliaryIncrement] at zeroResidual
  have originEq :
      liftGaugeTwoFormOperator
          (c3h181StrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (currentP286OriginAuxiliaryCoordinate
            (recenteredCartanRepairedScalarSecondJetActual
              (canonicalSpatialProjection point))) =
        c3h181FullCurvatureCoordinateNormalForm (-zeroPoint) :=
    (sub_eq_zero.mp zeroResidual).symm
  unfold fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm
  rw [liftGaugeTwoFormOperator_add_p286]
  rw [originEq]
  module

private theorem canonicalAuxiliaryIncrement_timeAxis_smul
    (target : P286GaugeThreeForm)
    (time : ℝ) :
    formNativeP286CanonicalAuxiliaryIncrement target
        (canonicalCauchySlicePoint time 0) =
      time •
        formNativeP286CanonicalAuxiliaryIncrement target
          (canonicalCauchySlicePoint 1 0) := by
  funext pair
  fin_cases pair <;>
    simp [formNativeP286CanonicalAuxiliaryIncrement,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      localBaseCoordinate_apply, Fin.sum_univ_four]

private theorem curvatureNormalForm_timeDifference_smul
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    c3h181FullCurvatureCoordinateNormalForm
          (-(canonicalCauchySlicePoint time space)) -
        c3h181FullCurvatureCoordinateNormalForm
          (-(canonicalCauchySlicePoint 0 space)) =
      time •
        (c3h181FullCurvatureCoordinateNormalForm
              (-(canonicalCauchySlicePoint 1 space)) -
          c3h181FullCurvatureCoordinateNormalForm
            (-(canonicalCauchySlicePoint 0 space))) := by
  funext pair
  fin_cases pair <;>
    simp [c3h181FullCurvatureCoordinateNormalForm,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three];
    module

/-- The spatial profile of the only possible mixed P286 auxiliary support.
It is a downstream read of the exact action-owned exterior profile. -/
def fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeCoordinateTwoForm :=
  fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm
    (canonicalCauchySlicePoint 1 space)

theorem fixedP506L0LorentzPathP286AuxiliaryMixedAssembly_factorization
    (point : BasePoint) :
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm point =
      canonicalTimeProjection point •
        fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient
          (canonicalSpatialProjection point) := by
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  have pointEq : point = canonicalCauchySlicePoint time space := by
    exact (canonicalCauchySlicePoint_projections point).symm
  rw [pointEq]
  unfold fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient
  simp only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    completeJointActionMatchingContactPoint]
  rw [curvatureNormalForm_timeDifference_smul]
  rw [canonicalAuxiliaryIncrement_timeAxis_smul]
  rw [liftGaugeTwoFormOperator_smul_p286]
  unfold fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm
  simp only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    completeJointActionMatchingContactPoint]
  module

/-- Faithful three-coordinate display of the mixed coefficient.  Only the
time-row components `012`, `013`, and `023` of the action-required exterior
profile can contribute. -/
def fixedP506L0LorentzPathP286AuxiliaryRequiredTimeMismatchNormalForm
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeCoordinateTwoForm :=
  let required :=
    formNativeCurrentP286RequiredExteriorDerivative Source
      (recenteredCartanRepairedScalarSecondJetActual space)
  ![
    -(c3h181StrongCouplingSquared • required 2),
    c3h181StrongCouplingSquared • required 1,
    c3h181StrongCouplingSquared •
      (positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge - required 0),
    0, 0, 0
  ]

theorem
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient_normalForm
    (space : StageNineSpatialPoint) :
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient space =
      fixedP506L0LorentzPathP286AuxiliaryRequiredTimeMismatchNormalForm
        space := by
  unfold fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyNormalForm
    fixedP506L0LorentzPathP286AuxiliaryRequiredTimeMismatchNormalForm
  simp only [canonicalSpatialProjection_slice, canonicalTimeProjection_slice,
    completeJointActionMatchingContactPoint]
  rw [liftGaugeTwoFormOperator_smul_operator_p286,
    StageNineResidualLimitCoframeBalanceDecision.coframeGaugeSpacetimeHodgeLinear_one]
  rw [show
    EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv.toLinearMap =
      lorentzianCoframeHodge by rfl]
  funext pair
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [liftGaugeTwoFormOperator_fixedHodge_apply_local]
  fin_cases pair <;>
    simp [c3h181FullCurvatureCoordinateNormalForm,
      formNativeP286CanonicalAuxiliaryIncrement,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      localBaseCoordinate_apply, Fin.sum_univ_four];
    module

theorem final_p286AuxiliaryResidualCoordinate_factorization
    (point : BasePoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings Source) Final point =
      canonicalTimeProjection point •
        fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient
          (canonicalSpatialProjection point) := by
  rw [final_p286AuxiliaryResidualCoordinate_mixedAssembly_normalForm,
    fixedP506L0LorentzPathP286AuxiliaryMixedAssembly_factorization]

/-- The exact source/current required profile has the unique time-row normal
form consumed by the synchronized whole-field write.  The spatial-volume
entry remains visible, but it cannot enter the mixed assembly coefficient. -/
theorem final_requiredExteriorDerivative_zeroSlice_normalForm
    (space : StageNineSpatialPoint) :
    formNativeCurrentP286RequiredExteriorDerivative Source
        (recenteredCartanRepairedScalarSecondJetActual space) =
      ![positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
        0, 0,
        -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge -
          p286SpatialRadiusSquared (canonicalCauchySlicePoint 0 space) •
            fixedP506L0U6OccurrenceP286MotherActionCharge] := by
  rw [
    fixedP506L0RecenteredCartanRequiredExteriorDerivative_eq_fixedInputDirect_zeroSlice,
    fixedP506L0_FixedInput_pointwiseDirectRequiredExterior_zeroSlice_normalForm]

/-- The mixed assembly coefficient vanishes identically.  This is a
same-actual consistency readback of the source/action-generated profile, not
a coefficient supplied to the global writer. -/
theorem fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient_zero
    (space : StageNineSpatialPoint) :
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient space = 0 := by
  rw [fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient_normalForm]
  unfold fixedP506L0LorentzPathP286AuxiliaryRequiredTimeMismatchNormalForm
  rw [final_requiredExteriorDerivative_zeroSlice_normalForm]
  funext pair
  fin_cases pair <;> simp

/-- All-point closure of the P286 auxiliary coordinate on the one emitted
global actual. -/
theorem final_p286AuxiliaryResidualCoordinate_allPoint_zero
    (point : BasePoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings Source) Final point = 0 := by
  rw [final_p286AuxiliaryResidualCoordinate_factorization,
    fixedP506L0LorentzPathP286AuxiliaryMixedAssemblyCoefficient_zero,
    smul_zero]

/-- Carrier-level all-point P286 auxiliary zero on that same actual. -/
theorem final_p286AuxiliaryResidual_allPoint_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Final point
      ).p286GaugeAuxiliary = 0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField Final point) = 0
  funext pair
  apply p286CoordinateEquiv.injective
  have coordinate := congrFun
    (final_p286AuxiliaryResidualCoordinate_allPoint_zero point) pair
  simpa [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate,
    formNativeP286GaugeActualToCoordinateLinear] using coordinate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback
