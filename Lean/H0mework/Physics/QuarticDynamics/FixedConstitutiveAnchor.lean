import H0mework.Physics.FixedJoint.FixedP286RadialRequiredExteriorAnchor
import H0mework.Physics.FullOccurrence.FixedP286Verdict
import H0mework.Physics.ActionForcing.FixedConnectionRelativeScalarSettlement
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport

/-!
# Fixed U6 radial-quartic constitutive anchor

The fixed mother-action charge generates a radial-quartic temporal P286
connection on the literal U6 lineage.  On the complete canonical zero slice,
its six-coordinate curvature increment is the fixed-source constitutive image
of the negative radial Euler auxiliary primitive.  Consequently the live
constitutive readout of that connection is exactly the committed corrected
required-exterior anchor, and the same actual satisfies `F = K_e B` there.

The construction consumes only the fixed source/current action data.  It
accepts no residual coordinate, target field, endpoint shell, branch, or
equation receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506P286RadialRequiredExteriorAnchor
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506U6ConnectionRelativeScalarSettlement
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineResidualLimitCoframeBalanceDecision
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance radialJointP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance radialJointP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance radialJointP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Charge : P286CoordinateCarrier :=
  fixedP506L0U6OccurrenceP286MotherActionCharge

def fixedP506L0U6RadialQuarticConnectionActual :
    StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate U6
    (p286RadialQuarticTemporalConnection Charge) 1

def fixedP506L0U6RadialQuarticConstitutiveActual :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveWrittenCurrent Source
    fixedP506L0U6RadialQuarticConnectionActual

private theorem u5_coframe_eq_algebraic :
    U5.coframe = Algebraic.coframe := by
  exact
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC.trans
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
        Source FixedInput)

private theorem u5_gaugeConnection_eq_algebraic :
    U5.gaugeConnection = Algebraic.gaugeConnection := by
  exact
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC.trans
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
        Source FixedInput)

theorem fixedP506L0U6_coframe_eq_algebraic :
    U6.coframe = Algebraic.coframe := by
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source U5).trans u5_coframe_eq_algebraic

theorem fixedP506L0U6_gaugeConnection_eq_algebraic :
    U6.gaugeConnection = Algebraic.gaugeConnection := by
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current.trans
      u5_gaugeConnection_eq_algebraic

theorem fixedP506L0Algebraic_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    Algebraic.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  change
    FixedInput.coframe (canonicalCauchySlicePoint 0 space) = 1
  simpa [FixedInput] using
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice space

private theorem algebraic_gaugeConnection_eq_fixedInput :
    Algebraic.gaugeConnection = FixedInput.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source
        (completeJointGlobalTemporalCurrent Source FixedInput) 0 by
    exact fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

theorem fixedP506L0U6_gaugeConnectionCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate U6 point =
      fixedP506FormNativeJointActionSolvedConnectionNormalForm point := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [fixedP506L0U6_gaugeConnection_eq_algebraic,
    algebraic_gaugeConnection_eq_fixedInput]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm point

private theorem fixedP506L0U6_gaugeConnectionCoordinate_zeroSlice_spatial
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    holonomicP286GaugeConnectionCoordinate U6
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  rw [fixedP506L0U6_gaugeConnectionCoordinate_normalForm]
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 space)) axis.succ
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line]
  fin_cases axis <;>
    simp [c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection]

/-! ## Exact six-coordinate curvature increment -/

/-- The ordinary curvature of the radial-quartic temporal connection has
support exactly in `(01,02,03)`. -/
def fixedP506L0U6RadialQuarticCurvatureIncrement
    (point : BasePoint) : P286GaugeTwoForm :=
  ![
    (-(p286SpatialRadiusSquared point * point 1 / 10 : ℝ)) • Charge,
    (-(p286SpatialRadiusSquared point * point 2 / 10 : ℝ)) • Charge,
    (-(p286SpatialRadiusSquared point * point 3 / 10 : ℝ)) • Charge,
    0, 0, 0]

private theorem fixedP506L0U6RadialQuarticConnection_coordinateDerivative
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        (p286RadialQuarticTemporalConnection Charge) point
        derivativeDirection formDirection =
      p286RadialQuarticTemporalFirstJet Charge point
        (coordinateDirection derivativeDirection) formDirection := by
  let evaluation : P286GaugeOneForm →L[ℝ] P286CoordinateCarrier :=
    ContinuousLinearMap.proj formDirection
  have derivative : HasFDerivAt
      (fun candidate =>
        evaluation (p286RadialQuarticTemporalConnection Charge candidate))
      (evaluation.comp
        (p286RadialQuarticTemporalFirstJet Charge point)) point := by
    exact evaluation.hasFDerivAt.comp point
      (p286RadialQuarticTemporalConnection_hasFDerivAt Charge point)
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  change
    (fderiv ℝ
      (fun candidate =>
        evaluation (p286RadialQuarticTemporalConnection Charge candidate))
      point) (coordinateDirection derivativeDirection) = _
  rw [derivative.fderiv]
  rfl

theorem fixedP506L0U6RadialQuarticConnection_exteriorDerivative
    (point : BasePoint) :
    (fun pair : Fin 6 =>
      p286GaugeVariationCoordinateDerivative
          (p286RadialQuarticTemporalConnection Charge) point
          (pairFirst pair) (pairSecond pair) -
        p286GaugeVariationCoordinateDerivative
          (p286RadialQuarticTemporalConnection Charge) point
          (pairSecond pair) (pairFirst pair)) =
      fixedP506L0U6RadialQuarticCurvatureIncrement point := by
  funext pair
  rw [fixedP506L0U6RadialQuarticConnection_coordinateDerivative,
    fixedP506L0U6RadialQuarticConnection_coordinateDerivative]
  fin_cases pair <;>
    simp [fixedP506L0U6RadialQuarticCurvatureIncrement,
      p286RadialQuarticTemporalFirstJet,
      p286TemporalConnectionJetEmbedding,
      p286SpatialRadialQuadraticScale,
      p286SpatialRadialCovector,
      p286SpatialMetricCovectorOperator,
      p286TemporalGaugeOneForm,
      p286SpatialRadiusSquared,
      p286BaseCoordinate_apply,
      coordinateDirection,
      canonicalLorentzianTimeDirection,
      pairFirst, pairSecond,
      Fin.sum_univ_three] <;>
    module

/-! ## Exact vanishing of the non-Abelian increments on the zero slice -/

/-- Both ordered background/radial cross brackets vanish on the full zero
slice by one-form support.  No identification of the old Gauss charge with
the mother-action charge is used. -/
theorem fixedP506L0U6RadialQuarticConnection_crossBracket_zeroSlice
    (space : StageNineSpatialPoint) :
    (fun pair : Fin 6 =>
      p286CoordinateLieBracket
          (p286RadialQuarticTemporalConnection Charge
            (canonicalCauchySlicePoint 0 space) (pairFirst pair))
          (holonomicP286GaugeConnectionCoordinate U6
            (canonicalCauchySlicePoint 0 space) (pairSecond pair)) +
        p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate U6
            (canonicalCauchySlicePoint 0 space) (pairFirst pair))
          (p286RadialQuarticTemporalConnection Charge
            (canonicalCauchySlicePoint 0 space) (pairSecond pair))) = 0 := by
  have spatialOne :
      holonomicP286GaugeConnectionCoordinate U6
          (canonicalCauchySlicePoint 0 space) 1 = 0 := by
    simpa using
      fixedP506L0U6_gaugeConnectionCoordinate_zeroSlice_spatial space 0
  have spatialTwo :
      holonomicP286GaugeConnectionCoordinate U6
          (canonicalCauchySlicePoint 0 space) 2 = 0 := by
    simpa using
      fixedP506L0U6_gaugeConnectionCoordinate_zeroSlice_spatial space 1
  have spatialThree :
      holonomicP286GaugeConnectionCoordinate U6
          (canonicalCauchySlicePoint 0 space) 3 = 0 := by
    simpa using
      fixedP506L0U6_gaugeConnectionCoordinate_zeroSlice_spatial space 2
  funext pair
  fin_cases pair
  all_goals
    simp [p286RadialQuarticTemporalConnection,
      p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
      pairFirst, pairSecond,
      spatialOne, spatialTwo, spatialThree,
      StageNineP286GaugeConnectionVariationDensity.p286CoordinateLieBracket_zero_left,
      StageNineP286GaugeConnectionVariationDensity.p286CoordinateLieBracket_zero_right]

/-- The radial-quartic connection is supported only in the temporal
one-form direction, so its quadratic curvature bracket vanishes globally. -/
theorem fixedP506L0U6RadialQuarticConnection_quadraticBracket_zero
    (point : BasePoint) :
    p286GaugeConnectionQuadraticCurvatureVariation
        (p286RadialQuarticTemporalConnection Charge) point = 0 := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeConnectionQuadraticCurvatureVariation,
      p286RadialQuarticTemporalConnection,
      p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
      pairFirst, pairSecond,
      StageNineP286GaugeConnectionVariationDensity.p286CoordinateLieBracket_zero_left,
      StageNineP286GaugeConnectionVariationDensity.p286CoordinateLieBracket_zero_right]

private theorem
    fixedP506L0U6RadialQuarticConnection_coordinateDerivative_vary
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        fixedP506L0U6RadialQuarticConnectionActual point
        derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative U6 point
          derivativeDirection formDirection +
        p286GaugeVariationCoordinateDerivative
          (p286RadialQuarticTemporalConnection Charge) point
          derivativeDirection formDirection := by
  have backgroundSmooth : ContDiff ℝ ∞ fun candidate =>
      holonomicP286GaugeConnectionCoordinate U6 candidate formDirection := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current]
    exact
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnectionCoordinate_contDiff
        formDirection
  have variationSmooth : ContDiff ℝ ∞ fun candidate =>
      p286RadialQuarticTemporalConnection Charge candidate formDirection :=
    contDiff_pi.mp (p286RadialQuarticTemporalConnection_contDiff Charge)
      formDirection
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate U6 candidate formDirection)
      point :=
    (backgroundSmooth.differentiable (by simp)).differentiableAt
  have variationDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        p286RadialQuarticTemporalConnection Charge candidate formDirection)
      point :=
    (variationSmooth.differentiable (by simp)).differentiableAt
  unfold p286GaugeConnectionCoordinateDerivative
    p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  have functionEquality :
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          fixedP506L0U6RadialQuarticConnectionActual candidate formDirection) =
        fun candidate =>
          holonomicP286GaugeConnectionCoordinate U6 candidate formDirection +
            p286RadialQuarticTemporalConnection Charge candidate
              formDirection := by
    funext candidate
    simpa [fixedP506L0U6RadialQuarticConnectionActual] using congrFun
      (holonomicP286GaugeConnectionCoordinate_vary U6
          (p286RadialQuarticTemporalConnection Charge) 1 candidate)
        formDirection
  rw [functionEquality]
  have derivativeEquality :
      fderiv ℝ
          (fun candidate =>
            holonomicP286GaugeConnectionCoordinate U6 candidate
                formDirection +
              p286RadialQuarticTemporalConnection Charge candidate
                formDirection)
          point =
        fderiv ℝ
            (fun candidate =>
              holonomicP286GaugeConnectionCoordinate U6 candidate
                formDirection)
            point +
          fderiv ℝ
            (fun candidate =>
              p286RadialQuarticTemporalConnection Charge candidate
                formDirection)
            point :=
    (backgroundDifferentiable.hasFDerivAt.add
      variationDifferentiable.hasFDerivAt).fderiv
  rw [derivativeEquality]
  rfl

private theorem fixedP506L0U6RadialQuarticConnection_curvature_expansion
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        fixedP506L0U6RadialQuarticConnectionActual point =
      holonomicP286GaugeCurvatureCoordinate U6 point +
        p286GaugeConnectionLinearCurvatureVariation U6
          (p286RadialQuarticTemporalConnection Charge) point +
        p286GaugeConnectionQuadraticCurvatureVariation
          (p286RadialQuarticTemporalConnection Charge) point := by
  funext pair
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  rw [fixedP506L0U6RadialQuarticConnection_coordinateDerivative_vary,
    fixedP506L0U6RadialQuarticConnection_coordinateDerivative_vary]
  have variedConnection :=
    holonomicP286GaugeConnectionCoordinate_vary U6
      (p286RadialQuarticTemporalConnection Charge) 1 point
  have variedConnectionActual :
      holonomicP286GaugeConnectionCoordinate
          fixedP506L0U6RadialQuarticConnectionActual point =
        holonomicP286GaugeConnectionCoordinate U6 point +
          1 • p286RadialQuarticTemporalConnection Charge point := by
    simpa [fixedP506L0U6RadialQuarticConnectionActual] using
      variedConnection
  rw [congrFun variedConnectionActual (pairFirst pair),
    congrFun variedConnectionActual (pairSecond pair)]
  simp only [one_smul, Pi.add_apply,
    p286CoordinateLieBracket_add_left,
    p286CoordinateLieBracket_add_right]
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  simp only [p286GaugeConnectionLinearCurvatureVariation,
    p286GaugeConnectionQuadraticCurvatureVariation]
  module

theorem fixedP506L0U6RadialQuarticConnection_linearCurvature_zeroSlice
    (space : StageNineSpatialPoint) :
    p286GaugeConnectionLinearCurvatureVariation U6
        (p286RadialQuarticTemporalConnection Charge)
        (canonicalCauchySlicePoint 0 space) =
      fixedP506L0U6RadialQuarticCurvatureIncrement
        (canonicalCauchySlicePoint 0 space) := by
  funext pair
  have exteriorEq := congrFun
    (fixedP506L0U6RadialQuarticConnection_exteriorDerivative
      (canonicalCauchySlicePoint 0 space)) pair
  have crossEq := congrFun
    (fixedP506L0U6RadialQuarticConnection_crossBracket_zeroSlice space) pair
  simp only [Pi.zero_apply] at crossEq
  unfold p286GaugeConnectionLinearCurvatureVariation
  rw [add_assoc, crossEq, add_zero]
  exact exteriorEq

/-- Exact curvature comparison on every point of the fixed zero slice. -/
theorem fixedP506L0U6RadialQuarticConnection_curvature_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeCurvatureCoordinate
        fixedP506L0U6RadialQuarticConnectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeCurvatureCoordinate Algebraic
          (canonicalCauchySlicePoint 0 space) +
        fixedP506L0U6RadialQuarticCurvatureIncrement
          (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0U6RadialQuarticConnection_curvature_expansion,
    fixedP506L0U6RadialQuarticConnection_linearCurvature_zeroSlice,
    fixedP506L0U6RadialQuarticConnection_quadraticBracket_zero,
    add_zero]
  have curvatureEq :
      holonomicGaugeCurvature U6 (canonicalCauchySlicePoint 0 space) =
        holonomicGaugeCurvature Algebraic
          (canonicalCauchySlicePoint 0 space) :=
    holonomicGaugeCurvature_eq_of_connection_eq U6 Algebraic
      fixedP506L0U6_gaugeConnection_eq_algebraic
      (canonicalCauchySlicePoint 0 space)
  unfold holonomicP286GaugeCurvatureCoordinate
  simp only [curvatureEq]

/-! ## Exact constitutive image of the curvature increment -/

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

/-- The literal curvature increment is the fixed-source constitutive image
of the negative radial auxiliary profile, in all six two-form slots. -/
theorem fixedP506L0U6RadialQuarticCurvatureIncrement_eq_constitutive
    (point : BasePoint) :
    formNativeP286CoordinateBlockwiseConstitutive 1
        ((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings Source).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings Source).hyperchargeCouplingSquared : ℝ)
        (-fixedP506L0P286RadialEulerAuxiliaryProfile point) =
      fixedP506L0U6RadialQuarticCurvatureIncrement point := by
  rw [fixedSource_blockwiseConstitutive_eq_unified]
  have couplingValue :
      ((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ) =
        1 / 2 := by
    change positiveSmoothUnifiedSource.legacy.sigma = (1 / 2 : ℝ)
    exact
      StageNinePositiveSourceGravityMouthResidualTransportIteration.positiveSmoothUnifiedSource_legacy_sigma_eq_half
  rw [couplingValue, liftGaugeTwoFormOperator_smul_operator_p286,
    StageNineResidualLimitCoframeBalanceDecision.coframeGaugeSpacetimeHodgeLinear_one]
  rw [show
    EmpiricalReferenceScaleCouplingBoundary.lorentzianCoframeHodgeEquiv.toLinearMap =
      lorentzianCoframeHodge by rfl]
  funext pair
  simp only [Pi.smul_apply]
  rw [StageNineP286SourceAffineCurvatureJetNormalForm.liftGaugeTwoFormOperator_fixedHodge_apply_local]
  fin_cases pair <;>
    simp [fixedP506L0U6RadialQuarticCurvatureIncrement,
      fixedP506L0P286RadialEulerAuxiliaryProfile,
      p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      pairFirst, pairSecond, Fin.sum_univ_three] <;>
    module

private def fixedP506L0U6RadialQuarticCurvatureIncrementActual
    (point : BasePoint) : FormNativeP286GaugeTwoForm :=
  formNativeP286GaugeCoordinateToActualLinear
    (fixedP506L0U6RadialQuarticCurvatureIncrement point)

private def fixedP506L0P286RadialEulerAuxiliaryProfileActual
    (point : BasePoint) : FormNativeP286GaugeTwoForm :=
  formNativeP286GaugeCoordinateToActualLinear
    (fixedP506L0P286RadialEulerAuxiliaryProfile point)

private theorem
    fixedP506L0U6RadialQuarticCurvatureIncrementActual_eq_constitutive
    (point : BasePoint) :
    formNativeP286BlockwiseConstitutive 1
        ((sourceGeneratedUnifiedCouplings Source).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings Source).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings Source).hyperchargeCouplingSquared : ℝ)
        (-fixedP506L0P286RadialEulerAuxiliaryProfileActual point) =
      fixedP506L0U6RadialQuarticCurvatureIncrementActual point := by
  have coordinateEq :=
    fixedP506L0U6RadialQuarticCurvatureIncrement_eq_constitutive point
  unfold formNativeP286CoordinateBlockwiseConstitutive at coordinateEq
  have actualEq := congrArg
    formNativeP286GaugeCoordinateToActualLinear coordinateEq
  simpa [fixedP506L0U6RadialQuarticCurvatureIncrementActual,
    fixedP506L0P286RadialEulerAuxiliaryProfileActual] using actualEq

private theorem
    fixedP506L0U6RadialQuarticCurvatureIncrementActual_eliminates
    (point : BasePoint) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source) 1
        (fixedP506L0U6RadialQuarticCurvatureIncrementActual point) =
      -fixedP506L0P286RadialEulerAuxiliaryProfileActual point := by
  rw [←
    fixedP506L0U6RadialQuarticCurvatureIncrementActual_eq_constitutive point]
  exact
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary_constitutive
      (sourceGeneratedUnifiedCouplings Source) 1 (by simp)
      (-fixedP506L0P286RadialEulerAuxiliaryProfileActual point)

private theorem formNativeP286GaugeEliminatedAuxiliaryAtBoundary_add_local
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (first second : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
        (first + second) =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe first +
        formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
          second := by
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary
    formNativeP286BlockScale formNativeP286LiftedCoframeHodge
  funext output
  apply Prod.ext
  · simp [liftGaugeTwoFormOperator, smul_add, Finset.sum_add_distrib]
    module
  · apply Prod.ext <;>
      simp [liftGaugeTwoFormOperator, smul_add, Finset.sum_add_distrib] <;>
      module

private theorem fixedP506L0U6RadialQuarticConnection_curvatureActual_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicGaugeCurvature fixedP506L0U6RadialQuarticConnectionActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicGaugeCurvature Algebraic
          (canonicalCauchySlicePoint 0 space) +
        fixedP506L0U6RadialQuarticCurvatureIncrementActual
          (canonicalCauchySlicePoint 0 space) := by
  funext pair
  apply p286CoordinateEquiv.injective
  have coordinateEq := congrFun
    (fixedP506L0U6RadialQuarticConnection_curvature_zeroSlice space) pair
  simpa [fixedP506L0U6RadialQuarticCurvatureIncrementActual,
    holonomicP286GaugeCurvatureCoordinate] using coordinateEq

private theorem fixedP506L0U6RadialQuarticConnection_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticConnectionActual.coframe
        (canonicalCauchySlicePoint 0 space) = 1 := by
  change U6.coframe (canonicalCauchySlicePoint 0 space) = 1
  rw [congrFun fixedP506L0U6_coframe_eq_algebraic
    (canonicalCauchySlicePoint 0 space)]
  exact fixedP506L0Algebraic_coframe_zeroSlice space

private theorem fixedP506L0Algebraic_eliminatedAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source) 1
        (holonomicGaugeCurvature Algebraic
          (canonicalCauchySlicePoint 0 space)) =
      Algebraic.gaugeAuxiliary (canonicalCauchySlicePoint 0 space) := by
  have constitutiveRead :=
    completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
      Source FixedInput (canonicalCauchySlicePoint 0 space)
  simpa [diracDualFormNativeConstitutiveAuxiliaryField,
    fixedP506L0Algebraic_coframe_zeroSlice] using constitutiveRead

/-- The live constitutive inverse of the radial-quartic connection subtracts
exactly the generated radial primitive from the algebraic auxiliary. -/
theorem fixedP506L0U6RadialQuarticConstitutiveActual_auxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticConstitutiveActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      Algebraic.gaugeAuxiliary (canonicalCauchySlicePoint 0 space) -
        fixedP506L0P286RadialEulerAuxiliaryProfileActual
          (canonicalCauchySlicePoint 0 space) := by
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (fixedP506L0U6RadialQuarticConnectionActual.coframe
          (canonicalCauchySlicePoint 0 space))
        (holonomicGaugeCurvature
          fixedP506L0U6RadialQuarticConnectionActual
          (canonicalCauchySlicePoint 0 space)) = _
  rw [fixedP506L0U6RadialQuarticConnection_coframe_zeroSlice,
    fixedP506L0U6RadialQuarticConnection_curvatureActual_zeroSlice,
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary_add_local,
    fixedP506L0Algebraic_eliminatedAuxiliary_zeroSlice,
    fixedP506L0U6RadialQuarticCurvatureIncrementActual_eliminates]
  rfl

theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0U6RadialQuarticConstitutiveActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate Algebraic
          (canonicalCauchySlicePoint 0 space) -
        fixedP506L0P286RadialEulerAuxiliaryProfile
          (canonicalCauchySlicePoint 0 space) := by
  funext pair
  have actualEq := congrFun
    (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliary_zeroSlice space)
    pair
  simpa [holonomicP286GaugeAuxiliaryCoordinate,
    fixedP506L0P286RadialEulerAuxiliaryProfileActual] using
    congrArg p286CoordinateEquiv actualEq

/-- Direct machine comparison with the committed corrected B-anchor on the
whole canonical zero slice. -/
theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_eq_requiredExteriorAnchor_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0U6RadialQuarticConstitutiveActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_zeroSlice,
    fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryCoordinate]

theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliary_eq_requiredExteriorAnchor_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticConstitutiveActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) =
      fixedP506L0P286RequiredExteriorZeroSliceAnchorActual.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_eq_requiredExteriorAnchor_zeroSlice
      space) pair

/-- On the same radial-quartic constitutive actual, the literal curvature is
the blockwise constitutive image of the literal auxiliary at every point of
the canonical zero slice. -/
theorem fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryEquation_zeroSlice
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField
        fixedP506L0U6RadialQuarticConstitutiveActual
        (canonicalCauchySlicePoint 0 space)) := by
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField
        fixedP506L0U6RadialQuarticConstitutiveActual
        (canonicalCauchySlicePoint 0 space))
      (by
        change Matrix.det
          (fixedP506L0U6RadialQuarticConnectionActual.coframe
            (canonicalCauchySlicePoint 0 space)) ≠ 0
        rw [fixedP506L0U6RadialQuarticConnection_coframe_zeroSlice]
        simp)).2
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
