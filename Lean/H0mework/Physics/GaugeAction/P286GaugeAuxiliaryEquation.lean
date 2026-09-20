import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryVariation

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeAuxiliaryEquation

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNinePlebanskiMultiplierVariation
open StageNineCoframeTwoFormPairing
open StageNineGravityAuxiliaryVariation
open StageNineHyperchargeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryVariation
open EmpiricalReferenceScaleCouplingBoundary
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

@[simp] theorem liftGaugeTwoFormOperator_zero_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) :
    liftGaugeTwoFormOperator operator (0 : P286GaugeTwoForm) = 0 := by
  funext output
  unfold liftGaugeTwoFormOperator
  simp

@[simp] theorem p286CoordinateLiePairing_zero_left
    (residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing 0 residual = 0 := by
  have equality := p286CoordinateLiePairing_add_left 0 0 residual
  simp only [zero_add] at equality
  linarith

@[simp] theorem p286CoordinateLiePairing_zero_right
    (residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing residual 0 = 0 := by
  have equality := p286CoordinateLiePairing_add_right 0 0 residual
  simp only [zero_add] at equality
  linarith

theorem holonomicLiftCoframeTwoFormLinear_apply_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (form : BasePoint → P286GaugeTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point =>
      liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point)) (form point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  apply continuous_pi
  intro output
  unfold liftGaugeTwoFormOperator
  apply continuous_finsetSum
  intro input _
  have coefficientContinuous : Continuous fun point =>
      gaugeOperatorCoefficient
        (coframeTwoFormLinear (configuration.coframe point)) output input :=
    (continuous_apply output).comp
      (coframeTwoFormLinear_apply_continuous configuration.coframe
        coframeContinuous
        (fun _ => gaugeTwoFormCoordinateDirection input) continuous_const)
  have formInputContinuous : Continuous fun point => form point input :=
    (continuous_apply input).comp formContinuous
  exact coefficientContinuous.smul formInputContinuous

theorem holonomicLiftGaugeSpacetimeHodge_apply_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (form : BasePoint → P286GaugeTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point =>
      liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (form point) := by
  apply continuous_pi
  intro output
  unfold liftGaugeTwoFormOperator
  apply continuous_finsetSum
  intro input _
  have basisHodgeContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate (fun _ => gaugeTwoFormCoordinateDirection input)
      continuous_const
  have coefficientContinuous : Continuous fun point =>
      gaugeOperatorCoefficient
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        output input :=
    (continuous_apply output).comp basisHodgeContinuous
  have formInputContinuous : Continuous fun point => form point input :=
    (continuous_apply input).comp formContinuous
  exact coefficientContinuous.smul formInputContinuous

theorem generatedGaugeTwoFormMetricPairing_p286_apply_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (first second : BasePoint → P286GaugeTwoForm)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
        (configuration.coframe point) (first point) (second point) := by
  have firstTransformContinuous :=
    holonomicLiftCoframeTwoFormLinear_apply_continuous configuration smooth
      first firstContinuous
  have secondTransformContinuous :=
    holonomicLiftCoframeTwoFormLinear_apply_continuous configuration smooth
      second secondContinuous
  unfold generatedGaugeTwoFormMetricPairing
  apply continuous_finsetSum
  intro pair _
  have internalPairingContinuous :=
    p286CoordinateLiePairing_apply_continuous
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (first point) pair)
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (second point) pair)
      ((continuous_apply pair).comp firstTransformContinuous)
      ((continuous_apply pair).comp secondTransformContinuous)
  exact continuous_const.mul internalPairingContinuous

def holonomicP286GaugeAuxiliaryEquationResidual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  p286CoordinateGaugeAuxiliaryEquationResidual
    (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
    ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)
    (holonomicP286GaugeCurvatureCoordinate configuration point)
    (holonomicP286GaugeAuxiliaryCoordinate configuration point)

theorem holonomicP286GaugeAuxiliaryEquationResidual_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous
      (holonomicP286GaugeAuxiliaryEquationResidual source configuration) := by
  let couplingSquared : ℝ :=
    (sourceGeneratedUnifiedCouplings source).strongCouplingSquared
  have curvatureContinuous :=
    holonomicP286GaugeCurvatureCoordinate_continuous configuration smooth
  have auxiliaryContinuous :=
    holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth
  have hodgeAuxiliaryContinuous :=
    holonomicLiftGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate (holonomicP286GaugeAuxiliaryCoordinate configuration)
      auxiliaryContinuous
  have coupledHodgeAuxiliaryContinuous : Continuous fun point =>
      couplingSquared •
        liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryCoordinate configuration point) :=
    (continuous_const : Continuous fun _ : BasePoint => couplingSquared).smul
      hodgeAuxiliaryContinuous
  unfold holonomicP286GaugeAuxiliaryEquationResidual
    p286CoordinateGaugeAuxiliaryEquationResidual
  have residualContinuous :=
    curvatureContinuous.sub coupledHodgeAuxiliaryContinuous
  exact residualContinuous.congr fun point => by
    rw [liftGaugeTwoFormOperator_smul_operator_p286]
    rfl

theorem holonomicP286GaugeAuxiliaryFirstVariationDensity_eq_residualPairing
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (variation : BasePoint → P286GaugeTwoForm) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryFirstVariationDensity
        source configuration variation point =
      generatedVolumeDensity (toContinuumPointField configuration point) *
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
          (configuration.coframe point) (variation point)
          (liftGaugeTwoFormOperator
            (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
            (holonomicP286GaugeAuxiliaryEquationResidual
              source configuration point)) := by
  unfold holonomicP286GaugeAuxiliaryFirstVariationDensity
    p286GaugeAuxiliaryFirstVariationDensity
  change generatedVolumeDensity (toContinuumPointField configuration point) *
      p286CoordinateGaugeAuxiliaryFirstVariationDensity
        (configuration.coframe point)
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicP286GaugeCurvatureCoordinate configuration point)
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)
        (variation point) = _
  rw [p286CoordinateGaugeAuxiliaryFirstVariationDensity_eq_residualPairing
    (configuration.coframe point) (nondegenerate point)]
  rfl

theorem p286CoordinateGaugeAuxiliarySecondVariationDensity_eq_metric
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (couplingSquared : ℝ) (variation : P286GaugeTwoForm) :
    p286CoordinateGaugeAuxiliarySecondVariationDensity coframe
        (coframeGaugeSpacetimeHodgeLinear coframe)
        (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
        variation =
      (couplingSquared / 2) *
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
          variation variation := by
  unfold p286CoordinateGaugeAuxiliarySecondVariationDensity
  rw [liftGaugeTwoFormOperator_coframeHodge_constitutive_p286 coframe
    nondegenerate couplingSquared variation]
  rw [generatedGaugeTwoFormMetricPairing_p286_smul_right]
  ring

theorem holonomicP286GaugeAuxiliaryFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    Continuous
      (holonomicP286GaugeAuxiliaryFirstVariationDensity
        source configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous
      (variation : BasePoint → P286GaugeTwoForm) := variation.smooth.continuous
  have residualContinuous :=
    holonomicP286GaugeAuxiliaryEquationResidual_continuous source configuration
      smooth nondegenerate
  have hodgeResidualContinuous :=
    holonomicLiftGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (holonomicP286GaugeAuxiliaryEquationResidual source configuration)
      residualContinuous
  have pairingContinuous :=
    generatedGaugeTwoFormMetricPairing_p286_apply_continuous configuration smooth
      variation
      (fun point => liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicP286GaugeAuxiliaryEquationResidual source configuration point))
      variationContinuous hodgeResidualContinuous
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  exact (volumeContinuous.mul pairingContinuous).congr fun point => by
    rw [holonomicP286GaugeAuxiliaryFirstVariationDensity_eq_residualPairing
      source configuration nondegenerate]
    rfl

theorem holonomicP286GaugeAuxiliarySecondVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    Continuous
      (holonomicP286GaugeAuxiliarySecondVariationDensity
        source configuration variation) := by
  let couplingSquared : ℝ :=
    (sourceGeneratedUnifiedCouplings source).strongCouplingSquared
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous
      (variation : BasePoint → P286GaugeTwoForm) := variation.smooth.continuous
  have pairingContinuous :=
    generatedGaugeTwoFormMetricPairing_p286_apply_continuous configuration smooth
      variation variation variationContinuous variationContinuous
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have actual := volumeContinuous.mul
    ((continuous_const.mul pairingContinuous) : Continuous fun point =>
      (couplingSquared / 2) *
        generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
          (configuration.coframe point) (variation point) (variation point))
  exact actual.congr fun point => by
    unfold holonomicP286GaugeAuxiliarySecondVariationDensity
      p286GaugeAuxiliarySecondVariationDensity
    change generatedVolumeDensity (toContinuumPointField configuration point) *
        ((couplingSquared / 2) *
          generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
            (configuration.coframe point) (variation point) (variation point)) =
      generatedVolumeDensity (toContinuumPointField configuration point) *
        p286CoordinateGaugeAuxiliarySecondVariationDensity
          (configuration.coframe point)
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (couplingSquared •
            coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (variation point)
    rw [p286CoordinateGaugeAuxiliarySecondVariationDensity_eq_metric
      (configuration.coframe point) (nondegenerate point)]

theorem holonomicP286GaugeAuxiliaryFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    HasCompactSupport
      (holonomicP286GaugeAuxiliaryFirstVariationDensity
        source configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicP286GaugeAuxiliaryFirstVariationDensity,
    p286GaugeAuxiliaryFirstVariationDensity,
    p286CoordinateGaugeAuxiliaryFirstVariationDensity,
    generatedGaugeTwoFormMetricPairing, variationZero,
    liftGaugeTwoFormOperator_zero_p286]

theorem holonomicP286GaugeAuxiliarySecondVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    HasCompactSupport
      (holonomicP286GaugeAuxiliarySecondVariationDensity
        source configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicP286GaugeAuxiliarySecondVariationDensity,
    p286GaugeAuxiliarySecondVariationDensity,
    p286CoordinateGaugeAuxiliarySecondVariationDensity,
    generatedGaugeTwoFormMetricPairing, variationZero,
    liftGaugeTwoFormOperator_zero_p286]

theorem holonomicP286GaugeAuxiliaryFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    Integrable
      (holonomicP286GaugeAuxiliaryFirstVariationDensity
        source configuration variation) :=
  (holonomicP286GaugeAuxiliaryFirstVariationDensity_continuous source
      configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
    (holonomicP286GaugeAuxiliaryFirstVariationDensity_compact source
      configuration variation)

theorem holonomicP286GaugeAuxiliarySecondVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    Integrable
      (holonomicP286GaugeAuxiliarySecondVariationDensity
        source configuration variation) :=
  (holonomicP286GaugeAuxiliarySecondVariationDensity_continuous source
      configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
    (holonomicP286GaugeAuxiliarySecondVariationDensity_compact source
      configuration variation)

theorem holonomicIntegratedUnifiedAction_p286GaugeAuxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source chart
        (varyP286GaugeAuxiliaryCoordinate configuration variation parameter) =
      holonomicIntegratedUnifiedAction source chart configuration +
        parameter * (
          ∫ point : BasePoint,
            holonomicP286GaugeAuxiliaryFirstVariationDensity
              source configuration variation point) +
        parameter ^ 2 * (
          ∫ point : BasePoint,
            holonomicP286GaugeAuxiliarySecondVariationDensity
              source configuration variation point) := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (varyP286GaugeAuxiliaryCoordinate configuration variation parameter)
          point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicP286GaugeAuxiliaryFirstVariationDensity
            source configuration variation point +
        parameter ^ 2 *
          holonomicP286GaugeAuxiliarySecondVariationDensity
            source configuration variation point := by
    funext point
    exact holonomicLocalDensity_p286GaugeAuxiliary_quadratic source chart
      configuration variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicP286GaugeAuxiliaryFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicP286GaugeAuxiliarySecondVariationDensity_integrable source
      configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter * holonomicP286GaugeAuxiliaryFirstVariationDensity
              source configuration variation point +
          parameter ^ 2 * holonomicP286GaugeAuxiliarySecondVariationDensity
            source configuration variation point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter * holonomicP286GaugeAuxiliaryFirstVariationDensity
              source configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicP286GaugeAuxiliarySecondVariationDensity
            source configuration variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) chart point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter * holonomicP286GaugeAuxiliaryFirstVariationDensity
            source configuration variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicP286GaugeAuxiliarySecondVariationDensity
            source configuration variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicIntegratedUnifiedAction_p286GaugeAuxiliary_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation P286GaugeTwoForm) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyP286GaugeAuxiliaryCoordinate configuration variation parameter))
      (∫ point : BasePoint,
        holonomicP286GaugeAuxiliaryFirstVariationDensity
          source configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicP286GaugeAuxiliaryFirstVariationDensity
      source configuration variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicP286GaugeAuxiliarySecondVariationDensity
      source configuration variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyP286GaugeAuxiliaryCoordinate configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source chart configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_p286GaugeAuxiliary_quadratic
      source chart configuration smooth nondegenerate densityIntegrable
        variation parameter
  rw [actionEquality]
  change HasDerivAt
    ((fun parameter =>
      holonomicIntegratedUnifiedAction source chart configuration +
        parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * secondIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicIntegratedUnifiedAction source chart configuration)).add
        (((hasDerivAt_id (x := 0)).pow 2).mul_const secondIntegral))

def P286GaugeAuxiliaryActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeTwoForm,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyP286GaugeAuxiliaryCoordinate configuration variation parameter))
      0 0

def P286GaugeAuxiliaryWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeTwoForm,
    (∫ point : BasePoint,
      holonomicP286GaugeAuxiliaryFirstVariationDensity
        source configuration variation point) = 0

theorem p286GaugeAuxiliaryActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (stationary : P286GaugeAuxiliaryActionStationary
      source chart configuration) :
    P286GaugeAuxiliaryWeakEquation source configuration := by
  intro variation
  have actual :=
    holonomicIntegratedUnifiedAction_p286GaugeAuxiliary_hasDerivAt source
      chart configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

def scalarTimesP286GaugeVariation
    (direction : P286GaugeTwoForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation P286GaugeTwoForm where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have variationCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
    filter_upwards [variationCompact] with point variationZero
    simp [variationZero]

theorem liftGaugeTwoFormOperator_apply_continuous_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : BasePoint → P286GaugeTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point => liftGaugeTwoFormOperator operator (form point) := by
  apply continuous_pi
  intro output
  unfold liftGaugeTwoFormOperator
  apply continuous_finsetSum
  intro input _
  exact (continuous_const : Continuous fun _ : BasePoint =>
      gaugeOperatorCoefficient operator output input).smul
    ((continuous_apply input).comp formContinuous)

theorem liftCoframe_dynamicHodge_p286
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator (coframeTwoFormLinear coframe)
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe) form) =
      liftGaugeTwoFormOperator lorentzianCoframeHodge
        (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) form) := by
  funext output
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  have innerEquality :
      (fun input =>
        liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe) form input internal) =
      coframeGaugeSpacetimeHodgeLinear coframe
        (fun input => form input internal) := by
    funext input
    exact liftGaugeTwoFormOperator_p286Coordinate_apply
      (coframeGaugeSpacetimeHodgeLinear coframe) form input internal
  rw [innerEquality,
    coframeTwoFormLinear_dynamicHodge coframe nondegenerate]
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  have transformedEquality :
      (fun input =>
        liftGaugeTwoFormOperator (coframeTwoFormLinear coframe)
          form input internal) =
      coframeTwoFormLinear coframe (fun input => form input internal) := by
    funext input
    exact liftGaugeTwoFormOperator_p286Coordinate_apply
      (coframeTwoFormLinear coframe) form input internal
  rw [transformedEquality]

def p286GaugeAuxiliaryHodgePairingPolynomial
    (coframe : LorentzianCoframe)
    (first residual : P286GaugeTwoForm) : ℝ :=
  ∑ pair : Fin 6,
    lorentzianTwoFormSign pair *
      p286CoordinateLiePairing
        (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) first pair)
        (liftGaugeTwoFormOperator lorentzianCoframeHodge
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual)
          pair)

theorem p286GaugeAuxiliaryHodgePairingPolynomial_eq
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first residual : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial coframe first residual =
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe first
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear coframe) residual) := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
    generatedGaugeTwoFormMetricPairing
  rw [liftCoframe_dynamicHodge_p286 coframe nondegenerate residual]

def p286GaugeAuxiliaryDirectionCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeTwoForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    p286GaugeAuxiliaryHodgePairingPolynomial
      (configuration.coframe point) direction
      (holonomicP286GaugeAuxiliaryEquationResidual source configuration point)

theorem p286GaugeAuxiliaryDirectionCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeTwoForm) :
    Continuous
      (p286GaugeAuxiliaryDirectionCoefficient source configuration direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have residualContinuous :=
    holonomicP286GaugeAuxiliaryEquationResidual_continuous source configuration
      smooth nondegenerate
  have directionTransformContinuous :=
    holonomicLiftCoframeTwoFormLinear_apply_continuous configuration smooth
      (fun _ => direction) continuous_const
  have residualTransformContinuous :=
    holonomicLiftCoframeTwoFormLinear_apply_continuous configuration smooth
      (holonomicP286GaugeAuxiliaryEquationResidual source configuration)
      residualContinuous
  have hodgeResidualTransformContinuous :=
    liftGaugeTwoFormOperator_apply_continuous_p286 lorentzianCoframeHodge
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point))
        (holonomicP286GaugeAuxiliaryEquationResidual
          source configuration point)) residualTransformContinuous
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold p286GaugeAuxiliaryDirectionCoefficient
    p286GaugeAuxiliaryHodgePairingPolynomial
  apply volumeContinuous.mul
  apply continuous_finsetSum
  intro pair _
  have internalPairingContinuous :=
    p286CoordinateLiePairing_apply_continuous
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point)) direction pair)
      (fun point => liftGaugeTwoFormOperator lorentzianCoframeHodge
        (liftGaugeTwoFormOperator
          (coframeTwoFormLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryEquationResidual
            source configuration point)) pair)
      ((continuous_apply pair).comp directionTransformContinuous)
      ((continuous_apply pair).comp hodgeResidualTransformContinuous)
  exact continuous_const.mul internalPairingContinuous

theorem holonomicP286GaugeAuxiliaryFirstVariationDensity_direction
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeTwoForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryFirstVariationDensity source configuration
        (scalarTimesP286GaugeVariation direction variation) point =
      variation point * p286GaugeAuxiliaryDirectionCoefficient
        source configuration direction point := by
  rw [holonomicP286GaugeAuxiliaryFirstVariationDensity_eq_residualPairing
    source configuration nondegenerate]
  rw [show scalarTimesP286GaugeVariation direction variation point =
    variation point • direction by rfl]
  rw [generatedGaugeTwoFormMetricPairing_p286_smul_left]
  rw [← p286GaugeAuxiliaryHodgePairingPolynomial_eq
    (configuration.coframe point) (nondegenerate point)]
  unfold p286GaugeAuxiliaryDirectionCoefficient
  ring

theorem p286GaugeAuxiliaryWeakEquation_direction_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : P286GaugeAuxiliaryWeakEquation source configuration)
    (direction : P286GaugeTwoForm) :
    p286GaugeAuxiliaryDirectionCoefficient source configuration direction = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (p286GaugeAuxiliaryDirectionCoefficient source configuration direction)
    (p286GaugeAuxiliaryDirectionCoefficient_continuous source configuration
      smooth nondegenerate direction)
  intro variation
  have weakDirection := weakEquation
    (scalarTimesP286GaugeVariation direction variation)
  have integrandEquality :
      (fun point : BasePoint =>
        holonomicP286GaugeAuxiliaryFirstVariationDensity source configuration
          (scalarTimesP286GaugeVariation direction variation) point) =
      fun point => variation point *
        p286GaugeAuxiliaryDirectionCoefficient source configuration
          direction point := by
    funext point
    exact holonomicP286GaugeAuxiliaryFirstVariationDensity_direction source
      configuration nondegenerate direction variation point
  rw [integrandEquality] at weakDirection
  exact weakDirection

theorem liftCoframeTwoFormLinear_comp_inv_p286
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator (coframeTwoFormLinear coframe)
        (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe⁻¹) form) =
      form := by
  funext output
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  have innerEquality :
      (fun input =>
        liftGaugeTwoFormOperator (coframeTwoFormLinear coframe⁻¹)
          form input internal) =
      coframeTwoFormLinear coframe⁻¹ (fun input => form input internal) := by
    funext input
    exact liftGaugeTwoFormOperator_p286Coordinate_apply
      (coframeTwoFormLinear coframe⁻¹) form input internal
  rw [innerEquality]
  have cancellation := congrArg
    (fun operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm =>
      operator (fun input => form input internal))
    (coframeTwoFormLinear_comp_inv coframe nondegenerate)
  have formEquality :
      coframeTwoFormLinear coframe
          (coframeTwoFormLinear coframe⁻¹ (fun input => form input internal)) =
        (fun input => form input internal) := by
    simpa [LinearMap.comp_apply] using cancellation
  exact congrFun formEquality output

theorem liftCoframeTwoFormLinear_injective_p286
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective
      (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) :
        P286GaugeTwoForm → P286GaugeTwoForm) := by
  intro first second equality
  have twiceEquality := congrArg
    (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe⁻¹)) equality
  have inverseNondegenerate : Matrix.det coframe⁻¹ ≠ 0 := by
    simpa [Matrix.det_nonsing_inv] using nondegenerate
  have firstCancellation :
      liftGaugeTwoFormOperator (coframeTwoFormLinear coframe⁻¹)
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) first) =
        first := by
    have raw := liftCoframeTwoFormLinear_comp_inv_p286
      coframe⁻¹ inverseNondegenerate first
    rw [coframe.nonsing_inv_nonsing_inv
      (isUnit_iff_ne_zero.mpr nondegenerate)] at raw
    exact raw
  have secondCancellation :
      liftGaugeTwoFormOperator (coframeTwoFormLinear coframe⁻¹)
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) second) =
        second := by
    have raw := liftCoframeTwoFormLinear_comp_inv_p286
      coframe⁻¹ inverseNondegenerate second
    rw [coframe.nonsing_inv_nonsing_inv
      (isUnit_iff_ne_zero.mpr nondegenerate)] at raw
    exact raw
  rw [firstCancellation, secondCancellation] at twiceEquality
  exact twiceEquality

def p286GaugeMetricPositiveTestDirection
    (coframe : LorentzianCoframe)
    (residual : P286GaugeTwoForm) : P286GaugeTwoForm :=
  liftGaugeTwoFormOperator (coframeTwoFormLinear coframe⁻¹)
    (fun pair => lorentzianTwoFormSign pair •
      liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)

theorem p286GaugeMetricPositiveTestDirection_transform
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator (coframeTwoFormLinear coframe)
        (p286GaugeMetricPositiveTestDirection coframe residual) =
      fun pair => lorentzianTwoFormSign pair •
        liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair := by
  unfold p286GaugeMetricPositiveTestDirection
  exact liftCoframeTwoFormLinear_comp_inv_p286 coframe nondegenerate _

theorem generatedGaugeTwoFormMetricPairing_p286_positiveTestDirection
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : P286GaugeTwoForm) :
    generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        (p286GaugeMetricPositiveTestDirection coframe residual) residual =
      ∑ pair : Fin 6,
        p286CoordinateLiePairing
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair) := by
  unfold generatedGaugeTwoFormMetricPairing
  rw [p286GaugeMetricPositiveTestDirection_transform coframe nondegenerate]
  apply Finset.sum_congr rfl
  intro pair _
  rw [p286CoordinateLiePairing_smul_left]
  calc
    lorentzianTwoFormSign pair *
        (lorentzianTwoFormSign pair *
          p286CoordinateLiePairing
            (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)
            (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)) =
      lorentzianTwoFormSign pair ^ 2 *
        p286CoordinateLiePairing
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair) := by
      ring
    _ = _ := by rw [lorentzianTwoFormSign_sq]; ring

theorem generatedGaugeTwoFormMetricPairing_p286_nondegenerate_right
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : P286GaugeTwoForm)
    (annihilates : ∀ first,
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        first residual = 0) :
    residual = 0 := by
  have sumPairingZero :
      (∑ pair : Fin 6,
        p286CoordinateLiePairing
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)) =
        0 := by
    rw [← generatedGaugeTwoFormMetricPairing_p286_positiveTestDirection
      coframe nondegenerate residual]
    exact annihilates (p286GaugeMetricPositiveTestDirection coframe residual)
  have transformedZero :
      liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual = 0 := by
    funext pair
    have selfPairingZero :
        p286CoordinateLiePairing
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair)
          (liftGaugeTwoFormOperator (coframeTwoFormLinear coframe) residual pair) =
          0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        p286CoordinateLiePairing_self_nonnegative _)).mp
          sumPairingZero pair (Finset.mem_univ pair)
    exact (p286CoordinateLiePairing_self_eq_zero_iff _).mp selfPairingZero
  apply liftCoframeTwoFormLinear_injective_p286 coframe nondegenerate
  simpa using transformedZero

theorem liftGaugeSpacetimeHodge_injective_p286
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective
      (liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear coframe) :
        P286GaugeTwoForm → P286GaugeTwoForm) := by
  intro first second equality
  have twiceEquality := congrArg
    (liftGaugeTwoFormOperator
      (coframeGaugeSpacetimeHodgeLinear coframe)) equality
  have negativeEquality : -first = -second := by
    simpa only [liftGaugeTwoFormOperator_coframeHodge_square_p286
      coframe nondegenerate] using twiceEquality
  exact neg_injective negativeEquality

def P286GaugeAuxiliaryEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point,
    holonomicGaugeCurvature configuration point =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (configuration.gaugeAuxiliary point)

theorem p286GaugeAuxiliaryWeakEquation_implies_equation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : P286GaugeAuxiliaryWeakEquation source configuration) :
    P286GaugeAuxiliaryEquation source configuration := by
  intro point
  have allPairingZero : ∀ direction,
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing
        (configuration.coframe point) direction
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryEquationResidual
            source configuration point)) = 0 := by
    intro direction
    have coefficientZero := congrFun
      (p286GaugeAuxiliaryWeakEquation_direction_zero source configuration
        smooth nondegenerate weakEquation direction) point
    have coefficientZeroScalar :
        p286GaugeAuxiliaryDirectionCoefficient source configuration
          direction point = 0 := by
      simpa using coefficientZero
    have volumeNonzero :
        generatedVolumeDensity
          (toContinuumPointField configuration point) ≠ 0 := by
      simp only [generatedVolumeDensity, toContinuumPointField]
      exact abs_ne_zero.mpr (nondegenerate point)
    have polynomialZero :
        p286GaugeAuxiliaryHodgePairingPolynomial
          (configuration.coframe point) direction
          (holonomicP286GaugeAuxiliaryEquationResidual
            source configuration point) = 0 := by
      exact (mul_eq_zero.mp (by
        simpa only [p286GaugeAuxiliaryDirectionCoefficient] using
          coefficientZeroScalar)).resolve_left volumeNonzero
    rw [← p286GaugeAuxiliaryHodgePairingPolynomial_eq
      (configuration.coframe point) (nondegenerate point)]
    exact polynomialZero
  have hodgeResidualZero :
      liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicP286GaugeAuxiliaryEquationResidual
          source configuration point) = 0 :=
    generatedGaugeTwoFormMetricPairing_p286_nondegenerate_right
      (configuration.coframe point) (nondegenerate point) _ allPairingZero
  have residualZero :
      holonomicP286GaugeAuxiliaryEquationResidual
        source configuration point = 0 := by
    apply liftGaugeSpacetimeHodge_injective_p286
      (configuration.coframe point) (nondegenerate point)
    simpa using hodgeResidualZero
  have coordinateEquation :
      holonomicP286GaugeCurvatureCoordinate configuration point =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryCoordinate configuration point) := by
    simpa [holonomicP286GaugeAuxiliaryEquationResidual,
      p286CoordinateGaugeAuxiliaryEquationResidual, sub_eq_zero] using residualZero
  funext pair
  apply p286CoordinateEquiv.injective
  rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]
  have coordinateComponent := congrFun coordinateEquation pair
  have auxiliaryCoordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate configuration point =
        fun input => p286CoordinateEquiv
          (configuration.gaugeAuxiliary point input) := by
    rfl
  rw [auxiliaryCoordinateEquality] at coordinateComponent
  simpa [holonomicP286GaugeCurvatureCoordinate,
    holonomicP286GaugeAuxiliaryCoordinate] using coordinateComponent

theorem p286GaugeAuxiliaryActionStationary_implies_equation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (stationary : P286GaugeAuxiliaryActionStationary
      source chart configuration) :
    P286GaugeAuxiliaryEquation source configuration :=
  p286GaugeAuxiliaryWeakEquation_implies_equation source configuration
    smooth nondegenerate
    (p286GaugeAuxiliaryActionStationary_implies_weakEquation source chart
      configuration smooth nondegenerate densityIntegrable stationary)

def p286GaugeConstitutiveAuxiliaryCoordinate
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (curvature : P286GaugeTwoForm) : P286GaugeTwoForm :=
  (-(((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ)⁻¹)) •
    liftGaugeTwoFormOperator
      (coframeGaugeSpacetimeHodgeLinear coframe) curvature

theorem p286GaugeConstitutiveAuxiliaryCoordinate_solves
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        (p286GaugeConstitutiveAuxiliaryCoordinate source coframe curvature) =
      curvature := by
  have couplingNonzero :
      ((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) ≠ 0 :=
    ne_of_gt (sourceGeneratedUnifiedCouplings source).strong_pos
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  rw [liftGaugeTwoFormOperator_smul_operator_p286,
    liftGaugeTwoFormOperator_smul_p286,
    liftGaugeTwoFormOperator_coframeHodge_square_p286 coframe nondegenerate]
  funext output
  rw [WithLp.ext_iff]
  funext internal
  simp only [Pi.smul_apply, WithLp.ofLp_smul, WithLp.ofLp_neg,
    Pi.neg_apply, smul_eq_mul]
  field_simp

def generatedP286GaugeConstitutiveAuxiliary
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (curvature : Fin 6 → P286LieBlockData) : Fin 6 → P286LieBlockData :=
  fun pair => p286CoordinateEquiv.symm
    (p286GaugeConstitutiveAuxiliaryCoordinate source coframe
      (fun candidate => p286CoordinateEquiv (curvature candidate)) pair)

theorem generatedP286GaugeConstitutiveAuxiliary_solves
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : Fin 6 → P286LieBlockData) :
    liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        (generatedP286GaugeConstitutiveAuxiliary source coframe curvature) =
      curvature := by
  funext pair
  apply p286CoordinateEquiv.injective
  rw [p286CoordinateEquiv_liftGaugeTwoFormOperator]
  have coordinateSolution := congrFun
    (p286GaugeConstitutiveAuxiliaryCoordinate_solves source coframe
      nondegenerate (fun candidate => p286CoordinateEquiv (curvature candidate)))
    pair
  simpa [generatedP286GaugeConstitutiveAuxiliary] using coordinateSolution

def colorP286Generator : P286LieBlockData :=
  (colorCartanGenerator, 0, 0)

theorem colorP286Generator_ne_zero : colorP286Generator ≠ 0 := by
  intro generatorZero
  have strongZero := congrArg (fun data : P286LieBlockData => data.1)
    generatorZero
  have entryZero := congrArg
    (fun matrix : SU3BlockLieMatrix => (matrix : Matrix (Fin 3) (Fin 3) ℂ) 0 0)
    strongZero
  norm_num [colorP286Generator, colorCartanGenerator, colorCartanRaw] at entryZero

def unitColorP286Curvature : Fin 6 → P286LieBlockData :=
  fun pair => if pair = 0 then colorP286Generator else 0

theorem unitColorP286Curvature_ne_zero : unitColorP286Curvature ≠ 0 := by
  intro curvatureZero
  have componentZero := congrFun curvatureZero 0
  have generatorZero : colorP286Generator = 0 := by
    simpa [unitColorP286Curvature] using componentZero
  exact colorP286Generator_ne_zero generatorZero

@[simp] theorem liftGaugeTwoFormOperator_p286_typed_zero
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) :
    liftGaugeTwoFormOperator operator (0 : Fin 6 → P286LieBlockData) = 0 := by
  funext pair
  unfold liftGaugeTwoFormOperator
  simp

/-- Negative regression: an explicit nonzero color curvature cannot satisfy
the complete P286 constitutive equation with a zero auxiliary field. -/
theorem zeroP286GaugeAuxiliary_negativeRegression
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe) :
    unitColorP286Curvature ≠
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        (0 : Fin 6 → P286LieBlockData) := by
  rw [liftGaugeTwoFormOperator_p286_typed_zero]
  exact unitColorP286Curvature_ne_zero

end


end SaturationMonoid.PhysicsCore.StageNineP286GaugeAuxiliaryEquation
