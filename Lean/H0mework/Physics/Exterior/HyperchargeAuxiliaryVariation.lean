import H0mework.Physics.Exterior.GravityAuxiliaryVariation

namespace SaturationMonoid.PhysicsCore.StageNineHyperchargeAuxiliaryVariation

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
open EmpiricalReferenceScaleCouplingBoundary
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

local instance p286ModuleFiniteHypercharge :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

theorem hypercharge_real_part_eq_zero (value : HyperchargeLieScalar) :
    value.1.re = 0 := by
  have starEquality : star value.1 = -value.1 := value.property
  change conj value.1 = -value.1 at starEquality
  have equality := congrArg Complex.re starEquality
  simp only [Complex.conj_re, Complex.neg_re] at equality
  linarith

def hyperchargeCoordinateEquiv : HyperchargeLieScalar ≃ₗ[ℝ] ℝ where
  toFun value := value.1.im
  invFun coordinate := ⟨coordinate * Complex.I, by
    change star (coordinate * Complex.I : ℂ) = -(coordinate * Complex.I)
    simp⟩
  left_inv := by
    intro value
    apply Subtype.ext
    apply Complex.ext
    · simp [hypercharge_real_part_eq_zero value]
    · simp
  right_inv := by
    intro coordinate
    simp
  map_add' := by
    intro first second
    simp
  map_smul' := by
    intro scalar value
    simp

theorem hyperchargeLiePairing_eq_coordinate_mul
    (first second : HyperchargeLieScalar) :
    hyperchargeLiePairing first second =
      hyperchargeCoordinateEquiv first * hyperchargeCoordinateEquiv second := by
  have firstRe := hypercharge_real_part_eq_zero first
  have secondRe := hypercharge_real_part_eq_zero second
  unfold hyperchargeLiePairing hyperchargeCoordinateEquiv
  simp [Complex.mul_re, firstRe, secondRe]

def gaugeTwoFormCoordinateDirection (input : Fin 6) : GaugeTwoForm :=
  fun candidate => if candidate = input then 1 else 0

theorem gaugeTwoForm_eq_sum_coordinates (form : GaugeTwoForm) :
    form = ∑ input : Fin 6,
      form input • gaugeTwoFormCoordinateDirection input := by
  funext candidate
  simp [gaugeTwoFormCoordinateDirection]

theorem gaugeOperator_apply_eq_sum_coefficient
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : GaugeTwoForm) (output : Fin 6) :
    operator form output =
      ∑ input : Fin 6,
        gaugeOperatorCoefficient operator output input * form input := by
  calc
    operator form output =
        operator (∑ input : Fin 6,
          form input • gaugeTwoFormCoordinateDirection input) output :=
      congrArg (fun candidate => operator candidate output)
        (gaugeTwoForm_eq_sum_coordinates form)
    _ = ∑ input : Fin 6,
        form input * operator (gaugeTwoFormCoordinateDirection input) output := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro input _
      unfold gaugeOperatorCoefficient gaugeTwoFormCoordinateDirection
      ring

theorem hyperchargeCoordinateEquiv_liftGaugeTwoFormOperator
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → HyperchargeLieScalar) (output : Fin 6) :
    hyperchargeCoordinateEquiv
        (liftGaugeTwoFormOperator operator form output) =
      operator (fun input => hyperchargeCoordinateEquiv (form input)) output := by
  unfold liftGaugeTwoFormOperator hyperchargeCoordinateEquiv
  simp only [map_sum, map_smul]
  rw [gaugeOperator_apply_eq_sum_coefficient]
  apply Finset.sum_congr rfl
  intro input _
  simp [smul_eq_mul, mul_comm]

theorem generatedGaugeTwoFormMetricPairing_hypercharge_eq
    (coframe : LorentzianCoframe)
    (first second : Fin 6 → HyperchargeLieScalar) :
    generatedGaugeTwoFormMetricPairing hyperchargeLiePairing coframe
        first second =
      coframeTwoFormMetricPairing coframe
        (fun pair => hyperchargeCoordinateEquiv (first pair))
        (fun pair => hyperchargeCoordinateEquiv (second pair)) := by
  unfold generatedGaugeTwoFormMetricPairing coframeTwoFormMetricPairing
  simp_rw [hyperchargeLiePairing_eq_coordinate_mul,
    hyperchargeCoordinateEquiv_liftGaugeTwoFormOperator]
  apply Finset.sum_congr rfl
  intro pair _
  ring

def scalarGaugeSectorBFDensity
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : GaugeTwoForm) : ℝ :=
  coframeTwoFormMetricPairing coframe auxiliary
      (spacetimeHodge curvature) -
    (1 / 2 : ℝ) *
      coframeTwoFormMetricPairing coframe auxiliary
        (spacetimeHodge (operator auxiliary))

theorem generatedGaugeSectorBFDensity_hypercharge_eq_scalar
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : Fin 6 → HyperchargeLieScalar) :
    generatedGaugeSectorBFDensity hyperchargeLiePairing coframe
        spacetimeHodge operator curvature auxiliary =
      scalarGaugeSectorBFDensity coframe spacetimeHodge operator
        (fun pair => hyperchargeCoordinateEquiv (curvature pair))
        (fun pair => hyperchargeCoordinateEquiv (auxiliary pair)) := by
  unfold generatedGaugeSectorBFDensity scalarGaugeSectorBFDensity
  rw [generatedGaugeTwoFormMetricPairing_hypercharge_eq,
    generatedGaugeTwoFormMetricPairing_hypercharge_eq]
  simp_rw [hyperchargeCoordinateEquiv_liftGaugeTwoFormOperator]

theorem coframeTwoFormMetricPairing_add_right
    (coframe : LorentzianCoframe)
    (first second residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe residual (first + second) =
      coframeTwoFormMetricPairing coframe residual first +
        coframeTwoFormMetricPairing coframe residual second := by
  rw [coframeTwoFormMetricPairing_symmetric coframe residual,
    coframeTwoFormMetricPairing_add_left,
    coframeTwoFormMetricPairing_symmetric coframe first,
    coframeTwoFormMetricPairing_symmetric coframe second]

theorem coframeTwoFormMetricPairing_smul_right
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (first residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe residual (parameter • first) =
      parameter * coframeTwoFormMetricPairing coframe residual first := by
  rw [coframeTwoFormMetricPairing_symmetric coframe residual,
    coframeTwoFormMetricPairing_smul_left,
    coframeTwoFormMetricPairing_symmetric coframe first]

theorem coframeTwoFormMetricPairing_sub_right
    (coframe : LorentzianCoframe)
    (first second residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe residual (first - second) =
      coframeTwoFormMetricPairing coframe residual first -
        coframeTwoFormMetricPairing coframe residual second := by
  simp only [sub_eq_add_neg, coframeTwoFormMetricPairing_add_right]
  rw [show -second = (-1 : ℝ) • second by ext; simp]
  rw [coframeTwoFormMetricPairing_smul_right]
  ring

def scalarGaugeAuxiliaryFirstVariationDensity
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary variation : GaugeTwoForm) : ℝ :=
  coframeTwoFormMetricPairing coframe variation
      (spacetimeHodge curvature) -
    (1 / 2 : ℝ) *
      (coframeTwoFormMetricPairing coframe variation
          (spacetimeHodge (operator auxiliary)) +
        coframeTwoFormMetricPairing coframe auxiliary
          (spacetimeHodge (operator variation)))

def scalarGaugeAuxiliarySecondVariationDensity
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (variation : GaugeTwoForm) : ℝ :=
  -(1 / 2 : ℝ) *
    coframeTwoFormMetricPairing coframe variation
      (spacetimeHodge (operator variation))

theorem scalarGaugeSectorBFDensity_auxiliary_quadratic
    (coframe : LorentzianCoframe)
    (spacetimeHodge operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary variation : GaugeTwoForm) (parameter : ℝ) :
    scalarGaugeSectorBFDensity coframe spacetimeHodge operator curvature
        (auxiliary + parameter • variation) =
      scalarGaugeSectorBFDensity coframe spacetimeHodge operator
          curvature auxiliary +
        parameter * scalarGaugeAuxiliaryFirstVariationDensity coframe
          spacetimeHodge operator curvature auxiliary variation +
        parameter ^ 2 * scalarGaugeAuxiliarySecondVariationDensity coframe
          spacetimeHodge operator variation := by
  unfold scalarGaugeSectorBFDensity
    scalarGaugeAuxiliaryFirstVariationDensity
    scalarGaugeAuxiliarySecondVariationDensity
  simp only [coframeTwoFormMetricPairing_add_left,
    coframeTwoFormMetricPairing_smul_left,
    coframeTwoFormMetricPairing_add_right,
    coframeTwoFormMetricPairing_smul_right,
    map_add, map_smul]
  ring

theorem scalarGaugeConstitutiveBilinear_symmetric
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (hodgeIsGenerated : spacetimeHodge =
      coframeGaugeSpacetimeHodgeLinear coframe)
    (couplingSquared : ℝ) (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe first
        (spacetimeHodge ((couplingSquared • spacetimeHodge) second)) =
      coframeTwoFormMetricPairing coframe second
        (spacetimeHodge ((couplingSquared • spacetimeHodge) first)) := by
  subst spacetimeHodge
  simp only [LinearMap.smul_apply, map_smul,
    coframeTwoFormMetricPairing_smul_right]
  congr 1
  calc
    coframeTwoFormMetricPairing coframe first
        (coframeGaugeSpacetimeHodgeLinear coframe
          (coframeGaugeSpacetimeHodgeLinear coframe second)) =
      coframeTwoFormMetricPairing coframe
        (coframeGaugeSpacetimeHodgeLinear coframe first)
        (coframeGaugeSpacetimeHodgeLinear coframe second) :=
      coframeTwoFormMetricPairing_hodge_symmetric coframe nondegenerate
        first (coframeGaugeSpacetimeHodgeLinear coframe second)
    _ = coframeTwoFormMetricPairing coframe
        (coframeGaugeSpacetimeHodgeLinear coframe second)
        (coframeGaugeSpacetimeHodgeLinear coframe first) :=
      coframeTwoFormMetricPairing_symmetric coframe _ _
    _ = coframeTwoFormMetricPairing coframe second
        (coframeGaugeSpacetimeHodgeLinear coframe
          (coframeGaugeSpacetimeHodgeLinear coframe first)) :=
      (coframeTwoFormMetricPairing_hodge_symmetric coframe nondegenerate
        second (coframeGaugeSpacetimeHodgeLinear coframe first)).symm

def scalarGaugeAuxiliaryEquationResidual
    (spacetimeHodge : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (couplingSquared : ℝ)
    (curvature auxiliary : GaugeTwoForm) : GaugeTwoForm :=
  curvature - (couplingSquared • spacetimeHodge) auxiliary

theorem scalarGaugeAuxiliaryFirstVariationDensity_eq_residualPairing
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (couplingSquared : ℝ)
    (curvature auxiliary variation : GaugeTwoForm) :
    scalarGaugeAuxiliaryFirstVariationDensity coframe
        (coframeGaugeSpacetimeHodgeLinear coframe)
        (couplingSquared • coframeGaugeSpacetimeHodgeLinear coframe)
        curvature auxiliary variation =
      coframeTwoFormMetricPairing coframe variation
        (coframeGaugeSpacetimeHodgeLinear coframe
          (scalarGaugeAuxiliaryEquationResidual
            (coframeGaugeSpacetimeHodgeLinear coframe)
            couplingSquared curvature auxiliary)) := by
  unfold scalarGaugeAuxiliaryFirstVariationDensity
    scalarGaugeAuxiliaryEquationResidual
  rw [← scalarGaugeConstitutiveBilinear_symmetric coframe nondegenerate
    (coframeGaugeSpacetimeHodgeLinear coframe) rfl couplingSquared
      variation auxiliary]
  rw [map_sub, coframeTwoFormMetricPairing_sub_right]
  ring

def hyperchargeCurvatureCoordinate
    (field : StageNineContinuumPointField) : GaugeTwoForm :=
  fun pair => hyperchargeCoordinateEquiv (field.gaugeCurvature pair).2.2

def hyperchargeAuxiliaryCoordinate
    (field : StageNineContinuumPointField) : GaugeTwoForm :=
  fun pair => hyperchargeCoordinateEquiv (field.gaugeAuxiliary pair).2.2

def withHyperchargeAuxiliaryCoordinate
    (field : StageNineContinuumPointField)
    (auxiliary : GaugeTwoForm) : StageNineContinuumPointField :=
  { field with
    gaugeAuxiliary := fun pair =>
      ((field.gaugeAuxiliary pair).1,
        ((field.gaugeAuxiliary pair).2.1,
          hyperchargeCoordinateEquiv.symm (auxiliary pair))) }

@[simp] theorem withHyperchargeAuxiliaryCoordinate_hypercharge
    (field : StageNineContinuumPointField)
    (auxiliary : GaugeTwoForm) (pair : Fin 6) :
    hyperchargeCoordinateEquiv
        ((withHyperchargeAuxiliaryCoordinate field auxiliary).gaugeAuxiliary
          pair).2.2 = auxiliary pair := by
  simp [withHyperchargeAuxiliaryCoordinate]

def hyperchargeAuxiliaryFirstVariationDensity
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (variation : GaugeTwoForm) : ℝ :=
  generatedVolumeDensity field *
    scalarGaugeAuxiliaryFirstVariationDensity field.coframe
      (coframeGaugeSpacetimeHodgeLinear field.coframe)
      ((boundary.hyperchargeCouplingSquared : ℝ) •
        coframeGaugeSpacetimeHodgeLinear field.coframe)
      (hyperchargeCurvatureCoordinate field)
      (hyperchargeAuxiliaryCoordinate field) variation

def hyperchargeAuxiliarySecondVariationDensity
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (variation : GaugeTwoForm) : ℝ :=
  generatedVolumeDensity field *
    scalarGaugeAuxiliarySecondVariationDensity field.coframe
      (coframeGaugeSpacetimeHodgeLinear field.coframe)
      ((boundary.hyperchargeCouplingSquared : ℝ) •
        coframeGaugeSpacetimeHodgeLinear field.coframe)
      variation

def generatedUnifiedLocalDensityHyperchargeIndependentCoreAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  let spacetimeHodge := coframeGaugeSpacetimeHodgeLinear field.coframe
  generatedGravitySimplicityDensity field +
    generatedGravityBFDensity field +
    generatedGaugeSectorBFDensity specialUnitaryLiePairing field.coframe
      spacetimeHodge
      ((boundary.strongCouplingSquared : ℝ) • spacetimeHodge)
      (fun pair => (field.gaugeCurvature pair).1)
      (fun pair => (field.gaugeAuxiliary pair).1) +
    generatedGaugeSectorBFDensity specialUnitaryLiePairing field.coframe
      spacetimeHodge
      ((boundary.weakCouplingSquared : ℝ) • spacetimeHodge)
      (fun pair => (field.gaugeCurvature pair).2.1)
      (fun pair => (field.gaugeAuxiliary pair).2.1) +
    generatedScalarKineticDensity source chart point field -
    StageNineDynamicBreakingVacuum.generatedScalarPotential
      source chart point field.scalar +
    generatedContinuumMatterDensity source chart point field

theorem generatedUnifiedLocalDensity_hypercharge_decomposition
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedUnifiedLocalDensityAtBoundary source boundary chart point field =
      generatedVolumeDensity field *
        (generatedUnifiedLocalDensityHyperchargeIndependentCoreAtBoundary
            source boundary chart point field +
          scalarGaugeSectorBFDensity field.coframe
            (coframeGaugeSpacetimeHodgeLinear field.coframe)
            ((boundary.hyperchargeCouplingSquared : ℝ) •
              coframeGaugeSpacetimeHodgeLinear field.coframe)
            (hyperchargeCurvatureCoordinate field)
            (hyperchargeAuxiliaryCoordinate field)) := by
  unfold generatedUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
    generatedUnifiedLocalDensityHyperchargeIndependentCoreAtBoundary
  dsimp only
  rw [generatedGaugeSectorBFDensity_hypercharge_eq_scalar]
  unfold hyperchargeCurvatureCoordinate hyperchargeAuxiliaryCoordinate
  ring

@[simp] theorem generatedVolumeDensity_withHyperchargeAuxiliaryCoordinate
    (field : StageNineContinuumPointField) (auxiliary : GaugeTwoForm) :
    generatedVolumeDensity
        (withHyperchargeAuxiliaryCoordinate field auxiliary) =
      generatedVolumeDensity field := by
  rfl

@[simp] theorem withHyperchargeAuxiliaryCoordinate_coframe
    (field : StageNineContinuumPointField) (auxiliary : GaugeTwoForm) :
    (withHyperchargeAuxiliaryCoordinate field auxiliary).coframe =
      field.coframe := by
  rfl

@[simp] theorem hyperchargeCurvatureCoordinate_withHyperchargeAuxiliaryCoordinate
    (field : StageNineContinuumPointField) (auxiliary : GaugeTwoForm) :
    hyperchargeCurvatureCoordinate
        (withHyperchargeAuxiliaryCoordinate field auxiliary) =
      hyperchargeCurvatureCoordinate field := by
  rfl

@[simp] theorem hyperchargeAuxiliaryCoordinate_withHyperchargeAuxiliaryCoordinate
    (field : StageNineContinuumPointField) (auxiliary : GaugeTwoForm) :
    hyperchargeAuxiliaryCoordinate
        (withHyperchargeAuxiliaryCoordinate field auxiliary) = auxiliary := by
  funext pair
  exact withHyperchargeAuxiliaryCoordinate_hypercharge field auxiliary pair

@[simp] theorem generatedUnifiedLocalDensityHyperchargeIndependentCore_with
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (auxiliary : GaugeTwoForm) :
    generatedUnifiedLocalDensityHyperchargeIndependentCoreAtBoundary
        source boundary chart point
          (withHyperchargeAuxiliaryCoordinate field auxiliary) =
      generatedUnifiedLocalDensityHyperchargeIndependentCoreAtBoundary
        source boundary chart point field := by
  rfl

theorem generatedUnifiedLocalDensity_hyperchargeAuxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : GaugeTwoForm) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source boundary chart point
        (withHyperchargeAuxiliaryCoordinate field
          (hyperchargeAuxiliaryCoordinate field + parameter • variation)) =
      generatedUnifiedLocalDensityAtBoundary source boundary chart point field +
        parameter * hyperchargeAuxiliaryFirstVariationDensity
          boundary field variation +
        parameter ^ 2 * hyperchargeAuxiliarySecondVariationDensity
          boundary field variation := by
  rw [generatedUnifiedLocalDensity_hypercharge_decomposition,
    generatedUnifiedLocalDensity_hypercharge_decomposition]
  simp only [generatedVolumeDensity_withHyperchargeAuxiliaryCoordinate,
    withHyperchargeAuxiliaryCoordinate_coframe,
    generatedUnifiedLocalDensityHyperchargeIndependentCore_with,
    hyperchargeCurvatureCoordinate_withHyperchargeAuxiliaryCoordinate,
    hyperchargeAuxiliaryCoordinate_withHyperchargeAuxiliaryCoordinate]
  rw [scalarGaugeSectorBFDensity_auxiliary_quadratic]
  unfold hyperchargeAuxiliaryFirstVariationDensity
    hyperchargeAuxiliarySecondVariationDensity
  ring

def varyHyperchargeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → GaugeTwoForm) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gaugeAuxiliary := fun point pair =>
      ((configuration.gaugeAuxiliary point pair).1,
        ((configuration.gaugeAuxiliary point pair).2.1,
          hyperchargeCoordinateEquiv.symm
            (hyperchargeCoordinateEquiv
                (configuration.gaugeAuxiliary point pair).2.2 +
              parameter * variation point pair))) }

theorem toContinuumPointField_varyHyperchargeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → GaugeTwoForm) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyHyperchargeAuxiliaryCoordinate configuration variation parameter)
        point =
      withHyperchargeAuxiliaryCoordinate
        (toContinuumPointField configuration point)
        (hyperchargeAuxiliaryCoordinate
            (toContinuumPointField configuration point) +
          parameter • variation point) := by
  rfl

def holonomicHyperchargeAuxiliaryFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → GaugeTwoForm) (point : BasePoint) : ℝ :=
  hyperchargeAuxiliaryFirstVariationDensity
    (sourceGeneratedUnifiedCouplings source)
    (toContinuumPointField configuration point) (variation point)

def holonomicHyperchargeAuxiliarySecondVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → GaugeTwoForm) (point : BasePoint) : ℝ :=
  hyperchargeAuxiliarySecondVariationDensity
    (sourceGeneratedUnifiedCouplings source)
    (toContinuumPointField configuration point) (variation point)

theorem holonomicLocalDensity_hyperchargeAuxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → GaugeTwoForm) (parameter : ℝ)
    (point : BasePoint) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (varyHyperchargeAuxiliaryCoordinate configuration variation parameter)
          point) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter * holonomicHyperchargeAuxiliaryFirstVariationDensity
          source configuration variation point +
        parameter ^ 2 * holonomicHyperchargeAuxiliarySecondVariationDensity
          source configuration variation point := by
  rw [toContinuumPointField_varyHyperchargeAuxiliaryCoordinate]
  exact generatedUnifiedLocalDensity_hyperchargeAuxiliary_quadratic source
    (sourceGeneratedUnifiedCouplings source) chart point
      (toContinuumPointField configuration point) (variation point) parameter

def p286HyperchargeCoordinateLinear :
    P286CoordinateCarrier →ₗ[ℝ] ℝ where
  toFun coordinate :=
    hyperchargeCoordinateEquiv (p286CoordinateEquiv.symm coordinate).2.2
  map_add' := by
    intro first second
    rw [p286CoordinateEquiv.symm.map_add]
    change hyperchargeCoordinateEquiv
        ((p286CoordinateEquiv.symm first).2.2 +
          (p286CoordinateEquiv.symm second).2.2) = _
    exact hyperchargeCoordinateEquiv.map_add _ _
  map_smul' := by
    intro scalar coordinate
    rw [p286CoordinateEquiv.symm.map_smul]
    change hyperchargeCoordinateEquiv
        (scalar • (p286CoordinateEquiv.symm coordinate).2.2) = _
    exact hyperchargeCoordinateEquiv.map_smul scalar _

theorem p286ConnectionDerivative_hyperchargeCoordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection : LorentzianIndex) :
    Continuous fun point =>
      hyperchargeCoordinateEquiv
        (p286ConnectionDerivative configuration point derivativeDirection
          formDirection).2.2 := by
  have derivativeContinuous : Continuous
      (fderiv ℝ (fun candidate =>
        p286CoordinateEquiv
          (configuration.gaugeConnection candidate formDirection))) :=
    (smooth.2.2.2.2.1 formDirection).continuous_fderiv (by simp)
  have directionContinuous : Continuous fun _ : BasePoint =>
      coordinateDirection derivativeDirection := continuous_const
  have evaluatedContinuous : Continuous fun point =>
      (fderiv ℝ (fun candidate =>
        p286CoordinateEquiv
          (configuration.gaugeConnection candidate formDirection)) point)
        (coordinateDirection derivativeDirection) :=
    isBoundedBilinearMap_apply.continuous.comp
      (derivativeContinuous.prodMk directionContinuous)
  have coordinateContinuous :=
    p286HyperchargeCoordinateLinear.continuous_of_finiteDimensional.comp
      evaluatedContinuous
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  change Continuous
    (p286HyperchargeCoordinateLinear ∘ fun point =>
      (fderiv ℝ (fun candidate =>
        p286CoordinateEquiv
          (configuration.gaugeConnection candidate formDirection)) point)
        (coordinateDirection derivativeDirection))
  exact coordinateContinuous

def holonomicHyperchargeCurvatureCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : GaugeTwoForm :=
  hyperchargeCurvatureCoordinate (toContinuumPointField configuration point)

def holonomicHyperchargeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : GaugeTwoForm :=
  hyperchargeAuxiliaryCoordinate (toContinuumPointField configuration point)

theorem holonomicHyperchargeCurvatureCoordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous (holonomicHyperchargeCurvatureCoordinate configuration) := by
  apply continuous_pi
  intro pair
  have firstDerivative :=
    p286ConnectionDerivative_hyperchargeCoordinate_continuous configuration
    smooth (pairFirst pair) (pairSecond pair)
  have secondDerivative :=
    p286ConnectionDerivative_hyperchargeCoordinate_continuous configuration
    smooth (pairSecond pair) (pairFirst pair)
  have differenceContinuous := firstDerivative.sub secondDerivative
  have coordinateEquality :
      (fun point => holonomicHyperchargeCurvatureCoordinate
        configuration point pair) =
      (fun point =>
        hyperchargeCoordinateEquiv
            (p286ConnectionDerivative configuration point
              (pairFirst pair) (pairSecond pair)).2.2 -
          hyperchargeCoordinateEquiv
            (p286ConnectionDerivative configuration point
              (pairSecond pair) (pairFirst pair)).2.2) := by
    funext point
    simp [holonomicHyperchargeCurvatureCoordinate,
      hyperchargeCurvatureCoordinate, toContinuumPointField,
      holonomicGaugeCurvature, p286LieBracket]
  rw [coordinateEquality]
  exact differenceContinuous

theorem holonomicHyperchargeAuxiliaryCoordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous (holonomicHyperchargeAuxiliaryCoordinate configuration) := by
  apply continuous_pi
  intro pair
  have coordinateContinuous :=
    p286HyperchargeCoordinateLinear.continuous_of_finiteDimensional.comp
      (smooth.2.2.2.2.2.1 pair).continuous
  unfold holonomicHyperchargeAuxiliaryCoordinate
    hyperchargeAuxiliaryCoordinate
  simp only [toContinuumPointField]
  exact coordinateContinuous.congr fun point => by
    simp [p286HyperchargeCoordinateLinear, Function.comp_apply]

theorem coframeTwoFormMetricPairing_apply_continuous
    (coframe : BasePoint → LorentzianCoframe)
    (coframeContinuous : Continuous coframe)
    (first second : BasePoint → GaugeTwoForm)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      coframeTwoFormMetricPairing (coframe point)
        (first point) (second point) := by
  unfold coframeTwoFormMetricPairing
  apply continuous_finsetSum
  intro pair _
  have firstEntryContinuous := (continuous_apply pair).comp
    (coframeTwoFormLinear_apply_continuous coframe coframeContinuous
      first firstContinuous)
  have secondEntryContinuous := (continuous_apply pair).comp
    (coframeTwoFormLinear_apply_continuous coframe coframeContinuous
      second secondContinuous)
  exact (continuous_const.mul firstEntryContinuous).mul secondEntryContinuous

theorem holonomicHyperchargeAuxiliaryFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    Continuous
      (holonomicHyperchargeAuxiliaryFirstVariationDensity
        source configuration variation) := by
  let couplingSquared : ℝ :=
    sourceGeneratedUnifiedCouplings source |>.hyperchargeCouplingSquared
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have curvatureContinuous :=
    holonomicHyperchargeCurvatureCoordinate_continuous configuration smooth
  have auxiliaryContinuous :=
    holonomicHyperchargeAuxiliaryCoordinate_continuous configuration smooth
  have variationContinuous : Continuous (variation : BasePoint → GaugeTwoForm) :=
    variation.smooth.continuous
  have hodgeCurvatureContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate (holonomicHyperchargeCurvatureCoordinate configuration)
      curvatureContinuous
  have hodgeAuxiliaryContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate (holonomicHyperchargeAuxiliaryCoordinate configuration)
      auxiliaryContinuous
  have operatorAuxiliaryContinuous : Continuous fun point =>
      couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (holonomicHyperchargeAuxiliaryCoordinate configuration point) :=
    (continuous_const : Continuous fun _ : BasePoint => couplingSquared).smul
      hodgeAuxiliaryContinuous
  have hodgeOperatorAuxiliaryContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (fun point => couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (holonomicHyperchargeAuxiliaryCoordinate configuration point))
      operatorAuxiliaryContinuous
  have hodgeVariationContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate variation variationContinuous
  have operatorVariationContinuous : Continuous fun point =>
      couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (variation point) :=
    (continuous_const : Continuous fun _ : BasePoint => couplingSquared).smul
      hodgeVariationContinuous
  have hodgeOperatorVariationContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (fun point => couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (variation point)) operatorVariationContinuous
  have firstPairingContinuous := coframeTwoFormMetricPairing_apply_continuous
    configuration.coframe coframeContinuous variation
      (fun point => coframeGaugeSpacetimeHodgeLinear
        (configuration.coframe point)
        (holonomicHyperchargeCurvatureCoordinate configuration point))
      variationContinuous hodgeCurvatureContinuous
  have secondPairingContinuous := coframeTwoFormMetricPairing_apply_continuous
    configuration.coframe coframeContinuous variation
      (fun point => coframeGaugeSpacetimeHodgeLinear
        (configuration.coframe point)
        (couplingSquared •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
            (holonomicHyperchargeAuxiliaryCoordinate configuration point)))
      variationContinuous hodgeOperatorAuxiliaryContinuous
  have thirdPairingContinuous := coframeTwoFormMetricPairing_apply_continuous
    configuration.coframe coframeContinuous
      (holonomicHyperchargeAuxiliaryCoordinate configuration)
      (fun point => coframeGaugeSpacetimeHodgeLinear
        (configuration.coframe point)
        (couplingSquared •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
            (variation point)))
      auxiliaryContinuous hodgeOperatorVariationContinuous
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold holonomicHyperchargeAuxiliaryFirstVariationDensity
    hyperchargeAuxiliaryFirstVariationDensity
    scalarGaugeAuxiliaryFirstVariationDensity
  change Continuous fun point =>
    generatedVolumeDensity (toContinuumPointField configuration point) *
      (coframeTwoFormMetricPairing (configuration.coframe point)
          (variation point)
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
            (holonomicHyperchargeCurvatureCoordinate configuration point)) -
        (1 / 2 : ℝ) *
          (coframeTwoFormMetricPairing (configuration.coframe point)
              (variation point)
              (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
                (couplingSquared •
                  coframeGaugeSpacetimeHodgeLinear
                    (configuration.coframe point)
                    (holonomicHyperchargeAuxiliaryCoordinate
                      configuration point))) +
            coframeTwoFormMetricPairing (configuration.coframe point)
              (holonomicHyperchargeAuxiliaryCoordinate configuration point)
              (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
                (couplingSquared •
                  coframeGaugeSpacetimeHodgeLinear
                    (configuration.coframe point) (variation point)))))
  exact volumeContinuous.mul
    (firstPairingContinuous.sub
      (continuous_const.mul
        (secondPairingContinuous.add thirdPairingContinuous)))

theorem holonomicHyperchargeAuxiliarySecondVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    Continuous
      (holonomicHyperchargeAuxiliarySecondVariationDensity
        source configuration variation) := by
  let couplingSquared : ℝ :=
    sourceGeneratedUnifiedCouplings source |>.hyperchargeCouplingSquared
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous (variation : BasePoint → GaugeTwoForm) :=
    variation.smooth.continuous
  have hodgeVariationContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate variation variationContinuous
  have operatorVariationContinuous : Continuous fun point =>
      couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (variation point) :=
    (continuous_const : Continuous fun _ : BasePoint => couplingSquared).smul
      hodgeVariationContinuous
  have hodgeOperatorVariationContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (fun point => couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (variation point)) operatorVariationContinuous
  have pairingContinuous := coframeTwoFormMetricPairing_apply_continuous
    configuration.coframe coframeContinuous variation
      (fun point => coframeGaugeSpacetimeHodgeLinear
        (configuration.coframe point)
        (couplingSquared •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
            (variation point)))
      variationContinuous hodgeOperatorVariationContinuous
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold holonomicHyperchargeAuxiliarySecondVariationDensity
    hyperchargeAuxiliarySecondVariationDensity
    scalarGaugeAuxiliarySecondVariationDensity
  change Continuous fun point =>
    generatedVolumeDensity (toContinuumPointField configuration point) *
      (-(1 / 2 : ℝ) *
        coframeTwoFormMetricPairing (configuration.coframe point)
          (variation point)
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
            (couplingSquared •
              coframeGaugeSpacetimeHodgeLinear
                (configuration.coframe point) (variation point))))
  exact volumeContinuous.mul (continuous_const.mul pairingContinuous)

theorem holonomicHyperchargeAuxiliaryFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    HasCompactSupport
      (holonomicHyperchargeAuxiliaryFirstVariationDensity
        source configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicHyperchargeAuxiliaryFirstVariationDensity,
    hyperchargeAuxiliaryFirstVariationDensity,
    scalarGaugeAuxiliaryFirstVariationDensity,
    coframeTwoFormMetricPairing, variationZero]

theorem holonomicHyperchargeAuxiliarySecondVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    HasCompactSupport
      (holonomicHyperchargeAuxiliarySecondVariationDensity
        source configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicHyperchargeAuxiliarySecondVariationDensity,
    hyperchargeAuxiliarySecondVariationDensity,
    scalarGaugeAuxiliarySecondVariationDensity,
    coframeTwoFormMetricPairing, variationZero]

theorem holonomicHyperchargeAuxiliaryFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    Integrable
      (holonomicHyperchargeAuxiliaryFirstVariationDensity
        source configuration variation) :=
  (holonomicHyperchargeAuxiliaryFirstVariationDensity_continuous source
      configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
    (holonomicHyperchargeAuxiliaryFirstVariationDensity_compact source
      configuration variation)

theorem holonomicHyperchargeAuxiliarySecondVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    Integrable
      (holonomicHyperchargeAuxiliarySecondVariationDensity
        source configuration variation) :=
  (holonomicHyperchargeAuxiliarySecondVariationDensity_continuous source
      configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
    (holonomicHyperchargeAuxiliarySecondVariationDensity_compact source
      configuration variation)

theorem holonomicIntegratedUnifiedAction_hyperchargeAuxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source chart
        (varyHyperchargeAuxiliaryCoordinate configuration variation parameter) =
      holonomicIntegratedUnifiedAction source chart configuration +
        parameter * (
          ∫ point : BasePoint,
            holonomicHyperchargeAuxiliaryFirstVariationDensity
              source configuration variation point) +
        parameter ^ 2 * (
          ∫ point : BasePoint,
            holonomicHyperchargeAuxiliarySecondVariationDensity
              source configuration variation point) := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (varyHyperchargeAuxiliaryCoordinate configuration variation parameter)
          point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicHyperchargeAuxiliaryFirstVariationDensity
            source configuration variation point +
        parameter ^ 2 *
          holonomicHyperchargeAuxiliarySecondVariationDensity
            source configuration variation point := by
    funext point
    exact holonomicLocalDensity_hyperchargeAuxiliary_quadratic source chart
      configuration variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicHyperchargeAuxiliaryFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicHyperchargeAuxiliarySecondVariationDensity_integrable source
      configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter * holonomicHyperchargeAuxiliaryFirstVariationDensity
              source configuration variation point +
          parameter ^ 2 * holonomicHyperchargeAuxiliarySecondVariationDensity
            source configuration variation point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter * holonomicHyperchargeAuxiliaryFirstVariationDensity
              source configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicHyperchargeAuxiliarySecondVariationDensity
            source configuration variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) chart point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter * holonomicHyperchargeAuxiliaryFirstVariationDensity
            source configuration variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicHyperchargeAuxiliarySecondVariationDensity
            source configuration variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicIntegratedUnifiedAction_hyperchargeAuxiliary_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation GaugeTwoForm) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyHyperchargeAuxiliaryCoordinate configuration variation parameter))
      (∫ point : BasePoint,
        holonomicHyperchargeAuxiliaryFirstVariationDensity
          source configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicHyperchargeAuxiliaryFirstVariationDensity
      source configuration variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicHyperchargeAuxiliarySecondVariationDensity
      source configuration variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyHyperchargeAuxiliaryCoordinate configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source chart configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_hyperchargeAuxiliary_quadratic
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

def HyperchargeAuxiliaryActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation GaugeTwoForm,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyHyperchargeAuxiliaryCoordinate configuration variation parameter))
      0 0

def HyperchargeAuxiliaryWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation GaugeTwoForm,
    (∫ point : BasePoint,
      holonomicHyperchargeAuxiliaryFirstVariationDensity
        source configuration variation point) = 0

theorem hyperchargeAuxiliaryActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (stationary : HyperchargeAuxiliaryActionStationary
      source chart configuration) :
    HyperchargeAuxiliaryWeakEquation source configuration := by
  intro variation
  have actual :=
    holonomicIntegratedUnifiedAction_hyperchargeAuxiliary_hasDerivAt source
      chart configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

def holonomicHyperchargeAuxiliaryEquationResidual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : GaugeTwoForm :=
  scalarGaugeAuxiliaryEquationResidual
    (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
    ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ)
    (holonomicHyperchargeCurvatureCoordinate configuration point)
    (holonomicHyperchargeAuxiliaryCoordinate configuration point)

theorem holonomicHyperchargeAuxiliaryFirstVariationDensity_eq_residualPairing
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (variation : BasePoint → GaugeTwoForm) (point : BasePoint) :
    holonomicHyperchargeAuxiliaryFirstVariationDensity
        source configuration variation point =
      generatedVolumeDensity (toContinuumPointField configuration point) *
        coframeTwoFormMetricPairing (configuration.coframe point)
          (variation point)
          (coframeGaugeSpacetimeHodgeLinear
            (configuration.coframe point)
            (holonomicHyperchargeAuxiliaryEquationResidual
              source configuration point)) := by
  unfold holonomicHyperchargeAuxiliaryFirstVariationDensity
    hyperchargeAuxiliaryFirstVariationDensity
  change generatedVolumeDensity (toContinuumPointField configuration point) *
      scalarGaugeAuxiliaryFirstVariationDensity
        (configuration.coframe point)
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (holonomicHyperchargeCurvatureCoordinate configuration point)
        (holonomicHyperchargeAuxiliaryCoordinate configuration point)
        (variation point) = _
  rw [scalarGaugeAuxiliaryFirstVariationDensity_eq_residualPairing
    (configuration.coframe point) (nondegenerate point)]
  rfl

def singleGaugeTwoFormVariation
    (pair : Fin 6) (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation GaugeTwoForm where
  toFun := fun point candidate =>
    if candidate = pair then variation point else 0
  smooth := by
    apply contDiff_pi'
    intro candidate
    by_cases equality : candidate = pair
    · simpa [equality] using variation.smooth
    · simpa [equality] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint => (0 : ℝ)))
  compactSupport := by
    have variationCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
    filter_upwards [variationCompact] with point variationZero
    funext candidate
    simp [variationZero]

theorem singleGaugeTwoFormVariation_apply
    (pair : Fin 6) (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    singleGaugeTwoFormVariation pair variation point =
      variation point • gaugeTwoFormCoordinateDirection pair := by
  funext candidate
  simp [singleGaugeTwoFormVariation, gaugeTwoFormCoordinateDirection]

/-- Polynomial form of the coframe-metric pairing with the dynamic Hodge.
The inverse coframe cancels by the same-coframe intertwining theorem, so the
coefficient is continuous from primitive fields alone. -/
def hyperchargeAuxiliaryHodgePairingPolynomial
    (coframe : LorentzianCoframe)
    (first residual : GaugeTwoForm) : ℝ :=
  ∑ pair : Fin 6,
    lorentzianTwoFormSign pair *
      coframeTwoFormLinear coframe first pair *
      lorentzianCoframeHodge
        (coframeTwoFormLinear coframe residual) pair

theorem hyperchargeAuxiliaryHodgePairingPolynomial_eq
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first residual : GaugeTwoForm) :
    hyperchargeAuxiliaryHodgePairingPolynomial coframe first residual =
      coframeTwoFormMetricPairing coframe first
        (coframeGaugeSpacetimeHodgeLinear coframe residual) := by
  unfold hyperchargeAuxiliaryHodgePairingPolynomial
    coframeTwoFormMetricPairing
  simp_rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate]

def hyperchargeAuxiliaryCoordinateCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (pair : Fin 6) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    hyperchargeAuxiliaryHodgePairingPolynomial
      (configuration.coframe point)
      (gaugeTwoFormCoordinateDirection pair)
      (holonomicHyperchargeAuxiliaryEquationResidual
        source configuration point)

theorem holonomicHyperchargeAuxiliaryEquationResidual_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous
      (holonomicHyperchargeAuxiliaryEquationResidual source configuration) := by
  let couplingSquared : ℝ :=
    (sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared
  have curvatureContinuous :=
    holonomicHyperchargeCurvatureCoordinate_continuous configuration smooth
  have auxiliaryContinuous :=
    holonomicHyperchargeAuxiliaryCoordinate_continuous configuration smooth
  have hodgeAuxiliaryContinuous :=
    holonomicGaugeSpacetimeHodge_apply_continuous configuration smooth
      nondegenerate (holonomicHyperchargeAuxiliaryCoordinate configuration)
      auxiliaryContinuous
  have coupledHodgeAuxiliaryContinuous : Continuous fun point =>
      couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (holonomicHyperchargeAuxiliaryCoordinate configuration point) :=
    (continuous_const : Continuous fun _ : BasePoint => couplingSquared).smul
      hodgeAuxiliaryContinuous
  unfold holonomicHyperchargeAuxiliaryEquationResidual
    scalarGaugeAuxiliaryEquationResidual
  change Continuous
    (holonomicHyperchargeCurvatureCoordinate configuration -
      fun point => couplingSquared •
        coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (holonomicHyperchargeAuxiliaryCoordinate configuration point))
  exact curvatureContinuous.sub coupledHodgeAuxiliaryContinuous

theorem hyperchargeAuxiliaryCoordinateCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (pair : Fin 6) :
    Continuous
      (hyperchargeAuxiliaryCoordinateCoefficient source configuration pair) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have residualContinuous :=
    holonomicHyperchargeAuxiliaryEquationResidual_continuous source
      configuration smooth nondegenerate
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold hyperchargeAuxiliaryCoordinateCoefficient
    hyperchargeAuxiliaryHodgePairingPolynomial
  apply volumeContinuous.mul
  apply continuous_finsetSum
  intro candidate _
  have directionTransformContinuous :=
    (continuous_apply candidate).comp
      (coframeTwoFormLinear_apply_continuous configuration.coframe
        coframeContinuous
        (fun _ => gaugeTwoFormCoordinateDirection pair) continuous_const)
  have residualTransformContinuous :=
    coframeTwoFormLinear_apply_continuous configuration.coframe
      coframeContinuous
      (holonomicHyperchargeAuxiliaryEquationResidual source configuration)
      residualContinuous
  have hodgeResidualContinuous :=
    (continuous_apply candidate).comp
      (lorentzianCoframeHodge_apply_continuous
        (fun point => coframeTwoFormLinear (configuration.coframe point)
          (holonomicHyperchargeAuxiliaryEquationResidual
            source configuration point))
        residualTransformContinuous)
  exact (continuous_const.mul directionTransformContinuous).mul
    hodgeResidualContinuous

theorem holonomicHyperchargeAuxiliaryFirstVariationDensity_single
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (pair : Fin 6)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicHyperchargeAuxiliaryFirstVariationDensity source configuration
        (singleGaugeTwoFormVariation pair variation) point =
      variation point * hyperchargeAuxiliaryCoordinateCoefficient
        source configuration pair point := by
  rw [holonomicHyperchargeAuxiliaryFirstVariationDensity_eq_residualPairing
    source configuration nondegenerate]
  rw [singleGaugeTwoFormVariation_apply]
  rw [coframeTwoFormMetricPairing_smul_left]
  rw [← hyperchargeAuxiliaryHodgePairingPolynomial_eq
    (configuration.coframe point) (nondegenerate point)]
  unfold hyperchargeAuxiliaryCoordinateCoefficient
  ring

theorem hyperchargeAuxiliaryWeakEquation_coordinate_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : HyperchargeAuxiliaryWeakEquation source configuration)
    (pair : Fin 6) :
    hyperchargeAuxiliaryCoordinateCoefficient source configuration pair = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (hyperchargeAuxiliaryCoordinateCoefficient source configuration pair)
    (hyperchargeAuxiliaryCoordinateCoefficient_continuous source configuration
      smooth nondegenerate pair)
  intro variation
  have weakCoordinate := weakEquation
    (singleGaugeTwoFormVariation pair variation)
  have integrandEquality :
      (fun point : BasePoint =>
        holonomicHyperchargeAuxiliaryFirstVariationDensity source configuration
          (singleGaugeTwoFormVariation pair variation) point) =
      fun point => variation point *
        hyperchargeAuxiliaryCoordinateCoefficient source configuration
          pair point := by
    funext point
    exact holonomicHyperchargeAuxiliaryFirstVariationDensity_single source
      configuration nondegenerate pair variation point
  rw [integrandEquality] at weakCoordinate
  exact weakCoordinate

def gaugeMetricPositiveTestDirection
    (coframe : LorentzianCoframe)
    (residual : GaugeTwoForm) : GaugeTwoForm :=
  coframeTwoFormLinear coframe⁻¹ fun pair =>
    lorentzianTwoFormSign pair *
      coframeTwoFormLinear coframe residual pair

theorem gaugeMetricPositiveTestDirection_transform
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : GaugeTwoForm) :
    coframeTwoFormLinear coframe
        (gaugeMetricPositiveTestDirection coframe residual) =
      fun pair => lorentzianTwoFormSign pair *
        coframeTwoFormLinear coframe residual pair := by
  unfold gaugeMetricPositiveTestDirection
  have cancellation := congrArg
    (fun operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm =>
      operator (fun pair => lorentzianTwoFormSign pair *
        coframeTwoFormLinear coframe residual pair))
    (coframeTwoFormLinear_comp_inv coframe nondegenerate)
  simpa [LinearMap.comp_apply] using cancellation

theorem coframeTwoFormMetricPairing_positiveTestDirection
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe
        (gaugeMetricPositiveTestDirection coframe residual) residual =
      ∑ pair : Fin 6,
        coframeTwoFormLinear coframe residual pair ^ 2 := by
  unfold coframeTwoFormMetricPairing
  rw [gaugeMetricPositiveTestDirection_transform coframe nondegenerate]
  apply Finset.sum_congr rfl
  intro pair _
  calc
    lorentzianTwoFormSign pair *
        (lorentzianTwoFormSign pair *
          coframeTwoFormLinear coframe residual pair) *
        coframeTwoFormLinear coframe residual pair =
      lorentzianTwoFormSign pair ^ 2 *
        coframeTwoFormLinear coframe residual pair ^ 2 := by ring
    _ = coframeTwoFormLinear coframe residual pair ^ 2 := by
      rw [lorentzianTwoFormSign_sq]
      ring

theorem coframeTwoFormMetricPairing_nondegenerate_right
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : GaugeTwoForm)
    (annihilates : ∀ first,
      coframeTwoFormMetricPairing coframe first residual = 0) :
    residual = 0 := by
  have sumSquaresZero :
      (∑ pair : Fin 6,
        coframeTwoFormLinear coframe residual pair ^ 2) = 0 := by
    rw [← coframeTwoFormMetricPairing_positiveTestDirection
      coframe nondegenerate residual]
    exact annihilates (gaugeMetricPositiveTestDirection coframe residual)
  have transformedZero : coframeTwoFormLinear coframe residual = 0 := by
    funext pair
    have squareZero :
        coframeTwoFormLinear coframe residual pair ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp
        sumSquaresZero pair (Finset.mem_univ pair)
    exact sq_eq_zero_iff.mp squareZero
  apply coframeTwoFormLinear_injective coframe nondegenerate
  simpa using transformedZero

def coframeTwoFormMetricPairingLeftLinear
    (coframe : LorentzianCoframe)
    (residual : GaugeTwoForm) : GaugeTwoForm →ₗ[ℝ] ℝ where
  toFun := fun first => coframeTwoFormMetricPairing coframe first residual
  map_add' := fun first second =>
    coframeTwoFormMetricPairing_add_left coframe first second residual
  map_smul' := by
    intro parameter first
    simpa [smul_eq_mul] using
      coframeTwoFormMetricPairing_smul_left coframe parameter first residual

theorem coframeTwoFormMetricPairing_eq_zero_of_coordinate_zero
    (coframe : LorentzianCoframe) (residual : GaugeTwoForm)
    (coordinateZero : ∀ pair,
      coframeTwoFormMetricPairing coframe
        (gaugeTwoFormCoordinateDirection pair) residual = 0) :
    ∀ first, coframeTwoFormMetricPairing coframe first residual = 0 := by
  intro first
  change coframeTwoFormMetricPairingLeftLinear coframe residual first = 0
  rw [gaugeTwoForm_eq_sum_coordinates first]
  simp [coframeTwoFormMetricPairingLeftLinear, coordinateZero]

theorem coframeGaugeSpacetimeHodgeLinear_injective
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective (coframeGaugeSpacetimeHodgeLinear coframe) := by
  intro first second equality
  have twiceEquality := congrArg
    (coframeGaugeSpacetimeHodgeLinear coframe) equality
  have negativeEquality : -first = -second := by
    simpa only [coframeGaugeSpacetimeHodgeLinear_square
      coframe nondegenerate] using twiceEquality
  exact neg_injective negativeEquality

def HyperchargeAuxiliaryEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point,
    (fun pair => (holonomicGaugeCurvature configuration point pair).2.2) =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        (fun pair => (configuration.gaugeAuxiliary point pair).2.2)

theorem hyperchargeAuxiliaryWeakEquation_implies_equation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : HyperchargeAuxiliaryWeakEquation source configuration) :
    HyperchargeAuxiliaryEquation source configuration := by
  intro point
  have coordinatePairingZero : ∀ pair,
      coframeTwoFormMetricPairing (configuration.coframe point)
        (gaugeTwoFormCoordinateDirection pair)
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
          (holonomicHyperchargeAuxiliaryEquationResidual
            source configuration point)) = 0 := by
    intro pair
    have coefficientZero := congrFun
      (hyperchargeAuxiliaryWeakEquation_coordinate_zero source configuration
        smooth nondegenerate weakEquation pair) point
    have coefficientZeroScalar :
        hyperchargeAuxiliaryCoordinateCoefficient source configuration
          pair point = 0 := by
      simpa using coefficientZero
    have volumeNonzero :
        generatedVolumeDensity
          (toContinuumPointField configuration point) ≠ 0 := by
      simp only [generatedVolumeDensity, toContinuumPointField]
      exact abs_ne_zero.mpr (nondegenerate point)
    have polynomialZero :
        hyperchargeAuxiliaryHodgePairingPolynomial
          (configuration.coframe point)
          (gaugeTwoFormCoordinateDirection pair)
          (holonomicHyperchargeAuxiliaryEquationResidual
            source configuration point) = 0 := by
      exact (mul_eq_zero.mp (by
        simpa only [hyperchargeAuxiliaryCoordinateCoefficient] using
          coefficientZeroScalar)).resolve_left volumeNonzero
    rw [← hyperchargeAuxiliaryHodgePairingPolynomial_eq
      (configuration.coframe point) (nondegenerate point)]
    exact polynomialZero
  have allPairingZero :=
    coframeTwoFormMetricPairing_eq_zero_of_coordinate_zero
      (configuration.coframe point)
      (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
        (holonomicHyperchargeAuxiliaryEquationResidual
          source configuration point)) coordinatePairingZero
  have hodgeResidualZero :
      coframeGaugeSpacetimeHodgeLinear (configuration.coframe point)
        (holonomicHyperchargeAuxiliaryEquationResidual
          source configuration point) = 0 :=
    coframeTwoFormMetricPairing_nondegenerate_right
      (configuration.coframe point) (nondegenerate point) _ allPairingZero
  have residualZero :
      holonomicHyperchargeAuxiliaryEquationResidual
        source configuration point = 0 := by
    apply coframeGaugeSpacetimeHodgeLinear_injective
      (configuration.coframe point) (nondegenerate point)
    simpa using hodgeResidualZero
  have coordinateEquation :
      holonomicHyperchargeCurvatureCoordinate configuration point =
        (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicHyperchargeAuxiliaryCoordinate configuration point) := by
    simpa [holonomicHyperchargeAuxiliaryEquationResidual,
      scalarGaugeAuxiliaryEquationResidual, sub_eq_zero] using residualZero
  funext pair
  apply hyperchargeCoordinateEquiv.injective
  rw [hyperchargeCoordinateEquiv_liftGaugeTwoFormOperator]
  have coordinateComponent := congrFun coordinateEquation pair
  have auxiliaryCoordinateEquality :
      holonomicHyperchargeAuxiliaryCoordinate configuration point =
        fun input => hyperchargeCoordinateEquiv
          (configuration.gaugeAuxiliary point input).2.2 := by
    rfl
  rw [auxiliaryCoordinateEquality] at coordinateComponent
  simpa [holonomicHyperchargeCurvatureCoordinate,
    hyperchargeCurvatureCoordinate,
    toContinuumPointField] using coordinateComponent

theorem hyperchargeAuxiliaryActionStationary_implies_equation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (stationary : HyperchargeAuxiliaryActionStationary
      source chart configuration) :
    HyperchargeAuxiliaryEquation source configuration :=
  hyperchargeAuxiliaryWeakEquation_implies_equation source configuration
    smooth nondegenerate
    (hyperchargeAuxiliaryActionStationary_implies_weakEquation source chart
      configuration smooth nondegenerate densityIntegrable stationary)

def scalarHyperchargeConstitutiveAuxiliary
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (curvature : GaugeTwoForm) : GaugeTwoForm :=
  (-(((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ)⁻¹)) •
    coframeGaugeSpacetimeHodgeLinear coframe curvature

theorem scalarHyperchargeConstitutiveAuxiliary_solves
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : GaugeTwoForm) :
    (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) •
      coframeGaugeSpacetimeHodgeLinear coframe)
        (scalarHyperchargeConstitutiveAuxiliary source coframe curvature) =
      curvature := by
  have couplingNonzero :
      ((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) ≠
        0 :=
    ne_of_gt (sourceGeneratedUnifiedCouplings source).hypercharge_pos
  unfold scalarHyperchargeConstitutiveAuxiliary
  rw [LinearMap.smul_apply, map_smul,
    coframeGaugeSpacetimeHodgeLinear_square coframe nondegenerate]
  ext pair
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp

def generatedHyperchargeConstitutiveAuxiliary
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (curvature : Fin 6 → HyperchargeLieScalar) :
    Fin 6 → HyperchargeLieScalar :=
  fun pair => hyperchargeCoordinateEquiv.symm
    (scalarHyperchargeConstitutiveAuxiliary source coframe
      (fun candidate => hyperchargeCoordinateEquiv (curvature candidate)) pair)

theorem generatedHyperchargeConstitutiveAuxiliary_solves
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : Fin 6 → HyperchargeLieScalar) :
    liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        (generatedHyperchargeConstitutiveAuxiliary source coframe curvature) =
      curvature := by
  funext pair
  apply hyperchargeCoordinateEquiv.injective
  rw [hyperchargeCoordinateEquiv_liftGaugeTwoFormOperator]
  have coordinateSolution := congrFun
    (scalarHyperchargeConstitutiveAuxiliary_solves source coframe
      nondegenerate (fun candidate =>
        hyperchargeCoordinateEquiv (curvature candidate))) pair
  simpa [generatedHyperchargeConstitutiveAuxiliary] using coordinateSolution

def unitHyperchargeCurvature : Fin 6 → HyperchargeLieScalar :=
  fun pair => hyperchargeCoordinateEquiv.symm
    (gaugeTwoFormCoordinateDirection 0 pair)

theorem unitHyperchargeCurvature_ne_zero :
    unitHyperchargeCurvature ≠ 0 := by
  intro equality
  have componentEquality := congrFun equality 0
  have coordinateEquality := congrArg hyperchargeCoordinateEquiv componentEquality
  norm_num [unitHyperchargeCurvature, gaugeTwoFormCoordinateDirection]
    at coordinateEquality

theorem liftGaugeTwoFormOperator_hypercharge_zero
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) :
    liftGaugeTwoFormOperator operator
        (0 : Fin 6 → HyperchargeLieScalar) = 0 := by
  funext pair
  simp [liftGaugeTwoFormOperator]

/-- Negative regression: a nonzero typed hypercharge curvature cannot be
declared solved by a zero auxiliary field, even though the source coupling and
coframe operator remain well typed. -/
theorem zeroHyperchargeAuxiliary_negativeRegression
    (source : SmoothUnifiedSource) (coframe : LorentzianCoframe) :
    unitHyperchargeCurvature ≠
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        (0 : Fin 6 → HyperchargeLieScalar) := by
  rw [liftGaugeTwoFormOperator_hypercharge_zero]
  exact unitHyperchargeCurvature_ne_zero

end

end SaturationMonoid.PhysicsCore.StageNineHyperchargeAuxiliaryVariation
