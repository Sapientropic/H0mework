import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Gauge.GaugeAuxiliaryVariation
import H0mework.Physics.Geometry.TopologicalWeakEquation

/-!
# Integrated form-native P286 gauge-auxiliary variation

This module promotes the actual pointwise `SU(3) × SU(2) × U(1)`
auxiliary variation of the authoritative form-native mother action to compact
support.  Primitive variations are supplied in the faithful finite-dimensional
P286 coordinate chart, converted to the actual Lie carrier, and installed only
in the holonomic gauge-auxiliary slot.  The same action hash then generates

`W_P286(deltaB, F - K_e B)`

under the spacetime integral.  Compact-support stationarity is equivalent to
the metric-free weak equation and, by faithful P286 wedge duality, to the
pointwise constitutive zero fiber.

No historical volume-times-metric action derivative, stationarity receipt,
inverse constitutive operator, supplied equation, coverage witness, or target
solution enters a producer mouth.  This is producer soundness for the
gauge-auxiliary Euler leg.  It is not an independent Cauchy constraint, a
gauge-connection/current equation, auxiliary elimination, or existence of a
simultaneous stationary actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeGaugeAuxiliaryIntegratedVariation

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open StageNineBlockwiseConstitutive
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCompactSupportIntegrationByParts
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeMotherAction
open StageNineFundamentalLemma
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineTopologicalFourFormPairing
open StageNineTopologicalWeakEquation
open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Module.Free.ChooseBasisIndex.fintype ℝ P286LieBlockData

/-! ## Faithful coordinate variations and actual paths -/

/-- Finite-dimensional coordinate chart for one full P286-valued two-form. -/
abbrev FormNativeP286GaugeCoordinateTwoForm :=
  Fin 6 → P286CoordinateCarrier

/-- Convert one coordinate two-form back to the actual P286 Lie carrier. -/
def formNativeP286GaugeCoordinateToActualLinear :
    FormNativeP286GaugeCoordinateTwoForm →ₗ[ℝ]
      FormNativeP286GaugeTwoForm where
  toFun variation := fun pair => p286CoordinateEquiv.symm (variation pair)
  map_add' := by
    intro first second
    funext pair
    simp
  map_smul' := by
    intro parameter variation
    funext pair
    simp

@[simp] theorem formNativeP286GaugeCoordinateToActualLinear_apply
    (variation : FormNativeP286GaugeCoordinateTwoForm) (pair : Fin 6) :
    formNativeP286GaugeCoordinateToActualLinear variation pair =
      p286CoordinateEquiv.symm (variation pair) :=
  rfl

@[simp] theorem formNativeP286GaugeCoordinateToActualLinear_zero :
    formNativeP286GaugeCoordinateToActualLinear 0 = 0 := by
  exact map_zero formNativeP286GaugeCoordinateToActualLinear

/-- Install a coordinate variation in the actual primitive P286 auxiliary
slot.  Curvature is still regenerated from the unchanged primitive gauge
connection. -/
def varyFormNativeP286GaugeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  varyFormNativeP286GaugeAuxiliary configuration
    (fun point => formNativeP286GaugeCoordinateToActualLinear (variation point))
    parameter

theorem toContinuumPointField_varyFormNativeP286GaugeAuxiliaryCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (parameter : ℝ) (point : BasePoint) :
    toContinuumPointField
        (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
          parameter) point =
      withFormNativeP286GaugeAuxiliary
        (toContinuumPointField configuration point)
        (configuration.gaugeAuxiliary point +
          parameter •
            formNativeP286GaugeCoordinateToActualLinear (variation point)) :=
  rfl

/-- The coordinate path remains in the primitive smooth holonomic carrier.
This is path admissibility, not an Euler equation. -/
theorem varyFormNativeP286GaugeAuxiliaryCoordinate_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm)
    (parameter : ℝ) :
    (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
      parameter).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  have scaledVariationSmooth : ContDiff ℝ ∞ fun point =>
      parameter • variation point :=
    (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
      contDiff_const).smul variation.smooth
  have variedAuxiliarySmooth : ∀ pair,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv
          ((varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
            parameter).gaugeAuxiliary point pair) := by
    intro pair
    have scaledCoordinateSmooth :=
      contDiff_pi.mp scaledVariationSmooth pair
    simpa [varyFormNativeP286GaugeAuxiliaryCoordinate,
      varyFormNativeP286GaugeAuxiliary] using
      (gaugeAuxiliarySmooth pair).add scaledCoordinateSmooth
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    gravityMultiplierSmooth, gaugeConnectionSmooth, variedAuxiliarySmooth,
    scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-! ## Coordinate algebra and active residual regularity -/

/-- Return an actual P286 two-form to the faithful coordinate chart. -/
def formNativeP286GaugeActualToCoordinateLinear :
    FormNativeP286GaugeTwoForm →ₗ[ℝ]
      FormNativeP286GaugeCoordinateTwoForm where
  toFun form := fun pair => p286CoordinateEquiv (form pair)
  map_add' := by
    intro first second
    funext pair
    simp
  map_smul' := by
    intro parameter form
    funext pair
    simp

@[simp] theorem formNativeP286GaugeActualToCoordinateLinear_apply
    (form : FormNativeP286GaugeTwoForm) (pair : Fin 6) :
    formNativeP286GaugeActualToCoordinateLinear form pair =
      p286CoordinateEquiv (form pair) :=
  rfl

@[simp] theorem formNativeP286GaugeCoordinate_actual_coordinate
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeActualToCoordinateLinear
        (formNativeP286GaugeCoordinateToActualLinear form) = form := by
  funext pair
  simp

@[simp] theorem formNativeP286GaugeActual_coordinate_actual
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeCoordinateToActualLinear
        (formNativeP286GaugeActualToCoordinateLinear form) = form := by
  funext pair
  simp

/-- Positive P286 Lie-fiber pairing transported to the faithful coordinate
chart.  This is rebuilt from the active form-native pairing rather than
importing a historical action module. -/
def formNativeP286CoordinateLiePairing
    (first second : P286CoordinateCarrier) : ℝ :=
  formNativeP286LiePairing (p286CoordinateEquiv.symm first)
    (p286CoordinateEquiv.symm second)

theorem formNativeP286CoordinateLiePairing_add_left
    (first second residual : P286CoordinateCarrier) :
    formNativeP286CoordinateLiePairing (first + second) residual =
      formNativeP286CoordinateLiePairing first residual +
        formNativeP286CoordinateLiePairing second residual := by
  unfold formNativeP286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_add]
  exact formNativeP286LiePairing_add_left _ _ _

theorem formNativeP286CoordinateLiePairing_add_right
    (first second residual : P286CoordinateCarrier) :
    formNativeP286CoordinateLiePairing residual (first + second) =
      formNativeP286CoordinateLiePairing residual first +
        formNativeP286CoordinateLiePairing residual second := by
  unfold formNativeP286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_add]
  exact formNativeP286LiePairing_add_right _ _ _

theorem formNativeP286CoordinateLiePairing_smul_left
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    formNativeP286CoordinateLiePairing (parameter • first) residual =
      parameter * formNativeP286CoordinateLiePairing first residual := by
  unfold formNativeP286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_smul]
  exact formNativeP286LiePairing_smul_left _ _ _

theorem formNativeP286CoordinateLiePairing_smul_right
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    formNativeP286CoordinateLiePairing residual (parameter • first) =
      parameter * formNativeP286CoordinateLiePairing residual first := by
  unfold formNativeP286CoordinateLiePairing
  rw [p286CoordinateEquiv.symm.map_smul]
  exact formNativeP286LiePairing_smul_right _ _ _

def formNativeP286CoordinateLiePairingBilinear :
    P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier →ₗ[ℝ] ℝ where
  toFun first :=
    { toFun := fun second =>
        formNativeP286CoordinateLiePairing first second
      map_add' := fun second residual =>
        formNativeP286CoordinateLiePairing_add_right second residual first
      map_smul' := by
        intro parameter second
        simpa [smul_eq_mul] using
          formNativeP286CoordinateLiePairing_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact formNativeP286CoordinateLiePairing_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    simpa [smul_eq_mul] using
      formNativeP286CoordinateLiePairing_smul_left parameter first residual

theorem formNativeP286CoordinateLiePairing_apply_continuous
    (first second : BasePoint → P286CoordinateCarrier)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      formNativeP286CoordinateLiePairing (first point) (second point) := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × P286CoordinateCarrier =>
      formNativeP286CoordinateLiePairingBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((formNativeP286CoordinateLiePairingBilinear.toContinuousBilinearMap
        |>.continuous.comp continuous_fst).prodMk continuous_snd)
  exact (bilinearContinuous.comp
    (firstContinuous.prodMk secondContinuous)).congr fun point => rfl

/-- Metric-free P286 wedge transported to the faithful coordinate chart. -/
def formNativeP286GaugeCoordinateWedgeCoefficient
    (first second : FormNativeP286GaugeCoordinateTwoForm) : ℝ :=
  generatedTwoFormWedgeCoefficient formNativeP286CoordinateLiePairing
    first second

theorem formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeCoordinateWedgeCoefficient first second =
      formNativeP286GaugeWedgeCoefficient
        (formNativeP286GaugeCoordinateToActualLinear first)
        (formNativeP286GaugeCoordinateToActualLinear second) := by
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    formNativeP286GaugeWedgeCoefficient
    formNativeP286CoordinateLiePairing formNativeP286LiePairing
  rfl

theorem formNativeP286GaugeCoordinateWedgeCoefficient_symmetric
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeCoordinateWedgeCoefficient first second =
      formNativeP286GaugeCoordinateWedgeCoefficient second first := by
  rw [formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual,
    formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  exact formNativeP286GaugeWedgeCoefficient_symmetric _ _

theorem formNativeP286GaugeCoordinateWedgeCoefficient_smul_left
    (parameter : ℝ)
    (first second : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeCoordinateWedgeCoefficient (parameter • first) second =
      parameter *
        formNativeP286GaugeCoordinateWedgeCoefficient first second := by
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  exact formNativeP286CoordinateLiePairing_smul_left parameter (first pair)
    (second (twoFormComplement pair))

@[simp] theorem formNativeP286GaugeCoordinateWedgeCoefficient_zero_left
    (second : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeCoordinateWedgeCoefficient 0 second = 0 := by
  rw [formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  simp

@[simp] theorem formNativeP286GaugeCoordinateWedgeCoefficient_zero_right
    (first : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeCoordinateWedgeCoefficient first 0 = 0 := by
  rw [formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  simp

theorem formNativeP286GaugeCoordinateWedgeCoefficient_separates_left
    (first : FormNativeP286GaugeCoordinateTwoForm)
    (annihilates : ∀ second : FormNativeP286GaugeCoordinateTwoForm,
      formNativeP286GaugeCoordinateWedgeCoefficient first second = 0) :
    first = 0 := by
  have actualZero :
      formNativeP286GaugeCoordinateToActualLinear first = 0 := by
    apply formNativeP286GaugeWedgeCoefficient_separates_left
    intro actualSecond
    have actual := annihilates
      (formNativeP286GaugeActualToCoordinateLinear actualSecond)
    rw [formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual] at actual
    simpa using actual
  have coordinateZero := congrArg
    formNativeP286GaugeActualToCoordinateLinear actualZero
  simpa using coordinateZero

/-- Apply the three coupling coefficients in the P286 coordinate fiber. -/
def formNativeP286BlockwiseCouplingActualLinear
    (strongSquared weakSquared hyperchargeSquared : ℝ) :
    P286LieBlockData →ₗ[ℝ] P286LieBlockData where
  toFun actual :=
    (strongSquared • actual.1,
      weakSquared • actual.2.1,
      hyperchargeSquared • actual.2.2)
  map_add' := by
    intro first second
    apply Prod.ext
    · simp [smul_add]
    · apply Prod.ext <;> simp [smul_add]
  map_smul' := by
    intro parameter actual
    apply Prod.ext
    · simp [smul_smul, mul_comm]
    · apply Prod.ext <;> simp [smul_smul, mul_comm]

/-- Apply the three coupling coefficients in the faithful coordinate fiber. -/
def formNativeP286BlockwiseCouplingCoordinateLinear
    (strongSquared weakSquared hyperchargeSquared : ℝ) :
    P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier :=
  p286CoordinateEquiv.toLinearMap.comp
    ((formNativeP286BlockwiseCouplingActualLinear strongSquared weakSquared
      hyperchargeSquared).comp p286CoordinateEquiv.symm.toLinearMap)

@[simp] theorem formNativeP286BlockwiseCouplingCoordinateLinear_apply
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (coordinate : P286CoordinateCarrier) :
    formNativeP286BlockwiseCouplingCoordinateLinear strongSquared weakSquared
        hyperchargeSquared coordinate =
      p286CoordinateEquiv
        (formNativeP286BlockwiseCouplingActualLinear strongSquared weakSquared
          hyperchargeSquared (p286CoordinateEquiv.symm coordinate)) :=
  rfl

/-- Coordinate form of the active blockwise constitutive operator. -/
def formNativeP286CoordinateBlockwiseConstitutive
    (coframe : LorentzianCoframe)
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear
    (formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
      hyperchargeSquared
      (formNativeP286GaugeCoordinateToActualLinear form))

theorem formNativeP286CoordinateBlockwiseConstitutive_eq_sum
    (coframe : LorentzianCoframe)
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe strongSquared
        weakSquared hyperchargeSquared form = fun output =>
      ∑ input : Fin 6,
        gaugeOperatorCoefficient
            (coframeGaugeSpacetimeHodgeLinear coframe) output input •
          formNativeP286BlockwiseCouplingCoordinateLinear
            strongSquared weakSquared hyperchargeSquared (form input) := by
  funext output
  apply p286CoordinateEquiv.symm.injective
  simp only [formNativeP286CoordinateBlockwiseConstitutive,
    formNativeP286GaugeActualToCoordinateLinear_apply,
    p286CoordinateEquiv.symm_apply_apply]
  change
    formNativeP286BlockwiseConstitutive coframe strongSquared weakSquared
        hyperchargeSquared
        (formNativeP286GaugeCoordinateToActualLinear form) output =
      p286CoordinateEquiv.symm
        (∑ input : Fin 6,
          gaugeOperatorCoefficient
              (coframeGaugeSpacetimeHodgeLinear coframe) output input •
            formNativeP286BlockwiseCouplingCoordinateLinear
              strongSquared weakSquared hyperchargeSquared (form input))
  rw [map_sum]
  simp_rw [map_smul]
  simp only [formNativeP286BlockwiseCouplingCoordinateLinear,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    p286CoordinateEquiv.symm_apply_apply]
  apply Prod.ext
  · rw [Prod.fst_sum]
    simp [formNativeP286BlockwiseCouplingActualLinear,
      formNativeP286BlockwiseConstitutive, liftGaugeTwoFormOperator,
      gaugeOperatorCoefficient, smul_smul, mul_comm]
  · apply Prod.ext
    · rw [Prod.snd_sum, Prod.fst_sum]
      simp [formNativeP286BlockwiseCouplingActualLinear,
        formNativeP286BlockwiseConstitutive, liftGaugeTwoFormOperator,
        gaugeOperatorCoefficient, smul_smul, mul_comm]
    · rw [Prod.snd_sum, Prod.snd_sum]
      simp [formNativeP286BlockwiseCouplingActualLinear,
        formNativeP286BlockwiseConstitutive, liftGaugeTwoFormOperator,
        gaugeOperatorCoefficient, smul_smul, mul_comm]

@[simp] theorem formNativeP286CoordinateBlockwiseConstitutive_zero
    (coframe : LorentzianCoframe)
    (strongSquared weakSquared hyperchargeSquared : ℝ) :
    formNativeP286CoordinateBlockwiseConstitutive coframe strongSquared
        weakSquared hyperchargeSquared 0 = 0 := by
  rw [formNativeP286CoordinateBlockwiseConstitutive_eq_sum]
  funext output
  simp

private theorem formNativeHolonomicCoframe_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ configuration.coframe := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact smooth.1 row column

private theorem holonomicCoframeHodgeCoefficient_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (output input : Fin 6) :
    Continuous fun point =>
      gaugeOperatorCoefficient
        (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
        output input := by
  apply continuous_iff_continuousAt.mpr
  intro point
  change ContinuousAt
    ((fun candidate : LorentzianCoframe =>
      gaugeOperatorCoefficient
        (coframeGaugeSpacetimeHodgeLinear candidate) output input) ∘
      configuration.coframe) point
  have actual :=
    (scaledCoframeHodgeOperatorCoefficient_contDiffAt
      (configuration.coframe point) (nondegenerate point) 1 output input).comp
      point (formNativeHolonomicCoframe_contDiff configuration smooth).contDiffAt
  simpa only [one_smul] using actual.continuousAt

theorem holonomicFormNativeP286CoordinateBlockwiseConstitutive_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (strongSquared weakSquared hyperchargeSquared : ℝ)
    (form : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point =>
      formNativeP286CoordinateBlockwiseConstitutive
        (configuration.coframe point) strongSquared weakSquared
        hyperchargeSquared (form point) := by
  apply continuous_pi
  intro output
  rw [show (fun point =>
      formNativeP286CoordinateBlockwiseConstitutive
        (configuration.coframe point) strongSquared weakSquared
        hyperchargeSquared (form point) output) = fun point =>
      ∑ input : Fin 6,
        gaugeOperatorCoefficient
            (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
            output input •
          formNativeP286BlockwiseCouplingCoordinateLinear
            strongSquared weakSquared hyperchargeSquared (form point input) by
    funext point
    exact congrFun
      (formNativeP286CoordinateBlockwiseConstitutive_eq_sum
        (configuration.coframe point) strongSquared weakSquared
        hyperchargeSquared (form point)) output]
  apply continuous_finsetSum
  intro input _
  have coefficientContinuous :=
    holonomicCoframeHodgeCoefficient_continuous configuration smooth
      nondegenerate output input
  have formInputContinuous : Continuous fun point => form point input :=
    (continuous_apply input).comp formContinuous
  have coupledInputContinuous : Continuous fun point =>
      formNativeP286BlockwiseCouplingCoordinateLinear strongSquared
        weakSquared hyperchargeSquared (form point input) :=
    formNativeP286BlockwiseCouplingCoordinateLinear strongSquared weakSquared
      hyperchargeSquared
      |>.continuous_of_finiteDimensional.comp formInputContinuous
  exact coefficientContinuous.smul coupledInputContinuous

/-- Coordinate readout of the actual active Euler residual. -/
def holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear
    (formNativeP286GaugeAuxiliaryEulerResidualAtBoundary boundary
      (toContinuumPointField configuration point))

theorem holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_eq
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate boundary
        configuration point =
      (fun pair =>
        p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point pair)) -
        formNativeP286CoordinateBlockwiseConstitutive
          (configuration.coframe point)
          (boundary.strongCouplingSquared : ℝ)
          (boundary.weakCouplingSquared : ℝ)
          (boundary.hyperchargeCouplingSquared : ℝ)
          (fun pair =>
            p286CoordinateEquiv (configuration.gaugeAuxiliary point pair)) := by
  unfold holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary toContinuumPointField
  rw [map_sub]
  change
    formNativeP286GaugeActualToCoordinateLinear
          (holonomicGaugeCurvature configuration point) -
        formNativeP286GaugeActualToCoordinateLinear
          (formNativeP286BlockwiseConstitutive
            (configuration.coframe point)
            (boundary.strongCouplingSquared : ℝ)
            (boundary.weakCouplingSquared : ℝ)
            (boundary.hyperchargeCouplingSquared : ℝ)
            (configuration.gaugeAuxiliary point)) =
      formNativeP286GaugeActualToCoordinateLinear
          (holonomicGaugeCurvature configuration point) -
        formNativeP286CoordinateBlockwiseConstitutive
          (configuration.coframe point)
          (boundary.strongCouplingSquared : ℝ)
          (boundary.weakCouplingSquared : ℝ)
          (boundary.hyperchargeCouplingSquared : ℝ)
          (formNativeP286GaugeActualToCoordinateLinear
            (configuration.gaugeAuxiliary point))
  simp [formNativeP286CoordinateBlockwiseConstitutive]

/-- The coordinate residual is continuous from primitive smoothness and live
coframe nondegeneracy alone. -/
theorem holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_continuous
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous
      (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate boundary
        configuration) := by
  have curvatureContinuous : Continuous fun point pair =>
      p286CoordinateEquiv
        (holonomicGaugeCurvature configuration point pair) := by
    apply continuous_pi
    intro pair
    exact
      (holonomicGaugeCurvature_coordinate_contDiff configuration smooth pair)
        |>.continuous
  have auxiliaryContinuous : Continuous fun point pair =>
      p286CoordinateEquiv (configuration.gaugeAuxiliary point pair) := by
    apply continuous_pi
    intro pair
    exact (smooth.2.2.2.2.2.1 pair).continuous
  have constitutiveContinuous :=
    holonomicFormNativeP286CoordinateBlockwiseConstitutive_continuous
      configuration smooth nondegenerate
      (boundary.strongCouplingSquared : ℝ)
      (boundary.weakCouplingSquared : ℝ)
      (boundary.hyperchargeCouplingSquared : ℝ)
      (fun point pair =>
        p286CoordinateEquiv (configuration.gaugeAuxiliary point pair))
      auxiliaryContinuous
  rw [show
      holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate boundary
          configuration = fun point =>
        (fun pair => p286CoordinateEquiv
          (holonomicGaugeCurvature configuration point pair)) -
        formNativeP286CoordinateBlockwiseConstitutive
          (configuration.coframe point)
          (boundary.strongCouplingSquared : ℝ)
          (boundary.weakCouplingSquared : ℝ)
          (boundary.hyperchargeCouplingSquared : ℝ)
          (fun pair =>
            p286CoordinateEquiv (configuration.gaugeAuxiliary point pair)) by
    funext point
    exact
      holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_eq boundary
        configuration point]
  exact curvatureContinuous.sub constitutiveContinuous

private theorem formNativeP286GaugeCoordinateWedgeCoefficient_apply_continuous
    (first second : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      formNativeP286GaugeCoordinateWedgeCoefficient
        (first point) (second point) := by
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  apply continuous_finsetSum
  intro pair _
  have firstPairContinuous : Continuous fun point => first point pair :=
    (continuous_apply pair).comp firstContinuous
  have secondPairContinuous : Continuous fun point =>
      second point (twoFormComplement pair) :=
    (continuous_apply (twoFormComplement pair)).comp secondContinuous
  exact formNativeP286CoordinateLiePairing_apply_continuous
    (fun point => first point pair)
    (fun point => second point (twoFormComplement pair))
    firstPairContinuous secondPairContinuous

/-! ## Compact coefficients -/

def holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (point : BasePoint) : ℝ :=
  formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary boundary
    (toContinuumPointField configuration point)
    (formNativeP286GaugeCoordinateToActualLinear (variation point))

def holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (point : BasePoint) : ℝ :=
  formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary boundary
    (toContinuumPointField configuration point)
    (formNativeP286GaugeCoordinateToActualLinear (variation point))

theorem holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_eq_pairing
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (point : BasePoint) :
    holonomicFormNativeP286GaugeCoordinateFirstVariationDensity boundary
        configuration variation point =
      formNativeP286GaugeCoordinateWedgeCoefficient (variation point)
        (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate boundary
          configuration point) := by
  rw [formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  simp [holonomicFormNativeP286GaugeCoordinateFirstVariationDensity,
    formNativeP286GaugeAuxiliaryFirstVariationDensityAtBoundary,
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate]

theorem
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_eq_pairing
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (point : BasePoint) :
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity boundary
        configuration variation point =
      -(1 / 2 : ℝ) *
        formNativeP286GaugeCoordinateWedgeCoefficient (variation point)
          (formNativeP286CoordinateBlockwiseConstitutive
            (configuration.coframe point)
            (boundary.strongCouplingSquared : ℝ)
            (boundary.weakCouplingSquared : ℝ)
            (boundary.hyperchargeCouplingSquared : ℝ)
            (variation point)) := by
  rw [formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  simp [holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity,
    formNativeP286GaugeAuxiliaryQuadraticCoefficientDensityAtBoundary,
    formNativeP286CoordinateBlockwiseConstitutive,
    toContinuumPointField]

theorem holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_continuous
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    Continuous
      (holonomicFormNativeP286GaugeCoordinateFirstVariationDensity boundary
        configuration variation) := by
  rw [show holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
      boundary configuration variation = fun point =>
        formNativeP286GaugeCoordinateWedgeCoefficient (variation point)
          (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate boundary
            configuration point) by
    funext point
    exact
      holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_eq_pairing
        boundary configuration variation point]
  exact formNativeP286GaugeCoordinateWedgeCoefficient_apply_continuous
    variation
    (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate boundary
      configuration)
    variation.smooth.continuous
    (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_continuous
      boundary configuration smooth nondegenerate)

theorem
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_continuous
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    Continuous
      (holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
        boundary configuration variation) := by
  have variationContinuous : Continuous
      (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm) :=
    variation.smooth.continuous
  have constitutiveContinuous :=
    holonomicFormNativeP286CoordinateBlockwiseConstitutive_continuous configuration
      smooth nondegenerate
      (boundary.strongCouplingSquared : ℝ)
      (boundary.weakCouplingSquared : ℝ)
      (boundary.hyperchargeCouplingSquared : ℝ)
      variation variationContinuous
  rw [show
      holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
          boundary configuration variation = fun point =>
        -(1 / 2 : ℝ) *
          formNativeP286GaugeCoordinateWedgeCoefficient (variation point)
            (formNativeP286CoordinateBlockwiseConstitutive
              (configuration.coframe point)
              (boundary.strongCouplingSquared : ℝ)
              (boundary.weakCouplingSquared : ℝ)
              (boundary.hyperchargeCouplingSquared : ℝ)
              (variation point)) by
    funext point
    exact
      holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_eq_pairing
        boundary configuration variation point]
  exact continuous_const.mul
    (formNativeP286GaugeCoordinateWedgeCoefficient_apply_continuous
      variation
      (fun point => formNativeP286CoordinateBlockwiseConstitutive
        (configuration.coframe point)
        (boundary.strongCouplingSquared : ℝ)
        (boundary.weakCouplingSquared : ℝ)
        (boundary.hyperchargeCouplingSquared : ℝ) (variation point))
      variationContinuous constitutiveContinuous)

theorem holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_compact
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    HasCompactSupport
      (holonomicFormNativeP286GaugeCoordinateFirstVariationDensity boundary
        configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  rw [holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_eq_pairing,
    variationZero]
  simp

theorem
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_compact
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    HasCompactSupport
      (holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
        boundary configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  rw [
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_eq_pairing,
    variationZero]
  simp

theorem holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_integrable
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    Integrable
      (holonomicFormNativeP286GaugeCoordinateFirstVariationDensity boundary
        configuration variation) :=
  (holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_continuous
      boundary configuration smooth nondegenerate variation)
    |>.integrable_of_hasCompactSupport
      (holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_compact
        boundary configuration variation)

theorem
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_integrable
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    Integrable
      (holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
        boundary configuration variation) :=
  (holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_continuous
      boundary configuration smooth nondegenerate variation)
    |>.integrable_of_hasCompactSupport
      (holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_compact
        boundary configuration variation)

/-! ## Integrated polynomial and derivative -/

theorem holonomicFormNativeLocalDensity_p286GaugeAuxiliaryCoordinate_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (variation : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (parameter : ℝ) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
        (toContinuumPointField
          (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
            parameter) point) =
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeP286GaugeCoordinateFirstVariationDensity boundary
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
            boundary configuration variation point := by
  rw [toContinuumPointField_varyFormNativeP286GaugeAuxiliaryCoordinate]
  exact
    generatedFormNativeUnifiedLocalDensityAtBoundary_p286Auxiliary_quadratic
      source boundary chart point (toContinuumPointField configuration point)
      (nondegenerate point)
      (formNativeP286GaugeCoordinateToActualLinear (variation point)) parameter

/-- The actual form-native global action is quadratic along every compactly
supported primitive coordinate variation of the P286 auxiliary field. -/
theorem holonomicFormNativeIntegratedAction_p286GaugeAuxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm)
    (parameter : ℝ) :
    holonomicFormNativeIntegratedUnifiedAction source chart
        (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
          parameter) =
      holonomicFormNativeIntegratedUnifiedAction source chart configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
              (sourceGeneratedUnifiedCouplings source) configuration variation
              point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
              (sourceGeneratedUnifiedCouplings source) configuration variation
              point) := by
  unfold holonomicFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedFormNativeUnifiedAction
    integratedFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise :
      (fun point : BasePoint =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField
            (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
              parameter) point)) =
      fun point =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
            (sourceGeneratedUnifiedCouplings source) configuration variation
            point +
        parameter ^ 2 *
          holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
            (sourceGeneratedUnifiedCouplings source) configuration variation
            point := by
    funext point
    exact
      holonomicFormNativeLocalDensity_p286GaugeAuxiliaryCoordinate_quadratic
        source (sourceGeneratedUnifiedCouplings source) chart point
        configuration nondegenerate variation parameter
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_integrable
      (sourceGeneratedUnifiedCouplings source) configuration smooth
      nondegenerate variation
  have quadraticIntegrable :=
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity_integrable
      (sourceGeneratedUnifiedCouplings source) configuration smooth
      nondegenerate variation
  change Integrable (fun point : BasePoint =>
      generatedFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField configuration point)) at densityIntegrable
  calc
    (∫ point : BasePoint,
        generatedFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
                (sourceGeneratedUnifiedCouplings source) configuration variation
                point +
          parameter ^ 2 *
            holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
              (sourceGeneratedUnifiedCouplings source) configuration variation
              point) =
      (∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) chart point
                (toContinuumPointField configuration point) +
              parameter *
                holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
                  (sourceGeneratedUnifiedCouplings source) configuration
                  variation point) +
        ∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
              (sourceGeneratedUnifiedCouplings source) configuration variation
              point := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (quadraticIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) chart point
            (toContinuumPointField configuration point)) +
        ∫ point : BasePoint,
          parameter *
            holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
              (sourceGeneratedUnifiedCouplings source) configuration variation
              point) +
        ∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
              (sourceGeneratedUnifiedCouplings source) configuration variation
              point := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicFormNativeIntegratedAction_p286GaugeAuxiliary_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm) :
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
            parameter))
      (∫ point : BasePoint,
        holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
          (sourceGeneratedUnifiedCouplings source) configuration variation point)
      0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
      (sourceGeneratedUnifiedCouplings source) configuration variation point
  let quadraticIntegral := ∫ point : BasePoint,
    holonomicFormNativeP286GaugeCoordinateQuadraticCoefficientDensity
      (sourceGeneratedUnifiedCouplings source) configuration variation point
  have formula :
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
            parameter)) =
      fun parameter =>
        holonomicFormNativeIntegratedUnifiedAction source chart configuration +
          parameter * firstIntegral + parameter ^ 2 * quadraticIntegral := by
    funext parameter
    exact holonomicFormNativeIntegratedAction_p286GaugeAuxiliary_quadratic
      source chart configuration smooth nondegenerate densityIntegrable
      variation parameter
  rw [formula]
  change HasDerivAt
    ((fun parameter =>
      holonomicFormNativeIntegratedUnifiedAction source chart configuration +
        parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * quadraticIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstIntegral).const_add
      (holonomicFormNativeIntegratedUnifiedAction source chart configuration)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const
        quadraticIntegral))

/-! ## Faithful weak zero fiber -/

/-- Weak vanishing of the faithful coordinate readout of an actual P286
two-form residual against every compact coordinate variation. -/
def FormNativeP286GaugeWeakEquation
    (residual : BasePoint → FormNativeP286GaugeCoordinateTwoForm) : Prop :=
  ∀ variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm,
    (∫ point : BasePoint,
      formNativeP286GaugeCoordinateWedgeCoefficient
        (variation point) (residual point)) = 0

/-- Multiply an arbitrary faithful P286 coordinate direction by a compact
scalar bump. -/
def scalarTimesFormNativeP286GaugeCoordinateVariation
    (direction : FormNativeP286GaugeCoordinateTwoForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation
      FormNativeP286GaugeCoordinateTwoForm where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have variationCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
    filter_upwards [variationCompact] with point variationZero
    simp [variationZero]

@[simp] theorem scalarTimesFormNativeP286GaugeCoordinateVariation_apply
    (direction : FormNativeP286GaugeCoordinateTwoForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesFormNativeP286GaugeCoordinateVariation direction variation point =
      variation point • direction := by
  rfl

def formNativeP286GaugeDirectionalCoefficient
    (residual : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (direction : FormNativeP286GaugeCoordinateTwoForm) : BasePoint → ℝ :=
  fun point =>
    formNativeP286GaugeCoordinateWedgeCoefficient direction (residual point)

theorem formNativeP286GaugeDirectionalCoefficient_continuous
    (residual : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (residualContinuous : Continuous residual)
    (direction : FormNativeP286GaugeCoordinateTwoForm) :
    Continuous
      (formNativeP286GaugeDirectionalCoefficient residual direction) := by
  exact formNativeP286GaugeCoordinateWedgeCoefficient_apply_continuous
    (fun _ : BasePoint => direction) residual continuous_const
    residualContinuous

theorem formNativeP286GaugeCoordinateWedgeCoefficient_scalarTimes
    (residual : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (direction : FormNativeP286GaugeCoordinateTwoForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    formNativeP286GaugeCoordinateWedgeCoefficient
        (scalarTimesFormNativeP286GaugeCoordinateVariation direction variation
          point) (residual point) =
      variation point *
        formNativeP286GaugeDirectionalCoefficient residual direction point := by
  rw [scalarTimesFormNativeP286GaugeCoordinateVariation_apply,
    formNativeP286GaugeCoordinateWedgeCoefficient_smul_left]
  rfl

theorem formNativeP286GaugeWeakEquation_directionalCoefficient_eq_zero
    (residual : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (residualContinuous : Continuous residual)
    (weakEquation : FormNativeP286GaugeWeakEquation residual)
    (direction : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286GaugeDirectionalCoefficient residual direction = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (formNativeP286GaugeDirectionalCoefficient residual direction)
    (formNativeP286GaugeDirectionalCoefficient_continuous residual
      residualContinuous direction)
  intro variation
  have weakDirection := weakEquation
    (scalarTimesFormNativeP286GaugeCoordinateVariation direction variation)
  have integrandEquality :
      (fun point : BasePoint =>
        formNativeP286GaugeCoordinateWedgeCoefficient
          (scalarTimesFormNativeP286GaugeCoordinateVariation direction
            variation point) (residual point)) =
        fun point => variation point *
          formNativeP286GaugeDirectionalCoefficient residual direction point := by
    funext point
    exact formNativeP286GaugeCoordinateWedgeCoefficient_scalarTimes residual
      direction variation point
  rw [integrandEquality] at weakDirection
  exact weakDirection

/-- Dependency-light weak fundamental lemma for the full P286 topological
pairing.  Complementary spacetime tests and the faithful Lie pairing separate
the residual; no positivity of a four-form self-wedge is assumed. -/
theorem formNativeP286GaugeWeakEquation_iff_residual_eq_zero
    (residual : BasePoint → FormNativeP286GaugeCoordinateTwoForm)
    (residualContinuous : Continuous residual) :
    FormNativeP286GaugeWeakEquation residual ↔ residual = 0 := by
  constructor
  · intro weakEquation
    funext point
    apply formNativeP286GaugeCoordinateWedgeCoefficient_separates_left
    intro direction
    rw [formNativeP286GaugeCoordinateWedgeCoefficient_symmetric]
    exact congrFun
      (formNativeP286GaugeWeakEquation_directionalCoefficient_eq_zero residual
        residualContinuous weakEquation direction) point
  · rintro rfl
    intro variation
    simp

/-! ## Stationarity and pointwise source-generated equation -/

/-- Compact-support coordinate stationarity of the active form-native action
in the actual primitive P286 auxiliary slot. -/
def FormNativeP286GaugeAuxiliaryActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation :
      CompactlySupportedSmoothVariation
        FormNativeP286GaugeCoordinateTwoForm,
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeP286GaugeAuxiliaryCoordinate configuration variation
            parameter))
      0 0

def FormNativeP286GaugeAuxiliaryWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  FormNativeP286GaugeWeakEquation fun point =>
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
      (sourceGeneratedUnifiedCouplings source) configuration point

def FormNativeP286GaugeAuxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField configuration point)

theorem formNativeP286GaugeAuxiliaryActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    FormNativeP286GaugeAuxiliaryActionStationary source chart configuration ↔
      FormNativeP286GaugeAuxiliaryWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicFormNativeIntegratedAction_p286GaugeAuxiliary_hasDerivAt source
        chart configuration smooth nondegenerate densityIntegrable variation
    have coefficientZero :
        (∫ point : BasePoint,
          holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
            (sourceGeneratedUnifiedCouplings source) configuration variation
            point) = 0 :=
      ((stationary variation).unique actual).symm
    simpa only [FormNativeP286GaugeAuxiliaryWeakEquation,
      FormNativeP286GaugeWeakEquation,
      holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_eq_pairing]
      using coefficientZero
  · intro weakEquation variation
    have actual :=
      holonomicFormNativeIntegratedAction_p286GaugeAuxiliary_hasDerivAt source
        chart configuration smooth nondegenerate densityIntegrable variation
    have coefficientZero :
        (∫ point : BasePoint,
          holonomicFormNativeP286GaugeCoordinateFirstVariationDensity
            (sourceGeneratedUnifiedCouplings source) configuration variation
            point) = 0 := by
      simpa only [FormNativeP286GaugeAuxiliaryWeakEquation,
        FormNativeP286GaugeWeakEquation,
        holonomicFormNativeP286GaugeCoordinateFirstVariationDensity_eq_pairing]
        using weakEquation variation
    simpa [coefficientZero] using actual

theorem formNativeP286GaugeAuxiliaryWeakEquation_iff_residual_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    FormNativeP286GaugeAuxiliaryWeakEquation source configuration ↔
      (fun point =>
        holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
          (sourceGeneratedUnifiedCouplings source) configuration point) = 0 :=
  formNativeP286GaugeWeakEquation_iff_residual_eq_zero _
    (holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_continuous
      (sourceGeneratedUnifiedCouplings source) configuration smooth
      nondegenerate)

theorem formNativeP286GaugeAuxiliaryResidual_eq_zero_iff_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (fun point =>
      holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings source) configuration point) = 0 ↔
      FormNativeP286GaugeAuxiliaryPointwiseEquation source configuration := by
  constructor
  · intro residualZero point
    apply (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField configuration point)).mp
    have coordinateZero := congrFun residualZero point
    have actualZero := congrArg
      formNativeP286GaugeCoordinateToActualLinear coordinateZero
    simpa [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate]
      using actualZero
  · intro equation
    funext point
    have actualZero := (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField configuration point)).mpr (equation point)
    simp [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate,
      actualZero]

/-- Compact-support stationarity of the active form-native action is exactly
the source-boundary pointwise constitutive equation on the same holonomic
configuration.  This characterizes the Euler zero fiber; it does not produce
a stationary solution witness. -/
theorem formNativeP286GaugeAuxiliaryActionStationary_iff_pointwiseEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    FormNativeP286GaugeAuxiliaryActionStationary source chart configuration ↔
      FormNativeP286GaugeAuxiliaryPointwiseEquation source configuration := by
  rw [formNativeP286GaugeAuxiliaryActionStationary_iff_weakEquation source
    chart configuration smooth nondegenerate densityIntegrable]
  rw [formNativeP286GaugeAuxiliaryWeakEquation_iff_residual_eq_zero source
    configuration smooth nondegenerate]
  exact formNativeP286GaugeAuxiliaryResidual_eq_zero_iff_pointwiseEquation
    source configuration

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeGaugeAuxiliaryIntegratedVariation
