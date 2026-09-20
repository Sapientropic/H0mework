import H0mework.Physics.ConnectionJets.P286SourceAffineCurvatureJetNormalForm
import H0mework.Physics.Source.PositiveNativeAlgebraicEliminationRegularity

/-!
# S9-C3h78a infrastructure: color-Cartan quadratic P286 connection jet

Jurisdiction: this module constructs one existing-field P286
connection second-jet carrier over the actual C3h70 `canonicalResponse`.  The
raw monomial is `x₁²`, with no source slot, supplied target, branch receipt, or
stationarity certificate.  Its real parameter is only a coordinate for the
downstream zero-fiber classification; it is not a primitive physical knob.

This first gate proves ordinary `ContDiff` variation/curvature APIs and the
origin preservation of the connection value, first jet, and actual
`dA + [A,A]` curvature.  It does not rebuild the constitutive auxiliary, state
an Euler--Lagrange zero, or claim closure of any larger P286 or joint shell.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286ColorCartanQuadraticConnectionJet

open ProofFreeRicherAnholonomicSource
open StageNineCoframeGravityGaugeRegularity
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseCoframeDefect
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNinePositiveSourceNativeAlgebraicEliminationRegularity
open StageNineResidualLimitLorentzClassObstruction
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Ordinary smooth P286 connection-variation API -/

/-- The production compact-support derivative identity only uses local
smoothness.  This is its ordinary `ContDiff` form for noncompact polynomial
jet classification. -/
theorem p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : BasePoint → P286GaugeOneForm)
    (variationSmooth : ContDiff ℝ ∞ variation)
    (parameter : ℝ) (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative configuration point
          derivativeDirection formDirection +
        parameter • p286GaugeVariationCoordinateDerivative variation point
          derivativeDirection formDirection := by
  have backgroundSmooth : ContDiff ℝ ∞ fun candidate =>
      holonomicP286GaugeConnectionCoordinate configuration candidate
        formDirection :=
    smooth.2.2.2.2.1 formDirection
  have variationDirectionSmooth : ContDiff ℝ ∞ fun candidate =>
      variation candidate formDirection :=
    contDiff_pi.mp variationSmooth formDirection
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate configuration candidate
          formDirection) point :=
    (backgroundSmooth.differentiable (by simp)).differentiableAt
  have variationDifferentiable : DifferentiableAt ℝ
      (fun candidate => variation candidate formDirection) point :=
    (variationDirectionSmooth.differentiable (by simp)).differentiableAt
  unfold p286GaugeConnectionCoordinateDerivative
    p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  have functionEquality :
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          (varyP286GaugeConnectionCoordinate configuration variation parameter)
          candidate formDirection) =
        fun candidate =>
          holonomicP286GaugeConnectionCoordinate configuration candidate
              formDirection +
            parameter • variation candidate formDirection := by
    funext candidate
    exact congrFun
      (holonomicP286GaugeConnectionCoordinate_vary configuration variation
        parameter candidate) formDirection
  rw [functionEquality]
  have derivativeEquality :
      fderiv ℝ
          (fun candidate =>
            holonomicP286GaugeConnectionCoordinate configuration candidate
                formDirection +
              parameter • variation candidate formDirection)
          point =
        fderiv ℝ
            (fun candidate =>
              holonomicP286GaugeConnectionCoordinate configuration candidate
                formDirection)
            point +
          parameter • fderiv ℝ
            (fun candidate => variation candidate formDirection) point := by
    exact (backgroundDifferentiable.hasFDerivAt.add
      (variationDifferentiable.hasFDerivAt.const_smul parameter)).fderiv
  rw [derivativeEquality]
  simp

/-- The same exact non-Abelian curvature expansion as the production compact
variation theorem, now for any ordinary smooth variation. -/
theorem holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : BasePoint → P286GaugeOneForm)
    (variationSmooth : ContDiff ℝ ∞ variation)
    (parameter : ℝ) (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point =
      holonomicP286GaugeCurvatureCoordinate configuration point +
        parameter •
          p286GaugeConnectionLinearCurvatureVariation configuration variation
            point +
        parameter ^ 2 •
          p286GaugeConnectionQuadraticCurvatureVariation variation point := by
  funext pair
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  rw [p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
      configuration smooth variation variationSmooth,
    p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
      configuration smooth variation variationSmooth]
  have variedConnection :=
    holonomicP286GaugeConnectionCoordinate_vary configuration variation
      parameter point
  rw [congrFun variedConnection (pairFirst pair),
    congrFun variedConnection (pairSecond pair)]
  simp only [Pi.add_apply, Pi.smul_apply,
    p286CoordinateLieBracket_add_left,
    p286CoordinateLieBracket_add_right,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right]
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  simp only [p286GaugeConnectionLinearCurvatureVariation,
    p286GaugeConnectionQuadraticCurvatureVariation]
  module

theorem varyP286GaugeConnectionCoordinate_smooth_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : BasePoint → P286GaugeOneForm)
    (variationSmooth : ContDiff ℝ ∞ variation)
    (parameter : ℝ) :
    (varyP286GaugeConnectionCoordinate configuration variation
      parameter).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  have variedGaugeConnectionSmooth : ∀ direction,
      ContDiff ℝ ∞ fun point =>
        p286CoordinateEquiv
          ((varyP286GaugeConnectionCoordinate configuration variation
            parameter).gaugeConnection point direction) := by
    intro direction
    have directionSmooth : ContDiff ℝ ∞ fun point =>
        variation point direction :=
      contDiff_pi.mp variationSmooth direction
    have scaledSmooth : ContDiff ℝ ∞ fun point =>
        parameter • variation point direction :=
      (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
        contDiff_const).smul directionSmooth
    simpa [varyP286GaugeConnectionCoordinate,
      holonomicP286GaugeConnectionCoordinate] using
        (gaugeConnectionSmooth direction).add scaledSmooth
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    gravityMultiplierSmooth, variedGaugeConnectionSmooth,
    gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
    conjugateMatterSmooth⟩

/-! ## Canonical raw `x₁²` color-Cartan jet -/

def colorCartanQuadraticCoordinate : P286CoordinateCarrier :=
  p286CoordinateEquiv colorCartanP286ConnectionDirection

/-- Raw `x₁²`, with no `1/2` normalization hidden in the carrier. -/
def colorCartanQuadraticCoefficient : BasePoint → ℝ :=
  (p286BaseCoordinate 1 : BasePoint → ℝ) * p286BaseCoordinate 1

@[simp] theorem colorCartanQuadraticCoefficient_origin :
    colorCartanQuadraticCoefficient (0 : BasePoint) = 0 := by
  simp [colorCartanQuadraticCoefficient]

theorem colorCartanQuadraticCoefficient_contDiff :
    ContDiff ℝ ∞ colorCartanQuadraticCoefficient := by
  exact (p286BaseCoordinate 1).contDiff.mul (p286BaseCoordinate 1).contDiff

theorem colorCartanQuadraticCoefficient_hasFDerivAt_origin :
    HasFDerivAt colorCartanQuadraticCoefficient
      (0 : BasePoint →L[ℝ] ℝ) (0 : BasePoint) := by
  have derivative :=
    ((p286BaseCoordinate 1).hasFDerivAt (x := (0 : BasePoint))).mul
      ((p286BaseCoordinate 1).hasFDerivAt (x := (0 : BasePoint)))
  simpa [colorCartanQuadraticCoefficient] using derivative

theorem colorCartanQuadraticCoefficient_hasFDerivAt
    (point : BasePoint) :
    HasFDerivAt colorCartanQuadraticCoefficient
      ((p286BaseCoordinate 1 point) • p286BaseCoordinate 1 +
        (p286BaseCoordinate 1 point) • p286BaseCoordinate 1) point := by
  have derivative :=
    ((p286BaseCoordinate 1).hasFDerivAt (x := point)).mul
      ((p286BaseCoordinate 1).hasFDerivAt (x := point))
  simpa [colorCartanQuadraticCoefficient] using derivative

theorem colorCartanQuadraticCoefficient_direction_one
    (point : BasePoint) :
    fieldDirectionalDerivative colorCartanQuadraticCoefficient point 1 =
      2 * point 1 := by
  unfold fieldDirectionalDerivative
  rw [(colorCartanQuadraticCoefficient_hasFDerivAt point).fderiv]
  simp [p286BaseCoordinate_apply, coordinateDirection]
  ring

/-- Canonical unit quadratic connection one-form.  Only spacetime component
`mu = 0` is changed, in the fixed color-Cartan direction. -/
def colorCartanQuadraticJet (point : BasePoint) : P286GaugeOneForm :=
  fun formDirection =>
    if formDirection = 0 then
      colorCartanQuadraticCoefficient point •
        colorCartanQuadraticCoordinate
    else 0

theorem colorCartanQuadraticJet_contDiff :
    ContDiff ℝ ∞ colorCartanQuadraticJet := by
  apply contDiff_pi.mpr
  intro formDirection
  by_cases directionZero : formDirection = 0
  · subst formDirection
    simp only [colorCartanQuadraticJet, if_pos]
    exact colorCartanQuadraticCoefficient_contDiff.smul contDiff_const
  · simp only [colorCartanQuadraticJet, if_neg directionZero]
    exact contDiff_const

@[simp] theorem colorCartanQuadraticJet_origin :
    colorCartanQuadraticJet (0 : BasePoint) = 0 := by
  funext formDirection
  simp [colorCartanQuadraticJet]

theorem colorCartanQuadraticJet_component_hasFDerivAt_origin
    (formDirection : LorentzianIndex) :
    HasFDerivAt (fun point => colorCartanQuadraticJet point formDirection)
      (0 : BasePoint →L[ℝ] P286CoordinateCarrier) (0 : BasePoint) := by
  by_cases directionZero : formDirection = 0
  · subst formDirection
    simpa [colorCartanQuadraticJet] using
      colorCartanQuadraticCoefficient_hasFDerivAt_origin.smul_const
        colorCartanQuadraticCoordinate
  · simpa [colorCartanQuadraticJet, directionZero] using
      (hasFDerivAt_const (x := (0 : BasePoint))
        (c := (0 : P286CoordinateCarrier)))

theorem colorCartanQuadraticJet_variationDerivative_one_zero
    (point : BasePoint) :
    p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet point 1 0 =
      (2 * point 1) • colorCartanQuadraticCoordinate := by
  have functionEquality :
      (fun candidate => colorCartanQuadraticJet candidate 0) =
        fun candidate => colorCartanQuadraticCoefficient candidate •
          colorCartanQuadraticCoordinate := by
    funext candidate
    simp [colorCartanQuadraticJet]
  have derivative :=
    (colorCartanQuadraticCoefficient_hasFDerivAt point).smul_const
      colorCartanQuadraticCoordinate
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  rw [functionEquality, derivative.fderiv]
  simp [p286BaseCoordinate_apply, coordinateDirection]
  module

theorem colorCartanQuadraticJet_variationDerivative_of_form_ne_zero
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex)
    (formDirectionNe : formDirection ≠ 0) :
    p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet point
        derivativeDirection formDirection = 0 := by
  have functionEquality :
      (fun candidate => colorCartanQuadraticJet candidate formDirection) =
        fun _ : BasePoint => (0 : P286CoordinateCarrier) := by
    funext candidate
    simp [colorCartanQuadraticJet, formDirectionNe]
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  rw [functionEquality]
  simp

@[simp] theorem colorCartanQuadraticJet_variationDerivative_origin
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative colorCartanQuadraticJet
        (0 : BasePoint) derivativeDirection formDirection = 0 := by
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  rw [(colorCartanQuadraticJet_component_hasFDerivAt_origin
    formDirection).fderiv]
  simp

/-- The parameter is retained only to classify the response zero fiber.  The
background is the actual C3h70 response, not the pre-response native input. -/
def colorCartanQuadraticKinematic (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate canonicalResponse
    colorCartanQuadraticJet parameter

theorem canonicalResponse_smooth_local : canonicalResponse.Smooth :=
  positiveSourceNativeGravityAlgebraicKeepResponse_reference_smooth

theorem canonicalResponse_p286ConnectionCoordinate_eq_actual
    (point : BasePoint) (formDirection : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate canonicalResponse point
        formDirection =
      actualSourceAffineCoordinate formDirection point := by
  change p286CoordinateEquiv
      ((positiveSourceNativeAlgebraicEliminationUpdate
        residualLimitLorentzCarrierReader).gaugeConnection point
          formDirection) = _
  rw [positiveSourceNativeAlgebraicEliminationUpdate_gaugeConnection]
  simp [actualSourceAffineCoordinate, sourceP286AffineConnectionField]

/-- The only derivative channel in pair `(0,1)` is `-∂₁(x₁² C)`.
The second term is the actual non-Abelian bracket with the same source-affine
background; it is retained rather than silently Abelianized. -/
theorem colorCartanQuadraticLinearCurvatureVariation_pair_zero
    (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 0 =
      -(2 * point 1) • colorCartanQuadraticCoordinate +
        colorCartanQuadraticCoefficient point •
          p286CoordinateLieBracket colorCartanQuadraticCoordinate
            (actualSourceAffineCoordinate 1 point) := by
  unfold p286GaugeConnectionLinearCurvatureVariation
  simp only [pairFirst, pairSecond, Matrix.cons_val_zero]
  rw [colorCartanQuadraticJet_variationDerivative_of_form_ne_zero
      point 0 1 (by decide),
    colorCartanQuadraticJet_variationDerivative_one_zero,
    canonicalResponse_p286ConnectionCoordinate_eq_actual point 1]
  have oneNeZero : (1 : LorentzianIndex) ≠ 0 := by decide
  simp only [colorCartanQuadraticJet, if_pos, if_neg oneNeZero,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_zero_right_local, add_zero, zero_sub]
  module

theorem colorCartanQuadraticLinearCurvature_pair_zero_direction_one_origin :
    fieldDirectionalDerivative
        (fun point =>
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point 0)
        0 1 =
      (-2 : ℝ) • colorCartanQuadraticCoordinate := by
  let linearJet : BasePoint →L[ℝ] P286CoordinateCarrier :=
    (-2 : ℝ) •
      (p286BaseCoordinate 1).smulRight colorCartanQuadraticCoordinate
  have bracketDerivative :=
    p286CoordinateLieBracketBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (hasFDerivAt_const colorCartanQuadraticCoordinate (0 : BasePoint))
        (actualSourceAffineCoordinate_hasFDerivAt 1 0)
  have productDerivativeRaw :=
    colorCartanQuadraticCoefficient_hasFDerivAt_origin.smul bracketDerivative
  have sumDerivative := linearJet.hasFDerivAt.add productDerivativeRaw
  have functionEquality :
      (fun point =>
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point 0) =
        (linearJet : BasePoint → P286CoordinateCarrier) +
          colorCartanQuadraticCoefficient • fun point =>
            p286CoordinateLieBracketBilinear.toContinuousBilinearMap
              colorCartanQuadraticCoordinate
              (actualSourceAffineCoordinate 1 point) := by
    funext point
    rw [colorCartanQuadraticLinearCurvatureVariation_pair_zero]
    change
      -(2 * point 1) • colorCartanQuadraticCoordinate +
          colorCartanQuadraticCoefficient point •
            p286CoordinateLieBracket colorCartanQuadraticCoordinate
              (actualSourceAffineCoordinate 1 point) =
        linearJet point +
          colorCartanQuadraticCoefficient point •
            p286CoordinateLieBracket colorCartanQuadraticCoordinate
              (actualSourceAffineCoordinate 1 point)
    simp only [linearJet, smul_apply,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply]
    module
  rw [functionEquality]
  unfold fieldDirectionalDerivative
  rw [sumDerivative.fderiv]
  simp [linearJet, coordinateDirection, p286BaseCoordinate_apply]

@[simp] theorem colorCartanQuadraticCurvatureVariation_zero
    (point : BasePoint) :
    p286GaugeConnectionQuadraticCurvatureVariation
        colorCartanQuadraticJet point = 0 := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeConnectionQuadraticCurvatureVariation,
      colorCartanQuadraticJet, pairFirst, pairSecond]

theorem colorCartanQuadraticKinematic_smooth (parameter : ℝ) :
    (colorCartanQuadraticKinematic parameter).Smooth := by
  exact varyP286GaugeConnectionCoordinate_smooth_of_contDiff
    canonicalResponse canonicalResponse_smooth_local
    colorCartanQuadraticJet colorCartanQuadraticJet_contDiff parameter

theorem colorCartanQuadraticKinematic_curvatureCoordinate_expansion
    (parameter : ℝ) (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticKinematic parameter) point =
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point +
        parameter •
          p286GaugeConnectionLinearCurvatureVariation canonicalResponse
            colorCartanQuadraticJet point := by
  unfold colorCartanQuadraticKinematic
  rw [holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff
    canonicalResponse canonicalResponse_smooth_local colorCartanQuadraticJet
    colorCartanQuadraticJet_contDiff]
  simp

theorem colorCartanQuadraticLinearCurvature_pair_zero_contDiff :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet point 0 := by
  have variedCurvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticKinematic 1) point 0 := by
    exact holonomicGaugeCurvature_coordinate_contDiff
      (colorCartanQuadraticKinematic 1)
      (colorCartanQuadraticKinematic_smooth 1) 0
  have backgroundCurvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0 := by
    exact holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 0
  have functionEquality :
      (fun point =>
        p286GaugeConnectionLinearCurvatureVariation canonicalResponse
          colorCartanQuadraticJet point 0) =
        fun point =>
          holonomicP286GaugeCurvatureCoordinate
              (colorCartanQuadraticKinematic 1) point 0 -
            holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0 := by
    funext point
    have expanded := congrFun
      (colorCartanQuadraticKinematic_curvatureCoordinate_expansion 1 point) 0
    simp only [Pi.add_apply, one_smul] at expanded
    rw [eq_sub_iff_add_eq, add_comm]
    exact expanded.symm
  rw [functionEquality]
  exact variedCurvatureSmooth.sub backgroundCurvatureSmooth

theorem colorCartanQuadraticKinematic_curvature_pair_zero_direction_one
    (parameter : ℝ) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (colorCartanQuadraticKinematic parameter) point 0)
        0 1 =
      fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0)
          0 1 +
        parameter • ((-2 : ℝ) • colorCartanQuadraticCoordinate) := by
  let backgroundField : BasePoint → P286CoordinateCarrier := fun point =>
    holonomicP286GaugeCurvatureCoordinate canonicalResponse point 0
  let linearField : BasePoint → P286CoordinateCarrier := fun point =>
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
      colorCartanQuadraticJet point 0
  have backgroundSmooth : ContDiff ℝ ∞ backgroundField := by
    exact holonomicGaugeCurvature_coordinate_contDiff canonicalResponse
      canonicalResponse_smooth_local 0
  have linearSmooth : ContDiff ℝ ∞ linearField :=
    colorCartanQuadraticLinearCurvature_pair_zero_contDiff
  have backgroundDifferentiableAt :
      DifferentiableAt ℝ backgroundField (0 : BasePoint) :=
    (backgroundSmooth.differentiable (by simp)).differentiableAt
  have linearDifferentiableAt :
      DifferentiableAt ℝ linearField (0 : BasePoint) :=
    (linearSmooth.differentiable (by simp)).differentiableAt
  have backgroundHasDerivative := backgroundDifferentiableAt.hasFDerivAt
  have linearHasDerivative := linearDifferentiableAt.hasFDerivAt
  have sumDerivative := backgroundHasDerivative.add
    (linearHasDerivative.const_smul parameter)
  have functionEquality :
      (fun point =>
        holonomicP286GaugeCurvatureCoordinate
          (colorCartanQuadraticKinematic parameter) point 0) =
        backgroundField + parameter • linearField := by
    funext point
    have expanded := congrFun
      (colorCartanQuadraticKinematic_curvatureCoordinate_expansion parameter
        point) 0
    simpa only [Pi.add_apply, Pi.smul_apply, backgroundField, linearField]
      using expanded
  have linearDerivative :=
    colorCartanQuadraticLinearCurvature_pair_zero_direction_one_origin
  unfold fieldDirectionalDerivative at linearDerivative ⊢
  rw [functionEquality, sumDerivative.fderiv]
  simp only [add_apply, smul_apply]
  dsimp only [backgroundField, linearField]
  rw [linearDerivative]

/-! ## Origin value, first jet, and curvature preservation -/

theorem colorCartanQuadraticKinematic_connectionCoordinate_origin
    (parameter : ℝ) :
    holonomicP286GaugeConnectionCoordinate
        (colorCartanQuadraticKinematic parameter) 0 =
      holonomicP286GaugeConnectionCoordinate canonicalResponse 0 := by
  unfold colorCartanQuadraticKinematic
  rw [holonomicP286GaugeConnectionCoordinate_vary]
  simp

theorem colorCartanQuadraticKinematic_gaugeConnection_origin
    (parameter : ℝ) :
    (colorCartanQuadraticKinematic parameter).gaugeConnection 0 =
      canonicalResponse.gaugeConnection 0 := by
  funext formDirection
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeConnectionCoordinate
        (colorCartanQuadraticKinematic parameter) 0 formDirection =
      holonomicP286GaugeConnectionCoordinate canonicalResponse 0 formDirection
  exact congrFun
    (colorCartanQuadraticKinematic_connectionCoordinate_origin parameter)
    formDirection

theorem colorCartanQuadraticKinematic_firstJet_origin
    (parameter : ℝ)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (colorCartanQuadraticKinematic parameter) 0 derivativeDirection
        formDirection =
      p286GaugeConnectionCoordinateDerivative canonicalResponse 0
        derivativeDirection formDirection := by
  simpa [colorCartanQuadraticKinematic] using
    (p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
      canonicalResponse canonicalResponse_smooth_local
      colorCartanQuadraticJet colorCartanQuadraticJet_contDiff parameter
      (0 : BasePoint) derivativeDirection formDirection)

@[simp] theorem colorCartanQuadraticLinearCurvatureVariation_origin :
    p286GaugeConnectionLinearCurvatureVariation canonicalResponse
        colorCartanQuadraticJet 0 = 0 := by
  funext pair
  simp [p286GaugeConnectionLinearCurvatureVariation]

@[simp] theorem colorCartanQuadraticCurvatureVariation_origin :
    p286GaugeConnectionQuadraticCurvatureVariation
        colorCartanQuadraticJet 0 = 0 := by
  funext pair
  simp [p286GaugeConnectionQuadraticCurvatureVariation]

theorem colorCartanQuadraticKinematic_curvatureCoordinate_origin
    (parameter : ℝ) :
    holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticKinematic parameter) 0 =
      holonomicP286GaugeCurvatureCoordinate canonicalResponse 0 := by
  simpa [colorCartanQuadraticKinematic] using
    (holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff
      canonicalResponse canonicalResponse_smooth_local
      colorCartanQuadraticJet colorCartanQuadraticJet_contDiff parameter
      (0 : BasePoint))

theorem colorCartanQuadraticKinematic_curvature_origin
    (parameter : ℝ) :
    holonomicGaugeCurvature (colorCartanQuadraticKinematic parameter) 0 =
      holonomicGaugeCurvature canonicalResponse 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeCurvatureCoordinate
        (colorCartanQuadraticKinematic parameter) 0 pair =
      holonomicP286GaugeCurvatureCoordinate canonicalResponse 0 pair
  exact congrFun
    (colorCartanQuadraticKinematic_curvatureCoordinate_origin parameter) pair

end

end SaturationMonoid.PhysicsCore.StageNineP286ColorCartanQuadraticConnectionJet
