import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryEquation

/-!
# S9-C3a: primitive P286 connection variation

This module varies the actual primitive P286 connection rather than an
independent curvature or current slot.  In chosen finite coordinates it proves
the exact non-Abelian jet identity

`F(A + t η) = F(A) + t D_A η + t² [η,η]`

and transports the same primitive variation through the scalar and exterior
Dirac covariant derivatives.  The coordinate carrier is only a finite
analytic chart on the already typed P286 Lie algebra; no equation, current, or
stationarity certificate is stored in the variation mouth.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariation

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open scoped ContDiff

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

/-- Finite real coordinates for one P286 connection one-form. -/
abbrev P286GaugeOneForm :=
  LorentzianIndex → P286CoordinateCarrier

def holonomicP286GaugeConnectionCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeOneForm :=
  fun direction =>
    p286CoordinateEquiv (configuration.gaugeConnection point direction)

/-- The only connection variation mouth used below.  It changes the
primitive typed P286 connection and leaves every other primitive field
unchanged. -/
def varyP286GaugeConnectionCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gaugeConnection := fun point direction =>
      p286CoordinateEquiv.symm
        (holonomicP286GaugeConnectionCoordinate configuration point direction +
          parameter • variation point direction) }

@[simp] theorem holonomicP286GaugeConnectionCoordinate_vary
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (parameter : ℝ)
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point =
      holonomicP286GaugeConnectionCoordinate configuration point +
        parameter • variation point := by
  funext direction
  simp [holonomicP286GaugeConnectionCoordinate,
    varyP286GaugeConnectionCoordinate]

@[simp] theorem varyP286GaugeConnectionCoordinate_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) :
    varyP286GaugeConnectionCoordinate configuration variation 0 =
      configuration := by
  cases configuration
  simp [varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate]

def p286GaugeConnectionCoordinateDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative
    (fun candidate =>
      holonomicP286GaugeConnectionCoordinate configuration candidate
        formDirection)
    point derivativeDirection

theorem p286GaugeConnectionCoordinateDerivative_eq
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative configuration point
        derivativeDirection formDirection =
      p286CoordinateEquiv
        (p286ConnectionDerivative configuration point derivativeDirection
          formDirection) := by
  simp [p286GaugeConnectionCoordinateDerivative,
    holonomicP286GaugeConnectionCoordinate, p286ConnectionDerivative,
    fieldDirectionalDerivative]

def p286GaugeVariationCoordinateDerivative
    (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative
    (fun candidate => variation candidate formDirection)
    point derivativeDirection

theorem p286GaugeConnectionCoordinateDerivative_vary
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
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
  have variationSmooth : ContDiff ℝ ∞ fun candidate =>
      variation candidate formDirection :=
    contDiff_pi.mp variation.smooth formDirection
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate configuration candidate
          formDirection) point :=
    (backgroundSmooth.differentiable (by simp)).differentiableAt
  have variationDifferentiable : DifferentiableAt ℝ
      (fun candidate => variation candidate formDirection) point :=
    (variationSmooth.differentiable (by simp)).differentiableAt
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
    have varied := congrFun
      (holonomicP286GaugeConnectionCoordinate_vary configuration variation
        parameter candidate) formDirection
    exact varied
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

/-- The coefficient of `t` in the curvature of `A + tη`.  Both ordered
bracket channels are retained, so this is the actual coordinate expression
for `D_A η`. -/
def p286GaugeConnectionLinearCurvatureVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) : P286GaugeTwoForm :=
  fun pair =>
    p286GaugeVariationCoordinateDerivative variation point
        (pairFirst pair) (pairSecond pair) -
      p286GaugeVariationCoordinateDerivative variation point
        (pairSecond pair) (pairFirst pair) +
      p286CoordinateLieBracket
        (variation point (pairFirst pair))
        (holonomicP286GaugeConnectionCoordinate configuration point
          (pairSecond pair)) +
      p286CoordinateLieBracket
        (holonomicP286GaugeConnectionCoordinate configuration point
          (pairFirst pair))
        (variation point (pairSecond pair))

/-- The genuinely non-Abelian coefficient of `t²` in the varied curvature. -/
def p286GaugeConnectionQuadraticCurvatureVariation
    (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) : P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateLieBracket
      (variation point (pairFirst pair))
      (variation point (pairSecond pair))

theorem holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (pair : Fin 6) :
    holonomicP286GaugeCurvatureCoordinate configuration point pair =
      p286GaugeConnectionCoordinateDerivative configuration point
          (pairFirst pair) (pairSecond pair) -
        p286GaugeConnectionCoordinateDerivative configuration point
          (pairSecond pair) (pairFirst pair) +
        p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate configuration point
            (pairFirst pair))
          (holonomicP286GaugeConnectionCoordinate configuration point
            (pairSecond pair)) := by
  unfold holonomicP286GaugeCurvatureCoordinate holonomicGaugeCurvature
  rw [map_add, map_sub]
  rw [← p286GaugeConnectionCoordinateDerivative_eq,
    ← p286GaugeConnectionCoordinateDerivative_eq]
  simp [p286CoordinateLieBracket,
    holonomicP286GaugeConnectionCoordinate]

theorem holonomicP286GaugeCurvatureCoordinate_expansion
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
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
  rw [p286GaugeConnectionCoordinateDerivative_vary configuration smooth,
    p286GaugeConnectionCoordinateDerivative_vary configuration smooth]
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

def colorCartanP286ConnectionDirection : P286LieBlockData :=
  (colorCartanGenerator, 0, 0)

def colorMixingP286ConnectionDirection : P286LieBlockData :=
  (colorMixingGenerator, 0, 0)

theorem colorP286ConnectionDirections_bracket_ne_zero :
    p286LieBracket colorCartanP286ConnectionDirection
        colorMixingP286ConnectionDirection ≠ 0 := by
  intro bracketZero
  have colorZero := congrArg (fun data : P286LieBlockData => data.1)
    bracketZero
  exact colorGenerators_bracket_ne_zero
    (by simpa [p286LieBracket, colorCartanP286ConnectionDirection,
      colorMixingP286ConnectionDirection] using colorZero)

def nonAbelianP286ConnectionOneForm : P286GaugeOneForm :=
  fun direction =>
    if direction = 0 then
      p286CoordinateEquiv colorCartanP286ConnectionDirection
    else if direction = 1 then
      p286CoordinateEquiv colorMixingP286ConnectionDirection
    else 0

/-- An explicit compactly supported P286 connection variation whose
quadratic curvature channel is nonzero at the bump center. -/
def nonAbelianCompactP286ConnectionVariation :
    CompactlySupportedSmoothVariation P286GaugeOneForm where
  toFun := fun point =>
    nonzeroCompactScalarVariation point • nonAbelianP286ConnectionOneForm
  smooth := nonzeroCompactScalarVariation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := nonzeroCompactScalarVariation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

theorem nonAbelianCompactP286ConnectionVariation_center :
    nonAbelianCompactP286ConnectionVariation (0 : BasePoint) =
      nonAbelianP286ConnectionOneForm := by
  have bumpOne : nonzeroCompactScalarVariation (0 : BasePoint) = 1 := by
    apply unitCompactBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self unitCompactBump.rIn_pos.le
  change unitCompactBump (0 : BasePoint) • nonAbelianP286ConnectionOneForm =
    nonAbelianP286ConnectionOneForm
  rw [show unitCompactBump (0 : BasePoint) = 1 by exact bumpOne]
  exact one_smul ℝ nonAbelianP286ConnectionOneForm

/-- Negative regression against Abelianization: the `t²[η,η]` term of the
actual P286 connection variation cannot be erased. -/
theorem nonAbelianP286ConnectionQuadraticCurvature_ne_zero :
    p286GaugeConnectionQuadraticCurvatureVariation
        nonAbelianCompactP286ConnectionVariation (0 : BasePoint) 0 ≠ 0 := by
  have center := nonAbelianCompactP286ConnectionVariation_center
  change nonAbelianCompactP286ConnectionVariation.toFun (0 : BasePoint) =
    nonAbelianP286ConnectionOneForm at center
  unfold p286GaugeConnectionQuadraticCurvatureVariation
  rw [center]
  have firstZero : pairFirst (0 : Fin 6) = 0 := by decide
  have secondOne : pairSecond (0 : Fin 6) = 1 := by decide
  rw [firstZero, secondOne]
  simp only [nonAbelianP286ConnectionOneForm, if_pos,
    show (0 : LorentzianIndex) ≠ 1 by decide]
  unfold p286CoordinateLieBracket
  simp only [p286CoordinateEquiv.symm_apply_apply]
  exact fun coordinateZero =>
    colorP286ConnectionDirections_bracket_ne_zero
      (p286CoordinateEquiv.injective (by simpa using coordinateZero))

/-! ## The same primitive variation reaches scalar and matter jets -/

theorem p286LieBlockEmbed_real_smul
    (parameter : ℝ) (data : P286LieBlockData) :
    p286LieBlockEmbed (parameter • data) =
      parameter • p286LieBlockEmbed data := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock]

theorem fundamentalMotherLieAction_add
    (first second : SU7MotherLieMatrix) :
    fundamentalMotherLieAction (first + second) =
      fundamentalMotherLieAction first + fundamentalMotherLieAction second := by
  apply LinearMap.ext
  intro vector
  funext row
  simp [fundamentalMotherLieAction, Matrix.mulVecLin, Matrix.mulVec]

theorem fundamentalMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    fundamentalMotherLieAction (parameter • matrix) =
      (parameter : ℂ) • fundamentalMotherLieAction matrix := by
  apply LinearMap.ext
  intro vector
  funext row
  simp [fundamentalMotherLieAction, Matrix.mulVecLin, Matrix.mulVec]

def exteriorBasisInput
    (degree : ℕ) (index : ExteriorBasisIndex degree) :
    Fin degree → SU7FundamentalCarrier :=
  fun position =>
    su7FundamentalBasis (exteriorPositionEquiv index position).1

def exteriorBasisLieActionInput
    (degree : ℕ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) (position : Fin degree) :
    Fin degree → SU7FundamentalCarrier :=
  fun candidate =>
    if candidate = position then
      fundamentalMotherLieAction matrix
        (su7FundamentalBasis (exteriorPositionEquiv index candidate).1)
    else
      su7FundamentalBasis (exteriorPositionEquiv index candidate).1

theorem exteriorBasisLieActionTerm_eq_update
    (degree : ℕ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) (position : Fin degree) :
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree matrix index position) =
      (exteriorPower.ιMulti ℂ degree)
        (Function.update (exteriorBasisInput degree index) position
          (fundamentalMotherLieAction matrix
            (exteriorBasisInput degree index position))) := by
  apply congrArg (exteriorPower.ιMulti ℂ degree)
  funext candidate
  by_cases equality : candidate = position
  · subst candidate
    simp [exteriorBasisLieActionInput, exteriorBasisInput]
  · simp [exteriorBasisLieActionInput, exteriorBasisInput, equality]

theorem exteriorBasisLieAction_add
    (degree : ℕ) (first second : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorBasisLieAction degree (first + second) index =
      exteriorBasisLieAction degree first index +
        exteriorBasisLieAction degree second index := by
  unfold exteriorBasisLieAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro position _
  change
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (first + second) index position) =
      (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree first index position) +
        (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree second index position)
  rw [exteriorBasisLieActionTerm_eq_update,
    exteriorBasisLieActionTerm_eq_update,
    exteriorBasisLieActionTerm_eq_update]
  rw [fundamentalMotherLieAction_add, LinearMap.add_apply]
  exact (exteriorPower.ιMulti ℂ degree).map_update_add
    (exteriorBasisInput degree index) position
    (fundamentalMotherLieAction first
      (exteriorBasisInput degree index position))
    (fundamentalMotherLieAction second
      (exteriorBasisInput degree index position))

theorem exteriorBasisLieAction_real_smul
    (degree : ℕ) (parameter : ℝ) (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorBasisLieAction degree (parameter • matrix) index =
      (parameter : ℂ) • exteriorBasisLieAction degree matrix index := by
  unfold exteriorBasisLieAction
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro position _
  change
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (parameter • matrix) index
          position) =
      (parameter : ℂ) •
        (exteriorPower.ιMulti ℂ degree)
          (exteriorBasisLieActionInput degree matrix index position)
  rw [exteriorBasisLieActionTerm_eq_update,
    exteriorBasisLieActionTerm_eq_update]
  rw [fundamentalMotherLieAction_real_smul, LinearMap.smul_apply]
  exact (exteriorPower.ιMulti ℂ degree).map_update_smul
    (exteriorBasisInput degree index) position (parameter : ℂ)
    (fundamentalMotherLieAction matrix
      (exteriorBasisInput degree index position))

theorem exteriorMotherLieAction_add
    (degree : ℕ) (first second : SU7MotherLieMatrix) :
    exteriorMotherLieAction degree (first + second) =
      exteriorMotherLieAction degree first +
        exteriorMotherLieAction degree second := by
  apply LinearMap.ext
  intro field
  unfold exteriorMotherLieAction
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    exteriorBasisLieAction_add, smul_add, Finset.sum_add_distrib]

theorem exteriorMotherLieAction_real_smul
    (degree : ℕ) (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    exteriorMotherLieAction degree (parameter • matrix) =
      (parameter : ℂ) • exteriorMotherLieAction degree matrix := by
  apply LinearMap.ext
  intro field
  unfold exteriorMotherLieAction
  simp only [LinearMap.coe_mk, AddHom.coe_mk,
    exteriorBasisLieAction_real_smul, LinearMap.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  module

theorem exteriorSpinorMotherLieAction_add
    (first second : SU7MotherLieMatrix) :
    exteriorSpinorMotherLieAction (first + second) =
      exteriorSpinorMotherLieAction first +
        exteriorSpinorMotherLieAction second := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  simp [exteriorSpinorMotherLieAction, exteriorMotherLieAction_add]

theorem exteriorSpinorMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    exteriorSpinorMotherLieAction (parameter • matrix) =
      (parameter : ℂ) • exteriorSpinorMotherLieAction matrix := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  simp [exteriorSpinorMotherLieAction, exteriorMotherLieAction_real_smul]

theorem diracExteriorMotherLieAction_add
    (first second : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (first + second) =
      diracExteriorMotherLieAction first +
        diracExteriorMotherLieAction second := by
  apply LinearMap.ext
  intro matter
  funext spinIndex
  simp [diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction_add]

theorem diracExteriorMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (parameter • matrix) =
      (parameter : ℂ) • diracExteriorMotherLieAction matrix := by
  apply LinearMap.ext
  intro matter
  funext spinIndex
  simp [diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction_real_smul]

theorem scalarMotherLieAction_add
    (first second : SU7MotherLieMatrix)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction (first + second) scalar =
      scalarMotherLieAction first scalar +
        scalarMotherLieAction second scalar := by
  unfold scalarMotherLieAction
  rw [exteriorMotherLieAction_add, LinearMap.add_apply, map_add]

theorem scalarMotherLieAction_real_smul
    (parameter : ℝ) (matrix : SU7MotherLieMatrix)
    (scalar : ScalarCoordinateCarrier) :
    scalarMotherLieAction (parameter • matrix) scalar =
      parameter • scalarMotherLieAction matrix scalar := by
  unfold scalarMotherLieAction
  rw [exteriorMotherLieAction_real_smul, LinearMap.smul_apply, map_smul]
  rfl

theorem gaugeConnection_varyP286GaugeConnectionCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (parameter : ℝ)
    (point : BasePoint) (direction : LorentzianIndex) :
    (varyP286GaugeConnectionCoordinate configuration variation parameter).gaugeConnection
        point direction =
      configuration.gaugeConnection point direction +
        parameter • p286CoordinateEquiv.symm (variation point direction) := by
  simp [varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate]

def p286GaugeConnectionMotherVariation
    (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) (direction : LorentzianIndex) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (p286CoordinateEquiv.symm (variation point direction))

def holonomicScalarGaugeConnectionVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) (direction : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  scalarMotherLieAction
    (p286GaugeConnectionMotherVariation variation point direction)
    (configuration.scalar point)

def holonomicMatterGaugeConnectionVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm)
    (point : BasePoint) (direction : LorentzianIndex) :
    DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction
    (p286GaugeConnectionMotherVariation variation point direction)
    (configuration.matter point)

theorem holonomicScalarCovariantDerivative_gaugeConnection_expansion
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (parameter : ℝ)
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point direction =
      holonomicScalarCovariantDerivative configuration point direction +
        parameter • holonomicScalarGaugeConnectionVariation
          configuration variation point direction := by
  unfold holonomicScalarCovariantDerivative
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  change
    fieldDirectionalDerivative configuration.scalar point direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            ((varyP286GaugeConnectionCoordinate configuration variation
              parameter).gaugeConnection point direction))
          (configuration.scalar point) = _
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    p286LieBlockEmbed_add, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_add, scalarMotherLieAction_real_smul]
  module

theorem holonomicMatterCovariantDerivative_gaugeConnection_expansion
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (parameter : ℝ)
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point direction =
      holonomicMatterCovariantDerivative configuration point direction +
        parameter • holonomicMatterGaugeConnectionVariation
          configuration variation point direction := by
  unfold holonomicMatterCovariantDerivative
    holonomicMatterGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  change
    matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun candidate => matterCoordinateEquiv (configuration.matter candidate))
            point direction) +
        diracMatrixMatterAction
          (diracSpinConnectionLift (configuration.gravityConnection point)
            direction)
          (configuration.matter point) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            ((varyP286GaugeConnectionCoordinate configuration variation
              parameter).gaugeConnection point direction))
        (configuration.matter point) = _
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    p286LieBlockEmbed_add, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_add,
    diracExteriorMotherLieAction_real_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  module

/-- One primitive variation simultaneously generates the non-Abelian
curvature jet and both charged covariant-derivative jets.  None of these
three outputs can be independently hand-filled. -/
theorem p286GaugeConnectionVariation_generates_all_chargedJets
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        (varyP286GaugeConnectionCoordinate configuration variation parameter)
        point =
      holonomicP286GaugeCurvatureCoordinate configuration point +
        parameter •
          p286GaugeConnectionLinearCurvatureVariation configuration variation
            point +
        parameter ^ 2 •
          p286GaugeConnectionQuadraticCurvatureVariation variation point ∧
      (∀ direction,
        holonomicScalarCovariantDerivative
            (varyP286GaugeConnectionCoordinate configuration variation
              parameter)
            point direction =
          holonomicScalarCovariantDerivative configuration point direction +
            parameter • holonomicScalarGaugeConnectionVariation
              configuration variation point direction) ∧
      (∀ direction,
        holonomicMatterCovariantDerivative
            (varyP286GaugeConnectionCoordinate configuration variation
              parameter)
            point direction =
          holonomicMatterCovariantDerivative configuration point direction +
            parameter • holonomicMatterGaugeConnectionVariation
              configuration variation point direction) :=
  ⟨holonomicP286GaugeCurvatureCoordinate_expansion configuration smooth
      variation parameter point,
    holonomicScalarCovariantDerivative_gaugeConnection_expansion
      configuration variation parameter point,
    holonomicMatterCovariantDerivative_gaugeConnection_expansion
      configuration variation parameter point⟩

end

end SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariation
