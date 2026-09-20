import H0mework.Physics.GaugeAction.P286Bianchi
import H0mework.Physics.Holonomic.P286HolonomicSecondJetCarrier

/-!
# S9-C3h82b: curvature first-jet symbol of a holonomic P286 second jet

C3h82a declares the complete symmetric Hessian domain of the existing
primitive P286 connection.  This module derives its first visible transport:
the exterior curvature first-jet symbol

`H ↦ (rho, mu, nu ↦ H(rho, mu)_nu - H(rho, nu)_mu)`.

The symbol is real-linear and obeys the cyclic linearized Bianchi identity by
the Hessian symmetry alone.  More importantly, it is proved equal to the
actual origin curvature-derivative displacement of the primitive quadratic
installation over every smooth background.  Curvature is therefore still a
derived readout; it is not accepted as an independent source or field slot.

This is a local holonomic transporter/classifier.  It does not define the
constitutive or Euler--Lagrange response, choose a preimage, quotient a kernel,
or produce stationarity.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286HolonomicSecondJetCurvatureSymbol

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineP286Bianchi
open StageNineP286BracketCalculus
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open scoped ContDiff

noncomputable section

set_option autoImplicit false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Algebraic curvature first-jet symbol -/

abbrev P286GaugeCurvatureFirstJet :=
  LorentzianIndex → P286GaugeTwoForm

/-- Ordered version used by the cyclic Bianchi classifier. -/
def p286HolonomicSecondJetOrderedCurvatureSymbol
    (jet : P286HolonomicConnectionSecondJet)
    (derivativeDirection first second : LorentzianIndex) :
    P286CoordinateCarrier :=
  jet.1 (coordinateDirection derivativeDirection)
        (coordinateDirection first) second -
    jet.1 (coordinateDirection derivativeDirection)
        (coordinateDirection second) first

/-- Canonical six-pair readout of the ordered symbol. -/
def p286HolonomicSecondJetCurvatureSymbol :
    P286HolonomicConnectionSecondJet →ₗ[ℝ]
      P286GaugeCurvatureFirstJet where
  toFun jet derivativeDirection pair :=
    p286HolonomicSecondJetOrderedCurvatureSymbol jet derivativeDirection
      (pairFirst pair) (pairSecond pair)
  map_add' := by
    intro first second
    funext derivativeDirection pair
    simp [p286HolonomicSecondJetOrderedCurvatureSymbol]
    module
  map_smul' := by
    intro parameter jet
    funext derivativeDirection pair
    simp [p286HolonomicSecondJetOrderedCurvatureSymbol]
    module

@[simp] theorem p286HolonomicSecondJetCurvatureSymbol_apply
    (jet : P286HolonomicConnectionSecondJet)
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    p286HolonomicSecondJetCurvatureSymbol jet derivativeDirection pair =
      p286HolonomicSecondJetOrderedCurvatureSymbol jet derivativeDirection
        (pairFirst pair) (pairSecond pair) :=
  rfl

/-- The curvature symbol of every holonomic Hessian satisfies the cyclic
linearized Bianchi identity. -/
theorem p286HolonomicSecondJetOrderedCurvatureSymbol_bianchi
    (jet : P286HolonomicConnectionSecondJet)
    (first second third : LorentzianIndex) :
    p286HolonomicSecondJetOrderedCurvatureSymbol jet first second third +
        p286HolonomicSecondJetOrderedCurvatureSymbol jet second third first +
        p286HolonomicSecondJetOrderedCurvatureSymbol jet third first second =
      0 := by
  unfold p286HolonomicSecondJetOrderedCurvatureSymbol
  rw [p286HolonomicConnectionSecondJet_symmetric jet
      (coordinateDirection second) (coordinateDirection first),
    p286HolonomicConnectionSecondJet_symmetric jet
      (coordinateDirection third) (coordinateDirection first),
    p286HolonomicConnectionSecondJet_symmetric jet
      (coordinateDirection third) (coordinateDirection second)]
  abel

/-! ## Exact primitive-installation response -/

/-- Componentwise linear readout of one Hessian slot. -/
def p286HolonomicSecondJetComponentLinear
    (jet : P286HolonomicConnectionSecondJet)
    (innerDirection formDirection : LorentzianIndex) :
    BasePoint →L[ℝ] P286CoordinateCarrier :=
  (ContinuousLinearMap.proj formDirection).comp
    (jet.1.flip (coordinateDirection innerDirection))

@[simp] theorem p286HolonomicSecondJetComponentLinear_apply
    (jet : P286HolonomicConnectionSecondJet)
    (innerDirection formDirection : LorentzianIndex) (point : BasePoint) :
    p286HolonomicSecondJetComponentLinear jet innerDirection formDirection
        point =
      jet.1 point (coordinateDirection innerDirection) formDirection :=
  rfl

theorem p286HolonomicSecondJetQuadraticRealization_directionalDerivative
    (jet : P286HolonomicConnectionSecondJet) (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286HolonomicSecondJetQuadraticRealization jet) point direction =
      jet.1 point (coordinateDirection direction) := by
  unfold fieldDirectionalDerivative
  rw [(p286HolonomicSecondJetQuadraticRealization_hasFDerivAt
    jet point).fderiv]

theorem p286HolonomicSecondJetQuadraticRealization_variationDerivative
    (jet : P286HolonomicConnectionSecondJet) (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        (p286HolonomicSecondJetQuadraticRealization jet) point
        derivativeDirection formDirection =
      p286HolonomicSecondJetComponentLinear jet derivativeDirection
        formDirection point := by
  let evaluation : P286GaugeOneForm →L[ℝ] P286CoordinateCarrier :=
    ContinuousLinearMap.proj formDirection
  have componentDerivative : HasFDerivAt
      (fun candidate =>
        evaluation (p286HolonomicSecondJetQuadraticRealization jet candidate))
      (evaluation.comp (jet.1 point)) point := by
    exact evaluation.hasFDerivAt.comp point
      (p286HolonomicSecondJetQuadraticRealization_hasFDerivAt jet point)
  unfold p286GaugeVariationCoordinateDerivative fieldDirectionalDerivative
  change
    fderiv ℝ
        (fun candidate =>
          evaluation (p286HolonomicSecondJetQuadraticRealization jet candidate))
        point (coordinateDirection derivativeDirection) = _
  rw [componentDerivative.fderiv]
  rfl

private theorem fieldDirectionalDerivative_const_smul_clm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (parameter : ℝ) (linear : BasePoint →L[ℝ] V)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => parameter • linear candidate)
        point direction =
      parameter • linear (coordinateDirection direction) := by
  unfold fieldDirectionalDerivative
  have derivativeEquality :=
    ((linear.hasFDerivAt (x := point)).const_smul parameter).fderiv
  have evaluated := congrArg
    (fun derivative : BasePoint →L[ℝ] V =>
      derivative (coordinateDirection direction))
    derivativeEquality
  change
    (fderiv ℝ (parameter • (linear : BasePoint → V)) point)
        (coordinateDirection direction) =
      parameter • linear (coordinateDirection direction)
  simpa only [smul_apply] using evaluated

theorem installP286HolonomicConnectionSecondJet_connectionCoordinate_origin
    (configuration : StageNineHolonomicConfiguration)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (formDirection : LorentzianIndex) :
    connectionCoordinate
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 formDirection =
      connectionCoordinate configuration 0 formDirection := by
  exact congrFun
    (installP286HolonomicConnectionSecondJet_connection_origin configuration
      jet parameter)
    formDirection

theorem installP286HolonomicConnectionSecondJet_connectionDerivative_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (derivativeDirection formDirection : LorentzianIndex) :
    connectionCoordinateDerivative
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 derivativeDirection formDirection =
      connectionCoordinateDerivative configuration 0 derivativeDirection
        formDirection := by
  exact installP286HolonomicConnectionSecondJet_firstJet_origin configuration
    smooth jet parameter derivativeDirection formDirection

/-- The only new second derivative is the installed Hessian itself. -/
theorem installP286HolonomicConnectionSecondJet_connectionSecondDerivative_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (outerDirection innerDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          connectionCoordinateDerivative
            (installP286HolonomicConnectionSecondJet configuration jet
              parameter)
            point innerDirection formDirection)
        0 outerDirection =
      fieldDirectionalDerivative
          (fun point =>
            connectionCoordinateDerivative configuration point innerDirection
              formDirection)
          0 outerDirection +
        parameter •
          jet.1 (coordinateDirection outerDirection)
            (coordinateDirection innerDirection) formDirection := by
  let componentLinear :=
    p286HolonomicSecondJetComponentLinear jet innerDirection formDirection
  have functionEquality :
      (fun point =>
        connectionCoordinateDerivative
          (installP286HolonomicConnectionSecondJet configuration jet parameter)
          point innerDirection formDirection) =
        fun point =>
          connectionCoordinateDerivative configuration point innerDirection
              formDirection +
            parameter • componentLinear point := by
    funext point
    change
      p286GaugeConnectionCoordinateDerivative
          (varyP286GaugeConnectionCoordinate configuration
            (p286HolonomicSecondJetQuadraticRealization jet) parameter)
          point innerDirection formDirection = _
    rw [p286GaugeConnectionCoordinateDerivative_vary_of_contDiff configuration
      smooth (p286HolonomicSecondJetQuadraticRealization jet)
      (p286HolonomicSecondJetQuadraticRealization_contDiff jet)]
    rw [p286HolonomicSecondJetQuadraticRealization_variationDerivative]
    rfl
  rw [functionEquality]
  rw [fieldDirectionalDerivative_add_of_contDiff
    (fun point =>
      connectionCoordinateDerivative configuration point innerDirection
        formDirection)
    (fun point => parameter • componentLinear point)
    (connectionCoordinateDerivative_contDiff configuration smooth
      innerDirection formDirection)
    (ContDiff.const_smul parameter componentLinear.contDiff)]
  rw [fieldDirectionalDerivative_const_smul_clm]
  rfl

/-- Exact ordered-curvature derivative displacement induced by one installed
connection Hessian. -/
theorem installP286HolonomicConnectionSecondJet_orderedCurvatureDerivative_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (derivativeDirection first second : LorentzianIndex) :
    orderedCurvatureDirectionalDerivative
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 derivativeDirection first second =
      orderedCurvatureDirectionalDerivative configuration 0
          derivativeDirection first second +
        parameter •
          p286HolonomicSecondJetOrderedCurvatureSymbol jet
            derivativeDirection first second := by
  rw [orderedCurvatureDirectionalDerivative_eq_expansion
      (installP286HolonomicConnectionSecondJet configuration jet parameter)
      (installP286HolonomicConnectionSecondJet_smooth configuration smooth jet
        parameter),
    orderedCurvatureDirectionalDerivative_eq_expansion configuration smooth]
  unfold orderedCurvatureDerivativeExpansion
  rw [installP286HolonomicConnectionSecondJet_connectionSecondDerivative_origin
      configuration smooth jet parameter derivativeDirection first second,
    installP286HolonomicConnectionSecondJet_connectionSecondDerivative_origin
      configuration smooth jet parameter derivativeDirection second first,
    installP286HolonomicConnectionSecondJet_connectionDerivative_origin
      configuration smooth jet parameter derivativeDirection first,
    installP286HolonomicConnectionSecondJet_connectionDerivative_origin
      configuration smooth jet parameter derivativeDirection second,
    installP286HolonomicConnectionSecondJet_connectionCoordinate_origin
      configuration jet parameter first,
    installP286HolonomicConnectionSecondJet_connectionCoordinate_origin
      configuration jet parameter second]
  unfold p286HolonomicSecondJetOrderedCurvatureSymbol
  module

/-- Canonical six-pair form of the exact actual curvature first-jet response. -/
theorem installP286HolonomicConnectionSecondJet_curvatureDirectionalDerivative_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet) (parameter : ℝ)
    (derivativeDirection : LorentzianIndex) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (installP286HolonomicConnectionSecondJet configuration jet
              parameter)
            point pair)
        0 derivativeDirection =
      fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate configuration point pair)
          0 derivativeDirection +
        parameter •
          p286HolonomicSecondJetCurvatureSymbol jet derivativeDirection pair := by
  have installedFunction :
      (fun point =>
        holonomicP286GaugeCurvatureCoordinate
          (installP286HolonomicConnectionSecondJet configuration jet parameter)
          point pair) =
        fun point =>
          orderedCurvature
            (installP286HolonomicConnectionSecondJet configuration jet
              parameter)
            point (pairFirst pair) (pairSecond pair) := by
    funext point
    exact (orderedCurvature_canonicalPair_eq_holonomic
      (installP286HolonomicConnectionSecondJet configuration jet parameter)
      point pair).symm
  have backgroundFunction :
      (fun point =>
        holonomicP286GaugeCurvatureCoordinate configuration point pair) =
        fun point =>
          orderedCurvature configuration point (pairFirst pair)
            (pairSecond pair) := by
    funext point
    exact (orderedCurvature_canonicalPair_eq_holonomic configuration point
      pair).symm
  rw [installedFunction, backgroundFunction]
  exact
    installP286HolonomicConnectionSecondJet_orderedCurvatureDerivative_origin
      configuration smooth jet parameter derivativeDirection
      (pairFirst pair) (pairSecond pair)

/-! ## Positive and negative symbol regressions -/

/-- The general symbol recovers the already proved C3h78 curvature first-jet
increment in pair `(0,1)` and derivative direction `1`. -/
theorem colorCartanQuadraticHolonomicSecondJet_curvatureSymbol_pair_zero :
    p286HolonomicSecondJetCurvatureSymbol
        colorCartanQuadraticHolonomicSecondJet 1 0 =
      (-2 : ℝ) • colorCartanQuadraticCoordinate := by
  simp [p286HolonomicSecondJetCurvatureSymbol,
    p286HolonomicSecondJetOrderedCurvatureSymbol,
    colorCartanQuadraticHolonomicSecondJet,
    colorCartanQuadraticSecondJetAmbient,
    colorCartanQuadraticUnitOneForm,
    ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
    coordinateDirection, pairFirst, pairSecond]

theorem colorCartanQuadraticCoordinate_ne_zero :
    colorCartanQuadraticCoordinate ≠ 0 := by
  intro coordinateZero
  have typedZero : colorCartanP286ConnectionDirection = 0 := by
    apply p286CoordinateEquiv.injective
    simpa [colorCartanQuadraticCoordinate] using coordinateZero
  have entryZero := congrArg
    (fun data : P286LieBlockData =>
      (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0) typedZero
  norm_num [colorCartanP286ConnectionDirection, colorCartanGenerator,
    colorCartanRaw] at entryZero

/-- A longitudinal one-form direction: the Lie coordinate and the spacetime
quadratic direction both occupy slot `1`. -/
def longitudinalColorCartanQuadraticUnitOneForm : P286GaugeOneForm :=
  fun formDirection =>
    if formDirection = 1 then colorCartanQuadraticCoordinate else 0

def longitudinalColorCartanSecondJetAmbient :
    P286ConnectionSecondJetAmbient :=
  (2 : ℝ) •
    (p286BaseCoordinate 1).smulRight
      ((p286BaseCoordinate 1).smulRight
        longitudinalColorCartanQuadraticUnitOneForm)

theorem longitudinalColorCartanSecondJetAmbient_symmetric
    (first second : BasePoint) :
    longitudinalColorCartanSecondJetAmbient first second =
      longitudinalColorCartanSecondJetAmbient second first := by
  unfold longitudinalColorCartanSecondJetAmbient
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
    p286BaseCoordinate_apply]
  module

def longitudinalColorCartanHolonomicSecondJet :
    P286HolonomicConnectionSecondJet :=
  ⟨longitudinalColorCartanSecondJetAmbient,
    longitudinalColorCartanSecondJetAmbient_symmetric⟩

theorem longitudinalColorCartanHolonomicSecondJet_ne_zero :
    longitudinalColorCartanHolonomicSecondJet ≠ 0 := by
  intro jetZero
  have ambientZero := congrArg Subtype.val jetZero
  have evaluated := congrArg
    (fun jet : P286ConnectionSecondJetAmbient =>
      jet (coordinateDirection 1) (coordinateDirection 1) 1)
    ambientZero
  have coordinateZero : colorCartanQuadraticCoordinate = 0 := by
    have scaled := congrArg
      (fun coordinate : P286CoordinateCarrier => (1 / 2 : ℝ) • coordinate)
      evaluated
    simpa [longitudinalColorCartanHolonomicSecondJet,
      longitudinalColorCartanSecondJetAmbient,
      longitudinalColorCartanQuadraticUnitOneForm,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      coordinateDirection, smul_smul] using scaled
  exact colorCartanQuadraticCoordinate_ne_zero coordinateZero

/-- The exterior curvature symbol cannot see a purely longitudinal Hessian. -/
theorem longitudinalColorCartanHolonomicSecondJet_curvatureSymbol_eq_zero :
    p286HolonomicSecondJetCurvatureSymbol
        longitudinalColorCartanHolonomicSecondJet = 0 := by
  funext derivativeDirection pair
  fin_cases derivativeDirection <;> fin_cases pair <;>
    simp [p286HolonomicSecondJetCurvatureSymbol,
      p286HolonomicSecondJetOrderedCurvatureSymbol,
      longitudinalColorCartanHolonomicSecondJet,
      longitudinalColorCartanSecondJetAmbient,
      longitudinalColorCartanQuadraticUnitOneForm,
      ContinuousLinearMap.smulRight_apply, p286BaseCoordinate_apply,
      coordinateDirection, pairFirst, pairSecond]

theorem longitudinalColorCartanHolonomicSecondJet_mem_curvatureSymbol_kernel :
    longitudinalColorCartanHolonomicSecondJet ∈
      LinearMap.ker p286HolonomicSecondJetCurvatureSymbol :=
  longitudinalColorCartanHolonomicSecondJet_curvatureSymbol_eq_zero

theorem p286HolonomicSecondJetCurvatureSymbol_not_injective :
    ¬ Function.Injective p286HolonomicSecondJetCurvatureSymbol := by
  intro injective
  apply longitudinalColorCartanHolonomicSecondJet_ne_zero
  apply injective
  rw [longitudinalColorCartanHolonomicSecondJet_curvatureSymbol_eq_zero,
    map_zero]

end

end SaturationMonoid.PhysicsCore.StageNineP286HolonomicSecondJetCurvatureSymbol
