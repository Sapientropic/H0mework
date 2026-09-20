import H0mework.Physics.GaugeAction.P286SourceRelativeWardAlgebra
import H0mework.Physics.GaugeAction.TopologicalP286GaugeThreeFormDuality
import H0mework.Physics.Cartan.ResidualLinearPlebanskiTorsionReduction

/-!
# Form-native P286 gauge geometric kinematics

This module constructs the actual coordinate first jet of the live P286
auxiliary field and its explicit exterior covariant derivative `D_A B`.  It
also splits the primitive connection curvature tangent into exterior and
algebraic channels and proves that the algebraic channel pairs with the
connection-action part of `D_A B` through the canonical P286 W13 pairing.

All declarations are off-shell kinematics or trace-pairing identities.  They
consume no action equation, stationarity receipt, current, residual zero,
auxiliary equation, inverse constitutive operator, source branch, or fixed
actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeGeometricKinematics

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286BracketCalculus
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286SourceRelativeWardAlgebra
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Oriented P286 two-form components -/

/-- Recover an ordered spacetime two-form component from the canonical
`(01,02,03,23,31,12)` coordinate order. -/
def orderedP286GaugeTwoFormComponent
    (form : P286GaugeTwoForm) (first second : LorentzianIndex) :
    P286CoordinateCarrier :=
  ∑ pair : Fin 6,
    orientedLorentzBivectorBasisCoefficient pair first second • form pair

theorem orderedP286GaugeTwoFormComponent_add
    (firstForm secondForm : P286GaugeTwoForm)
    (first second : LorentzianIndex) :
    orderedP286GaugeTwoFormComponent (firstForm + secondForm) first second =
      orderedP286GaugeTwoFormComponent firstForm first second +
        orderedP286GaugeTwoFormComponent secondForm first second := by
  unfold orderedP286GaugeTwoFormComponent
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

@[simp] theorem orderedP286GaugeTwoFormComponent_zero
    (first second : LorentzianIndex) :
    orderedP286GaugeTwoFormComponent 0 first second = 0 := by
  simp [orderedP286GaugeTwoFormComponent]

@[simp] theorem orderedP286GaugeTwoFormComponent_zero_one
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 0 1 = form 0 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_zero_two
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 0 2 = form 1 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_zero_three
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 0 3 = form 2 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_two_three
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 2 3 = form 3 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_three_one
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 3 1 = form 4 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_one_two
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 1 2 = form 5 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_one_zero
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 1 0 = -form 0 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_two_zero
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 2 0 = -form 1 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_three_zero
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 3 0 = -form 2 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_three_two
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 3 2 = -form 3 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_one_three
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 1 3 = -form 4 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

@[simp] theorem orderedP286GaugeTwoFormComponent_two_one
    (form : P286GaugeTwoForm) :
    orderedP286GaugeTwoFormComponent form 2 1 = -form 5 := by
  simp [orderedP286GaugeTwoFormComponent,
    orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
    Fin.sum_univ_six]

/-! ## Explicit exterior covariant derivative -/

/-- Adjoint action of one P286 connection coordinate on a P286 two-form. -/
def p286GaugeTwoFormAdjoint
    (generator : P286CoordinateCarrier) (form : P286GaugeTwoForm) :
    P286GaugeTwoForm :=
  fun pair => p286CoordinateLieBracket generator (form pair)

/-- Covariant derivative of one pointwise P286 two-form jet in one spacetime
direction. -/
def pointwiseP286GaugeTwoFormCovariantDerivative
    (connection : P286GaugeOneForm)
    (value : P286GaugeTwoForm)
    (derivative : LorentzianIndex → P286GaugeTwoForm)
    (direction : LorentzianIndex) : P286GaugeTwoForm :=
  derivative direction + p286GaugeTwoFormAdjoint (connection direction) value

/-- Pure exterior derivative of a P286 two-form first jet. -/
def pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
    (derivative : LorentzianIndex → P286GaugeTwoForm) : P286GaugeThreeForm :=
  fun triple =>
    orderedP286GaugeTwoFormComponent
        (derivative (threeFormFirst triple))
        (threeFormSecond triple) (threeFormThird triple) +
      orderedP286GaugeTwoFormComponent
        (derivative (threeFormSecond triple))
        (threeFormThird triple) (threeFormFirst triple) +
      orderedP286GaugeTwoFormComponent
        (derivative (threeFormThird triple))
        (threeFormFirst triple) (threeFormSecond triple)

/-- Explicit typed P286 exterior covariant derivative. -/
def pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    (connection : P286GaugeOneForm)
    (value : P286GaugeTwoForm)
    (derivative : LorentzianIndex → P286GaugeTwoForm) :
    P286GaugeThreeForm :=
  fun triple =>
    orderedP286GaugeTwoFormComponent
        (pointwiseP286GaugeTwoFormCovariantDerivative connection value
          derivative (threeFormFirst triple))
        (threeFormSecond triple) (threeFormThird triple) +
      orderedP286GaugeTwoFormComponent
        (pointwiseP286GaugeTwoFormCovariantDerivative connection value
          derivative (threeFormSecond triple))
        (threeFormThird triple) (threeFormFirst triple) +
      orderedP286GaugeTwoFormComponent
        (pointwiseP286GaugeTwoFormCovariantDerivative connection value
          derivative (threeFormThird triple))
        (threeFormFirst triple) (threeFormSecond triple)

/-- Connection-action channel of `D_A B`. -/
def pointwiseP286GaugeTwoFormConnectionExteriorAction
    (connection : P286GaugeOneForm) (value : P286GaugeTwoForm) :
    P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative connection value 0

/-- The connection-action channel is linear in its auxiliary two-form.
This public subtraction law is the shared algebraic seam used when a live
auxiliary write is compared with its constitutive anchor. -/
theorem pointwiseP286GaugeTwoFormConnectionExteriorAction_sub_right
    (connection : P286GaugeOneForm)
    (first second : P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction connection
        (first - second) =
      pointwiseP286GaugeTwoFormConnectionExteriorAction connection first -
        pointwiseP286GaugeTwoFormConnectionExteriorAction connection second := by
  have bracketSub
      (generator firstValue secondValue : P286CoordinateCarrier) :
      p286CoordinateLieBracket generator (firstValue - secondValue) =
        p286CoordinateLieBracket generator firstValue -
          p286CoordinateLieBracket generator secondValue := by
    rw [sub_eq_add_neg, p286CoordinateLieBracket_add_right]
    rw [show -secondValue = (-1 : ℝ) • secondValue by simp,
      p286CoordinateLieBracket_smul_right]
    simp [sub_eq_add_neg]
  have adjointSub
      (generator : P286CoordinateCarrier) :
      p286GaugeTwoFormAdjoint generator (first - second) =
        p286GaugeTwoFormAdjoint generator first -
          p286GaugeTwoFormAdjoint generator second := by
    funext pair
    exact bracketSub generator (first pair) (second pair)
  have orderedSub
      (firstForm secondForm : P286GaugeTwoForm)
      (firstDirection secondDirection : LorentzianIndex) :
      orderedP286GaugeTwoFormComponent (firstForm - secondForm)
          firstDirection secondDirection =
        orderedP286GaugeTwoFormComponent firstForm firstDirection
            secondDirection -
          orderedP286GaugeTwoFormComponent secondForm firstDirection
            secondDirection := by
    unfold orderedP286GaugeTwoFormComponent
    simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
  funext triple
  simp only [pointwiseP286GaugeTwoFormConnectionExteriorAction,
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
    pointwiseP286GaugeTwoFormCovariantDerivative,
    Pi.zero_apply, zero_add, adjointSub, orderedSub, Pi.sub_apply]
  module

theorem pointwiseP286GaugeTwoFormExteriorCovariantDerivative_eq_parts
    (connection : P286GaugeOneForm)
    (value : P286GaugeTwoForm)
    (derivative : LorentzianIndex → P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative connection value
        derivative =
      pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative derivative +
        pointwiseP286GaugeTwoFormConnectionExteriorAction connection value := by
  funext triple
  simp [pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative,
    pointwiseP286GaugeTwoFormConnectionExteriorAction,
    pointwiseP286GaugeTwoFormCovariantDerivative,
    orderedP286GaugeTwoFormComponent_add]
  abel

/-! ## Same-actual holonomic derivative -/

/-- Actual directional derivative of the full faithful auxiliary-coordinate
two-form. -/
def p286GaugeAuxiliaryDirectionalDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) : P286GaugeTwoForm :=
  fieldDirectionalDerivative
    (holonomicP286GaugeAuxiliaryCoordinate configuration) point direction

/-- Actual `D_A B` generated by the primitive P286 connection and auxiliary
field on the same holonomic configuration. -/
def holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    (holonomicP286GaugeConnectionCoordinate configuration point)
    (holonomicP286GaugeAuxiliaryCoordinate configuration point)
    (p286GaugeAuxiliaryDirectionalDerivative configuration point)

def holonomicP286GaugeAuxiliaryExteriorDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
    (p286GaugeAuxiliaryDirectionalDerivative configuration point)

theorem holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative configuration point =
      holonomicP286GaugeAuxiliaryExteriorDerivative configuration point +
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate configuration point)
          (holonomicP286GaugeAuxiliaryCoordinate configuration point) :=
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative_eq_parts _ _ _

/-! ## Primitive curvature-tangent split -/

def p286GaugeConnectionExteriorDerivativeVariation
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    P286GaugeTwoForm :=
  fun pair =>
    p286GaugeVariationCoordinateDerivative variation point
        (pairFirst pair) (pairSecond pair) -
      p286GaugeVariationCoordinateDerivative variation point
        (pairSecond pair) (pairFirst pair)

def p286GaugeConnectionAlgebraicCurvatureVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateLieBracket
        (variation point (pairFirst pair))
        (holonomicP286GaugeConnectionCoordinate configuration point
          (pairSecond pair)) +
      p286CoordinateLieBracket
        (holonomicP286GaugeConnectionCoordinate configuration point
          (pairFirst pair))
        (variation point (pairSecond pair))

def p286GaugeConnectionAlgebraicCurvatureDirection
    (connection direction : P286GaugeOneForm) : P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateLieBracket (direction (pairFirst pair))
        (connection (pairSecond pair)) +
      p286CoordinateLieBracket (connection (pairFirst pair))
        (direction (pairSecond pair))

theorem p286GaugeConnectionLinearCurvatureVariation_eq_parts
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation configuration variation point =
      p286GaugeConnectionExteriorDerivativeVariation variation point +
      p286GaugeConnectionAlgebraicCurvatureVariation configuration variation
          point := by
  funext pair
  unfold p286GaugeConnectionLinearCurvatureVariation
    p286GaugeConnectionExteriorDerivativeVariation
    p286GaugeConnectionAlgebraicCurvatureVariation
  simp only [Pi.add_apply]
  abel

/-! ## Trace-invariant algebraic W22--W13 seam -/

theorem p286CoordinateLieBracket_skew
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracket first second =
      -p286CoordinateLieBracket second first := by
  unfold p286CoordinateLieBracket
  rw [p286LieBracket_skew, map_neg]

theorem p286CoordinateLiePairing_adjoint_skew
    (generator first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing
          (p286CoordinateLieBracket generator first) second +
        p286CoordinateLiePairing first
          (p286CoordinateLieBracket generator second) = 0 := by
  calc
    p286CoordinateLiePairing
          (p286CoordinateLieBracket generator first) second +
        p286CoordinateLiePairing first
          (p286CoordinateLieBracket generator second) =
      p286CoordinateLiePairing generator
          (p286CoordinateLieBracket first second) +
        p286CoordinateLiePairing
          (p286CoordinateLieBracket generator second) first := by
            rw [p286CoordinateLiePairing_bracket_left,
              p286CoordinateLiePairing_symmetric first
                (p286CoordinateLieBracket generator second)]
    _ = p286CoordinateLiePairing generator
          (p286CoordinateLieBracket first second) +
        p286CoordinateLiePairing generator
          (p286CoordinateLieBracket second first) := by
            rw [p286CoordinateLiePairing_bracket_left]
    _ = 0 := by
      rw [p286CoordinateLieBracket_skew second first]
      rw [show -p286CoordinateLieBracket first second =
          (-1 : ℝ) • p286CoordinateLieBracket first second by simp,
        p286CoordinateLiePairing_smul_right]
      ring

private theorem p286CoordinateLiePairing_variation_connection
    (auxiliary variation connection : P286CoordinateCarrier) :
    p286CoordinateLiePairing auxiliary
        (p286CoordinateLieBracket variation connection) =
      p286CoordinateLiePairing variation
        (p286CoordinateLieBracket connection auxiliary) := by
  rw [p286CoordinateLiePairing_symmetric auxiliary]
  exact p286CoordinateLiePairing_bracket_left variation connection auxiliary

private theorem p286CoordinateLiePairing_connection_variation
    (auxiliary connection variation : P286CoordinateCarrier) :
    p286CoordinateLiePairing auxiliary
        (p286CoordinateLieBracket connection variation) =
      -p286CoordinateLiePairing variation
        (p286CoordinateLieBracket connection auxiliary) := by
  have invariant :=
    p286CoordinateLiePairing_adjoint_skew connection auxiliary variation
  rw [p286CoordinateLiePairing_symmetric
    (p286CoordinateLieBracket connection auxiliary) variation] at invariant
  linarith

private theorem p286CoordinateLiePairing_neg_right
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

private def p286GaugeAlgebraicWedgeNormalForm
    (connection direction : P286GaugeOneForm)
    (auxiliary : P286GaugeTwoForm) : ℝ :=
  p286CoordinateLiePairing (direction 0)
      (p286CoordinateLieBracket (connection 1) (auxiliary 3)) +
    p286CoordinateLiePairing (direction 0)
      (p286CoordinateLieBracket (connection 2) (auxiliary 4)) +
    p286CoordinateLiePairing (direction 0)
      (p286CoordinateLieBracket (connection 3) (auxiliary 5)) -
    p286CoordinateLiePairing (direction 1)
      (p286CoordinateLieBracket (connection 0) (auxiliary 3)) +
    p286CoordinateLiePairing (direction 1)
      (p286CoordinateLieBracket (connection 2) (auxiliary 2)) -
    p286CoordinateLiePairing (direction 1)
      (p286CoordinateLieBracket (connection 3) (auxiliary 1)) -
    p286CoordinateLiePairing (direction 2)
      (p286CoordinateLieBracket (connection 0) (auxiliary 4)) -
    p286CoordinateLiePairing (direction 2)
      (p286CoordinateLieBracket (connection 1) (auxiliary 2)) +
    p286CoordinateLiePairing (direction 2)
      (p286CoordinateLieBracket (connection 3) (auxiliary 0)) -
    p286CoordinateLiePairing (direction 3)
      (p286CoordinateLieBracket (connection 0) (auxiliary 5)) +
    p286CoordinateLiePairing (direction 3)
      (p286CoordinateLieBracket (connection 1) (auxiliary 1)) -
    p286CoordinateLiePairing (direction 3)
      (p286CoordinateLieBracket (connection 2) (auxiliary 0))

private theorem p286TopologicalGaugeBF_algebraic_eq_normalForm
    (connection direction : P286GaugeOneForm)
    (auxiliary : P286GaugeTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing auxiliary
        (p286GaugeConnectionAlgebraicCurvatureDirection connection direction) =
      p286GaugeAlgebraicWedgeNormalForm connection direction auxiliary := by
  have h0a :
      p286CoordinateLiePairing (auxiliary 0)
          (p286CoordinateLieBracket (direction 2) (connection 3)) =
        p286CoordinateLiePairing (direction 2)
          (p286CoordinateLieBracket (connection 3) (auxiliary 0)) :=
    p286CoordinateLiePairing_variation_connection _ _ _
  have h0b :
      p286CoordinateLiePairing (auxiliary 0)
          (p286CoordinateLieBracket (connection 2) (direction 3)) =
        -p286CoordinateLiePairing (direction 3)
          (p286CoordinateLieBracket (connection 2) (auxiliary 0)) :=
    p286CoordinateLiePairing_connection_variation _ _ _
  have h1a :
      p286CoordinateLiePairing (auxiliary 1)
          (p286CoordinateLieBracket (direction 3) (connection 1)) =
        p286CoordinateLiePairing (direction 3)
          (p286CoordinateLieBracket (connection 1) (auxiliary 1)) :=
    p286CoordinateLiePairing_variation_connection _ _ _
  have h1b :
      p286CoordinateLiePairing (auxiliary 1)
          (p286CoordinateLieBracket (connection 3) (direction 1)) =
        -p286CoordinateLiePairing (direction 1)
          (p286CoordinateLieBracket (connection 3) (auxiliary 1)) :=
    p286CoordinateLiePairing_connection_variation _ _ _
  have h2a :
      p286CoordinateLiePairing (auxiliary 2)
          (p286CoordinateLieBracket (direction 1) (connection 2)) =
        p286CoordinateLiePairing (direction 1)
          (p286CoordinateLieBracket (connection 2) (auxiliary 2)) :=
    p286CoordinateLiePairing_variation_connection _ _ _
  have h2b :
      p286CoordinateLiePairing (auxiliary 2)
          (p286CoordinateLieBracket (connection 1) (direction 2)) =
        -p286CoordinateLiePairing (direction 2)
          (p286CoordinateLieBracket (connection 1) (auxiliary 2)) :=
    p286CoordinateLiePairing_connection_variation _ _ _
  have h3a :
      p286CoordinateLiePairing (auxiliary 3)
          (p286CoordinateLieBracket (direction 0) (connection 1)) =
        p286CoordinateLiePairing (direction 0)
          (p286CoordinateLieBracket (connection 1) (auxiliary 3)) :=
    p286CoordinateLiePairing_variation_connection _ _ _
  have h3b :
      p286CoordinateLiePairing (auxiliary 3)
          (p286CoordinateLieBracket (connection 0) (direction 1)) =
        -p286CoordinateLiePairing (direction 1)
          (p286CoordinateLieBracket (connection 0) (auxiliary 3)) :=
    p286CoordinateLiePairing_connection_variation _ _ _
  have h4a :
      p286CoordinateLiePairing (auxiliary 4)
          (p286CoordinateLieBracket (direction 0) (connection 2)) =
        p286CoordinateLiePairing (direction 0)
          (p286CoordinateLieBracket (connection 2) (auxiliary 4)) :=
    p286CoordinateLiePairing_variation_connection _ _ _
  have h4b :
      p286CoordinateLiePairing (auxiliary 4)
          (p286CoordinateLieBracket (connection 0) (direction 2)) =
        -p286CoordinateLiePairing (direction 2)
          (p286CoordinateLieBracket (connection 0) (auxiliary 4)) :=
    p286CoordinateLiePairing_connection_variation _ _ _
  have h5a :
      p286CoordinateLiePairing (auxiliary 5)
          (p286CoordinateLieBracket (direction 0) (connection 3)) =
        p286CoordinateLiePairing (direction 0)
          (p286CoordinateLieBracket (connection 3) (auxiliary 5)) :=
    p286CoordinateLiePairing_variation_connection _ _ _
  have h5b :
      p286CoordinateLiePairing (auxiliary 5)
          (p286CoordinateLieBracket (connection 0) (direction 3)) =
        -p286CoordinateLiePairing (direction 3)
          (p286CoordinateLieBracket (connection 0) (auxiliary 5)) :=
    p286CoordinateLiePairing_connection_variation _ _ _
  unfold generatedTwoFormWedgeCoefficient
    p286GaugeConnectionAlgebraicCurvatureDirection
  rw [Fin.sum_univ_six]
  simp [twoFormComplement, pairFirst, pairSecond]
  simp only [p286CoordinateLiePairing_add_right]
  rw [h0a, h0b, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b, h5a, h5b]
  unfold p286GaugeAlgebraicWedgeNormalForm
  ring

private theorem p286GaugeW13_connectionAction_eq_normalForm
    (connection direction : P286GaugeOneForm)
    (auxiliary : P286GaugeTwoForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (pointwiseP286GaugeTwoFormConnectionExteriorAction connection
          auxiliary) =
      p286GaugeAlgebraicWedgeNormalForm connection direction auxiliary := by
  simp [p286GaugeOneFormThreeFormWedgeCoefficient,
    pointwiseP286GaugeTwoFormConnectionExteriorAction,
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
    pointwiseP286GaugeTwoFormCovariantDerivative,
    p286GaugeTwoFormAdjoint, p286GaugeAlgebraicWedgeNormalForm,
    oneWedgeThreeSign, missingTripleOfOneForm,
    threeFormFirst, threeFormSecond, threeFormThird,
    Fin.sum_univ_four, p286CoordinateLiePairing_add_right,
    p286CoordinateLiePairing_neg_right]
  ring

/-- Exact pointwise seam for the algebraic connection channel. -/
theorem p286TopologicalGaugeBF_algebraicCurvatureDirection_eq_w13
    (connection direction : P286GaugeOneForm)
    (auxiliary : P286GaugeTwoForm) :
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing auxiliary
        (p286GaugeConnectionAlgebraicCurvatureDirection connection direction) =
      p286GaugeOneFormThreeFormWedgeCoefficient direction
        (pointwiseP286GaugeTwoFormConnectionExteriorAction connection
          auxiliary) := by
  rw [p286TopologicalGaugeBF_algebraic_eq_normalForm,
    p286GaugeW13_connectionAction_eq_normalForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeGeometricKinematics
