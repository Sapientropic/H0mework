import H0mework.Physics.Holonomic.HolonomicField

/-!
# Stage-9 dependency-light coframe first-jet calculus

This module owns the Fréchet first-jet readout of an actual primitive coframe
field and its canonical affine right inverse.  It depends only on the early
holonomic field layer, so source geometry need not import the later historical
residual-limit chain merely to state that a stored affine jet is the derivative
of the generated coframe.

No nondegeneracy, connection, curvature, field equation, target, or receipt is
accepted by these definitions.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeFirstJet

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField

noncomputable section

open scoped ContDiff

set_option autoImplicit false

/-- Extensionality for the raw coframe value and complete derivative tensor. -/
theorem coframeJet_eq_of_fields_eq
    (first second : PointwiseLorentzianCoframeJet)
    (coframe : first.coframe = second.coframe)
    (derivative : first.derivative = second.derivative) :
    first = second := by
  cases first with
  | mk firstCoframe firstDerivative =>
      cases second with
      | mk secondCoframe secondDerivative =>
          change firstCoframe = secondCoframe at coframe
          change firstDerivative = secondDerivative at derivative
          subst secondCoframe
          subst secondDerivative
          rfl

/-- Continuous projection onto one coordinate of the existing Euclidean base
chart. -/
def coframeBaseCoordinate
    (direction : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj direction).comp
    (EuclideanSpace.equiv LorentzianIndex ℝ).toContinuousLinearMap

@[simp] theorem coframeBaseCoordinate_apply
    (direction : LorentzianIndex) (point : BasePoint) :
    coframeBaseCoordinate direction point = point direction :=
  rfl

@[simp] theorem coframeBaseCoordinate_coordinateDirection
    (first second : LorentzianIndex) :
    coframeBaseCoordinate first (coordinateDirection second) =
      if first = second then 1 else 0 := by
  fin_cases first <;> fin_cases second <;>
    simp [coframeBaseCoordinate, coordinateDirection]

/-- One component of a coframe first derivative as a continuous linear
functional on the base chart. -/
def coframeJetAffineComponentLinear
    (jet : PointwiseLorentzianCoframeJet)
    (internal coordinate : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    jet.derivative derivativeDirection internal coordinate •
      coframeBaseCoordinate derivativeDirection

theorem coframeJetAffineComponentLinear_coordinateDirection
    (jet : PointwiseLorentzianCoframeJet)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    coframeJetAffineComponentLinear jet internal coordinate
        (coordinateDirection derivativeDirection) =
      jet.derivative derivativeDirection internal coordinate := by
  fin_cases derivativeDirection <;>
    simp [coframeJetAffineComponentLinear, coframeBaseCoordinate,
      coordinateDirection, Fin.sum_univ_four]

/-- Canonical affine field integrating one already-generated coframe jet. -/
def affineCoframeFieldOfJet
    (jet : PointwiseLorentzianCoframeJet) :
    BasePoint → LorentzianCoframe :=
  fun point internal coordinate =>
    jet.coframe internal coordinate +
      coframeJetAffineComponentLinear jet internal coordinate point

@[simp] theorem affineCoframeFieldOfJet_origin
    (jet : PointwiseLorentzianCoframeJet) :
    affineCoframeFieldOfJet jet 0 = jet.coframe := by
  ext internal coordinate
  simp [affineCoframeFieldOfJet]

theorem affineCoframeFieldOfJet_componentwiseSmooth
    (jet : PointwiseLorentzianCoframeJet)
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      affineCoframeFieldOfJet jet point internal coordinate := by
  simpa [affineCoframeFieldOfJet] using
    (contDiff_const.add
      (coframeJetAffineComponentLinear jet internal coordinate).contDiff)

theorem affineCoframeFieldOfJet_directionalDerivative
    (jet : PointwiseLorentzianCoframeJet)
    (point : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    fderiv ℝ
        (fun candidate =>
          affineCoframeFieldOfJet jet candidate internal coordinate)
        point (coordinateDirection derivativeDirection) =
      jet.derivative derivativeDirection internal coordinate := by
  rw [show
    fderiv ℝ
        (fun candidate =>
          affineCoframeFieldOfJet jet candidate internal coordinate) point =
      coframeJetAffineComponentLinear jet internal coordinate by
    exact ((coframeJetAffineComponentLinear jet internal coordinate).hasFDerivAt
      |>.const_add (jet.coframe internal coordinate)).fderiv]
  exact coframeJetAffineComponentLinear_coordinateDirection
    jet derivativeDirection internal coordinate

/-- Actual first jet read from a primitive coframe field by Fréchet
differentiation. -/
def holonomicCoframeFirstJetAt
    (field : BasePoint → LorentzianCoframe)
    (point : BasePoint) : PointwiseLorentzianCoframeJet where
  coframe := field point
  derivative := fun derivativeDirection internal coordinate =>
    fderiv ℝ (fun candidate => field candidate internal coordinate) point
      (coordinateDirection derivativeDirection)

/-- The affine integration reads back its complete first jet at the origin. -/
theorem holonomicCoframeFirstJetAt_affine_origin
    (jet : PointwiseLorentzianCoframeJet) :
    holonomicCoframeFirstJetAt (affineCoframeFieldOfJet jet) 0 = jet := by
  apply coframeJet_eq_of_fields_eq
  · exact affineCoframeFieldOfJet_origin _
  · funext derivativeDirection internal coordinate
    exact affineCoframeFieldOfJet_directionalDerivative _ 0
      derivativeDirection internal coordinate

end

end SaturationMonoid.PhysicsCore.StageNineCoframeFirstJet
