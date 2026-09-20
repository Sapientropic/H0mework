import H0mework.Physics.GaugeAction.TopologicalP286GaugeThreeFormDuality
import H0mework.Physics.Geometry.FundamentalLemma

/-!
# Topological P286 gauge weak equation

This module proves the faithful weak zero fiber of the metric-free P286 W13
pairing.  A continuous P286 three-form vanishes exactly when its pairing
against every compactly supported smooth P286 one-form has zero integral.

The theorem is formulation-neutral.  It consumes no action, source,
stationarity, current, auxiliary equation, connection, matter field, or
equation receipt.  Scalar compact bumps isolate every fixed one-form
direction before the complete finite-dimensional W13 dual separates the
residual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineTopologicalP286GaugeWeakEquation

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Weak vanishing against every genuine compactly supported smooth P286
connection one-form. -/
def TopologicalP286GaugeWeakEquation
    (residual : BasePoint → P286GaugeThreeForm) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeOneForm,
    (∫ point : BasePoint,
      p286GaugeOneFormThreeFormWedgeCoefficient
        (variation point) (residual point)) = 0

/-- Linear dependence of W13 on its three-form argument with a fixed P286
one-form direction. -/
def p286GaugeOneFormThreeFormWedgeRightLinear
    (direction : P286GaugeOneForm) :
    P286GaugeThreeForm →ₗ[ℝ] ℝ where
  toFun := p286GaugeOneFormThreeFormWedgeCoefficient direction
  map_add' :=
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right direction
  map_smul' := by
    intro parameter threeForm
    simpa only [RingHom.id_apply, smul_eq_mul] using
      p286GaugeOneFormThreeFormWedgeCoefficient_smul_right parameter direction
        threeForm

def p286GaugeOneFormThreeFormWedgeRightContinuousLinear
    (direction : P286GaugeOneForm) :
    P286GaugeThreeForm →L[ℝ] ℝ where
  toLinearMap := p286GaugeOneFormThreeFormWedgeRightLinear direction
  cont :=
    (p286GaugeOneFormThreeFormWedgeRightLinear direction)
      |>.continuous_of_finiteDimensional

@[simp] theorem p286GaugeOneFormThreeFormWedgeRightContinuousLinear_apply
    (direction : P286GaugeOneForm) (threeForm : P286GaugeThreeForm) :
    p286GaugeOneFormThreeFormWedgeRightContinuousLinear direction threeForm =
      p286GaugeOneFormThreeFormWedgeCoefficient direction threeForm :=
  rfl

/-- Multiply one fixed P286 one-form direction by a compact scalar bump. -/
def scalarTimesTopologicalP286GaugeVariation
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation P286GaugeOneForm where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesTopologicalP286GaugeVariation_apply
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesTopologicalP286GaugeVariation direction variation point =
      variation point • direction :=
  rfl

/-- Scalar coefficient read by one fixed P286 one-form direction. -/
def topologicalP286GaugeDirectionalCoefficient
    (residual : BasePoint → P286GaugeThreeForm)
    (direction : P286GaugeOneForm) : BasePoint → ℝ :=
  fun point =>
    p286GaugeOneFormThreeFormWedgeCoefficient direction (residual point)

theorem topologicalP286GaugeDirectionalCoefficient_continuous
    (residual : BasePoint → P286GaugeThreeForm)
    (residualContinuous : Continuous residual)
    (direction : P286GaugeOneForm) :
    Continuous
      (topologicalP286GaugeDirectionalCoefficient residual direction) := by
  change Continuous fun point =>
    p286GaugeOneFormThreeFormWedgeRightContinuousLinear direction
      (residual point)
  exact (p286GaugeOneFormThreeFormWedgeRightContinuousLinear direction)
    |>.continuous.comp residualContinuous

theorem p286GaugeOneFormThreeFormWedgeCoefficient_scalarTimes
    (residual : BasePoint → P286GaugeThreeForm)
    (direction : P286GaugeOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (scalarTimesTopologicalP286GaugeVariation direction variation point)
        (residual point) =
      variation point *
        topologicalP286GaugeDirectionalCoefficient residual direction point := by
  change p286GaugeOneFormThreeFormWedgeCoefficient
      (variation point • direction) (residual point) = _
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_smul_left]
  rfl

/-- The weak equation annihilates the continuous scalar coefficient seen by
every fixed P286 one-form direction. -/
theorem topologicalP286GaugeWeakEquation_directionalCoefficient_eq_zero
    (residual : BasePoint → P286GaugeThreeForm)
    (residualContinuous : Continuous residual)
    (weakEquation : TopologicalP286GaugeWeakEquation residual)
    (direction : P286GaugeOneForm) :
    topologicalP286GaugeDirectionalCoefficient residual direction = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (topologicalP286GaugeDirectionalCoefficient residual direction)
    (topologicalP286GaugeDirectionalCoefficient_continuous
      residual residualContinuous direction)
  intro variation
  have weakDirection := weakEquation
    (scalarTimesTopologicalP286GaugeVariation direction variation)
  have integrandEquality :
      (fun point : BasePoint =>
        p286GaugeOneFormThreeFormWedgeCoefficient
          (scalarTimesTopologicalP286GaugeVariation direction variation point)
          (residual point)) =
        fun point => variation point *
          topologicalP286GaugeDirectionalCoefficient residual direction point := by
    funext point
    exact p286GaugeOneFormThreeFormWedgeCoefficient_scalarTimes
      residual direction variation point
  rw [integrandEquality] at weakDirection
  exact weakDirection

/-- Dependency-light P286 W13 weak fundamental lemma. -/
theorem topologicalP286GaugeWeakEquation_iff_residual_eq_zero
    (residual : BasePoint → P286GaugeThreeForm)
    (residualContinuous : Continuous residual) :
    TopologicalP286GaugeWeakEquation residual ↔ residual = 0 := by
  constructor
  · intro weakEquation
    funext point
    have dualZero :
        p286GaugeThreeFormWedgeLinearDual (residual point) = 0 := by
      apply LinearMap.ext
      intro direction
      have coefficientZero := congrFun
        (topologicalP286GaugeWeakEquation_directionalCoefficient_eq_zero
          residual residualContinuous weakEquation direction) point
      simpa [topologicalP286GaugeDirectionalCoefficient] using coefficientZero
    exact
      (p286GaugeThreeFormWedgeLinearDual_eq_zero_iff
        (residual point)).mp dualZero
  · rintro rfl
    intro variation
    simp [p286GaugeOneFormThreeFormWedgeCoefficient]

end

end
  SaturationMonoid.PhysicsCore.StageNineTopologicalP286GaugeWeakEquation
