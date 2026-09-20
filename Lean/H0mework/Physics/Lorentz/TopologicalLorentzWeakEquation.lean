import H0mework.Physics.Lorentz.TopologicalLorentzThreeFormDuality
import H0mework.Physics.Geometry.FundamentalLemma

/-!
# Topological Lorentz weak equation

This module proves the faithful weak zero fiber of the metric-free W13
pairing.  A continuous physical-bivector three-form vanishes exactly when its
pairing against every compactly supported smooth lowered Lorentz one-form has
zero integral.

The theorem is formulation-neutral.  It consumes no action, source,
stationarity, coframe, nondegeneracy, connection, matter field, or equation
receipt.  Scalar compact bumps isolate every fixed one-form direction before
the already faithful finite-dimensional W13 dual separates the residual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineTopologicalLorentzWeakEquation

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff

noncomputable section

set_option autoImplicit false

/-- Weak vanishing against every genuine compactly supported smooth lowered
Lorentz one-form. -/
def TopologicalLorentzWeakEquation
    (residual : BasePoint → PhysicalBivectorThreeForm) : Prop :=
  ∀ variation :
      CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    (∫ point : BasePoint,
      lorentzOneFormThreeFormWedgeCoefficient
        (variation point) (residual point)) = 0

/-- Continuous-linear dependence of W13 on its three-form argument with a
fixed one-form direction. -/
def lorentzOneFormThreeFormWedgeRightLinear
    (direction : LorentzBivectorOneForm) :
    PhysicalBivectorThreeForm →ₗ[ℝ] ℝ where
  toFun := lorentzOneFormThreeFormWedgeCoefficient direction
  map_add' :=
    lorentzOneFormThreeFormWedgeCoefficient_add_right direction
  map_smul' := by
    intro parameter threeForm
    simpa only [RingHom.id_apply, smul_eq_mul] using
      lorentzOneFormThreeFormWedgeCoefficient_smul_right parameter direction
        threeForm

def lorentzOneFormThreeFormWedgeRightContinuousLinear
    (direction : LorentzBivectorOneForm) :
    PhysicalBivectorThreeForm →L[ℝ] ℝ where
  toLinearMap := lorentzOneFormThreeFormWedgeRightLinear direction
  cont :=
    (lorentzOneFormThreeFormWedgeRightLinear direction)
      |>.continuous_of_finiteDimensional

@[simp] theorem lorentzOneFormThreeFormWedgeRightContinuousLinear_apply
    (direction : LorentzBivectorOneForm)
    (threeForm : PhysicalBivectorThreeForm) :
    lorentzOneFormThreeFormWedgeRightContinuousLinear direction threeForm =
      lorentzOneFormThreeFormWedgeCoefficient direction threeForm :=
  rfl

/-- Multiply one fixed Lorentz direction by a compact scalar bump. -/
def scalarTimesTopologicalLorentzVariation
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation LorentzBivectorOneForm where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesTopologicalLorentzVariation_apply
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesTopologicalLorentzVariation direction variation point =
      variation point • direction :=
  rfl

/-- Scalar coefficient read by one fixed lowered Lorentz direction. -/
def topologicalLorentzDirectionalCoefficient
    (residual : BasePoint → PhysicalBivectorThreeForm)
    (direction : LorentzBivectorOneForm) : BasePoint → ℝ :=
  fun point =>
    lorentzOneFormThreeFormWedgeCoefficient direction (residual point)

theorem topologicalLorentzDirectionalCoefficient_continuous
    (residual : BasePoint → PhysicalBivectorThreeForm)
    (residualContinuous : Continuous residual)
    (direction : LorentzBivectorOneForm) :
    Continuous
      (topologicalLorentzDirectionalCoefficient residual direction) := by
  change Continuous fun point =>
    lorentzOneFormThreeFormWedgeRightContinuousLinear direction
      (residual point)
  exact (lorentzOneFormThreeFormWedgeRightContinuousLinear direction)
    |>.continuous.comp residualContinuous

theorem lorentzOneFormThreeFormWedgeCoefficient_scalarTimes
    (residual : BasePoint → PhysicalBivectorThreeForm)
    (direction : LorentzBivectorOneForm)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    lorentzOneFormThreeFormWedgeCoefficient
        (scalarTimesTopologicalLorentzVariation direction variation point)
        (residual point) =
      variation point *
        topologicalLorentzDirectionalCoefficient residual direction point := by
  change lorentzOneFormThreeFormWedgeCoefficient
      (variation point • direction) (residual point) = _
  rw [lorentzOneFormThreeFormWedgeCoefficient_smul_left]
  rfl

/-- The weak equation annihilates the continuous scalar coefficient seen by
every fixed one-form direction. -/
theorem topologicalLorentzWeakEquation_directionalCoefficient_eq_zero
    (residual : BasePoint → PhysicalBivectorThreeForm)
    (residualContinuous : Continuous residual)
    (weakEquation : TopologicalLorentzWeakEquation residual)
    (direction : LorentzBivectorOneForm) :
    topologicalLorentzDirectionalCoefficient residual direction = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (topologicalLorentzDirectionalCoefficient residual direction)
    (topologicalLorentzDirectionalCoefficient_continuous
      residual residualContinuous direction)
  intro variation
  have weakDirection := weakEquation
    (scalarTimesTopologicalLorentzVariation direction variation)
  have integrandEquality :
      (fun point : BasePoint =>
        lorentzOneFormThreeFormWedgeCoefficient
          (scalarTimesTopologicalLorentzVariation direction variation point)
          (residual point)) =
        fun point => variation point *
          topologicalLorentzDirectionalCoefficient residual direction point := by
    funext point
    exact lorentzOneFormThreeFormWedgeCoefficient_scalarTimes
      residual direction variation point
  rw [integrandEquality] at weakDirection
  exact weakDirection

/-- Dependency-light W13 weak fundamental lemma. -/
theorem topologicalLorentzWeakEquation_iff_residual_eq_zero
    (residual : BasePoint → PhysicalBivectorThreeForm)
    (residualContinuous : Continuous residual) :
    TopologicalLorentzWeakEquation residual ↔ residual = 0 := by
  constructor
  · intro weakEquation
    funext point
    have dualZero :
        lorentzThreeFormWedgeContinuousDual (residual point) = 0 := by
      apply ContinuousLinearMap.ext
      intro direction
      have coefficientZero := congrFun
        (topologicalLorentzWeakEquation_directionalCoefficient_eq_zero
          residual residualContinuous weakEquation direction) point
      simpa [topologicalLorentzDirectionalCoefficient] using coefficientZero
    exact
      (lorentzThreeFormWedgeContinuousDual_eq_zero_iff
        (residual point)).mp dualZero
  · rintro rfl
    intro variation
    simp [lorentzOneFormThreeFormWedgeCoefficient]

end

end
  SaturationMonoid.PhysicsCore.StageNineTopologicalLorentzWeakEquation
