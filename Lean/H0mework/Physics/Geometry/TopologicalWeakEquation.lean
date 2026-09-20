import H0mework.Physics.Geometry.TopologicalFourFormPairing
import H0mework.Physics.Geometry.FundamentalLemma

/-!
# Topological gravity weak equation

This module proves the faithful weak zero-fiber of the metric-free gravity
four-form pairing.  A continuous bivector residual vanishes exactly when its
pairing against every compactly supported smooth bivector variation has zero
integral.

The proof uses only the algebraic `W22` pairing, its faithful pointwise zero
fiber, and the scalar compact-bump fundamental lemma.  It consumes no
historical density, action derivative, stationarity theorem, coframe,
nondegeneracy assumption, source, or volume factor.

The two current imports transitively reach `StageNineGlobalIntegratedAction`
because the shared carrier/analysis infrastructure has not yet been split
from that historical module.  No declaration from the old density,
derivative, or stationarity layers is used below.  Extracting the topological
pairing core and compact-bump core into shallower modules is an import-time
performance and architecture debt, not a formulation-jurisdiction premise
of this theorem.
-/

namespace SaturationMonoid.PhysicsCore.StageNineTopologicalWeakEquation

open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNineTopologicalFourFormPairing
open MeasureTheory
open scoped ContDiff

noncomputable section

set_option autoImplicit false

/-- Weak vanishing of a continuous gravity-bivector residual against every
genuine compactly supported smooth variation.  Continuity is kept as a
separate theorem premise rather than stored as a field-equation receipt. -/
def TopologicalGravityWeakEquation
    (residual : BasePoint → PhysicalBivector) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    (∫ point : BasePoint,
      gravityTopologicalWedgeCoefficient
        (variation point) (residual point)) = 0

/-- Multiply a fixed physical-bivector direction by a genuine compact scalar
bump.  The direction is arbitrary data for testing the residual, not a
stored solution witness. -/
def scalarTimesTopologicalGravityVariation
    (direction : PhysicalBivector)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation PhysicalBivector where
  toFun := fun point => variation point • direction
  smooth := variation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

@[simp] theorem scalarTimesTopologicalGravityVariation_apply
    (direction : PhysicalBivector)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    scalarTimesTopologicalGravityVariation direction variation point =
      variation point • direction :=
  rfl

/-- Scalar coefficient seen by one fixed bivector direction. -/
def topologicalGravityDirectionalCoefficient
    (residual : BasePoint → PhysicalBivector)
    (direction : PhysicalBivector) : BasePoint → ℝ :=
  fun point =>
    gravityTopologicalWedgeCoefficient direction (residual point)

theorem topologicalGravityDirectionalCoefficient_continuous
    (residual : BasePoint → PhysicalBivector)
    (residualContinuous : Continuous residual)
    (direction : PhysicalBivector) :
    Continuous
      (topologicalGravityDirectionalCoefficient residual direction) := by
  change Continuous fun point =>
    gravityTopologicalWedgeDual direction (residual point)
  exact (gravityTopologicalWedgeDual direction)
    |>.continuous_of_finiteDimensional.comp residualContinuous

theorem gravityTopologicalWedgeCoefficient_scalarTimes
    (residual : BasePoint → PhysicalBivector)
    (direction : PhysicalBivector)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    gravityTopologicalWedgeCoefficient
        (scalarTimesTopologicalGravityVariation direction variation point)
        (residual point) =
      variation point *
        topologicalGravityDirectionalCoefficient residual direction point := by
  change gravityTopologicalWedgeCoefficient
      (variation point • direction) (residual point) = _
  rw [gravityTopologicalWedgeCoefficient_smul_left]
  rfl

/-- The weak equation annihilates every continuous scalar directional
coefficient.  This is the sole analytic use of compact bump functions. -/
theorem topologicalGravityWeakEquation_directionalCoefficient_eq_zero
    (residual : BasePoint → PhysicalBivector)
    (residualContinuous : Continuous residual)
    (weakEquation : TopologicalGravityWeakEquation residual)
    (direction : PhysicalBivector) :
    topologicalGravityDirectionalCoefficient residual direction = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (topologicalGravityDirectionalCoefficient residual direction)
    (topologicalGravityDirectionalCoefficient_continuous
      residual residualContinuous direction)
  intro variation
  have weakDirection := weakEquation
    (scalarTimesTopologicalGravityVariation direction variation)
  have integrandEquality :
      (fun point : BasePoint =>
        gravityTopologicalWedgeCoefficient
          (scalarTimesTopologicalGravityVariation direction variation point)
          (residual point)) =
        fun point => variation point *
          topologicalGravityDirectionalCoefficient
            residual direction point := by
    funext point
    exact gravityTopologicalWedgeCoefficient_scalarTimes
      residual direction variation point
  rw [integrandEquality] at weakDirection
  exact weakDirection

/-- Dependency-light weak fundamental lemma for the gravity topological
pairing.  The Lorentz pairing need not be positive definite: scalar bumps
first isolate every directional coefficient, and the already-proved faithful
algebraic zero fiber then separates the residual pointwise. -/
theorem topologicalGravityWeakEquation_iff_residual_eq_zero
    (residual : BasePoint → PhysicalBivector)
    (residualContinuous : Continuous residual) :
    TopologicalGravityWeakEquation residual ↔ residual = 0 := by
  constructor
  · intro weakEquation
    funext point
    apply gravityTopologicalWedgeCoefficient_separates_left
    intro direction
    rw [gravityTopologicalWedgeCoefficient_symmetric]
    exact congrFun
      (topologicalGravityWeakEquation_directionalCoefficient_eq_zero
        residual residualContinuous weakEquation direction) point
  · rintro rfl
    intro variation
    simp

end


end SaturationMonoid.PhysicsCore.StageNineTopologicalWeakEquation
