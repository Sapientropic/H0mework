import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.GaugeAction.P286ActionVelocityLocalActualLift

/-!
# Stage-9 canonical Cauchy coordinate projections

This dependency-light module records the fixed inverse coordinate maps for
the canonical `3+1` split.  They are kinematic chart data: no action equation,
residual, source receipt, endpoint, or Stage-9 exact actual enters their
definition.

The declarations retain their historical namespace so existing exact
consumers keep the same fully qualified names while newer action-first modules
can import the projections without importing the C3h196 actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift

noncomputable section

set_option autoImplicit false

/-- Projection onto the fixed canonical time coordinate. -/
def canonicalTimeProjection : BasePoint →L[ℝ] ℝ :=
  localBaseCoordinate canonicalLorentzianTimeDirection

/-- Projection onto the three fixed canonical spatial coordinates. -/
def canonicalSpatialProjection : BasePoint →L[ℝ] StageNineSpatialPoint :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      ![localBaseCoordinate 1, localBaseCoordinate 2,
        localBaseCoordinate 3])

theorem canonicalCauchySlicePoint_projections (point : BasePoint) :
    canonicalCauchySlicePoint (canonicalTimeProjection point)
        (canonicalSpatialProjection point) =
      point := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalTimeProjection, canonicalSpatialProjection,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      localBaseCoordinate_apply, Fin.sum_univ_three]

@[simp] theorem canonicalTimeProjection_slice
    (time : ℝ) (space : StageNineSpatialPoint) :
    canonicalTimeProjection (canonicalCauchySlicePoint time space) = time := by
  simp [canonicalTimeProjection, localBaseCoordinate_apply]

@[simp] theorem canonicalSpatialProjection_slice
    (time : ℝ) (space : StageNineSpatialPoint) :
    canonicalSpatialProjection (canonicalCauchySlicePoint time space) = space := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpatialProjection, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, localBaseCoordinate_apply,
      Fin.sum_univ_three]

end

end SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
