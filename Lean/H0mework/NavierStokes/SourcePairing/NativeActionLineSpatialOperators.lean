import H0mework.Physics.Fluid.LineDifferential
import H0mework.NavierStokes.SourceAction.SpatialOperators
import H0mework.NavierStokes.PhysicalJets.CurlCross

set_option autoImplicit false
open scoped BigOperators ContDiff

namespace SaturationMonoid.NavierStokes.NativeLineSpatialOperators

open PhysicsCore ProofFreeRicherAnholonomicSource Stage9CU StageNineCanonicalCauchyState
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFullVorticityStretching
open NativeFluidSpatialOperators (spatialDerivative spatialLaplacian)

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def slice (field : BasePoint → E) (time : ℝ) (space : PhysicalSpace) : E :=
  field (canonicalCauchySlicePoint time space)

theorem derivative_slice (field : BasePoint → E) (time : ℝ)
    (smooth : ContDiff ℝ ∞ (slice field time)) (direction : Fin 3) :
    slice (Fluid.coordinateLineDerivative field direction.succ) time =
      spatialDerivative (slice field time) direction := by
  funext space
  exact Fluid.coordinateLineDerivative_spatial_of_differentiableAt
    ((smooth.differentiable (by simp)) space) direction

theorem lineCurl_slice (field : BasePoint → PhysicalSpace) (time : ℝ)
    (smooth : ContDiff ℝ ∞ (slice field time)) (space : PhysicalSpace) :
    Fluid.lineCurl field (canonicalCauchySlicePoint time space) =
      vorticityField (slice field time) space := by
  have each (direction : Fin 3) := congrFun (derivative_slice field time smooth direction) space
  simp only [slice] at each
  simpa [Fluid.lineCurl, spatialDerivative] using
    congrArg (fun rows : Fin 3 → PhysicalSpace => WithLp.toLp 2
      ![rows 1 2 - rows 2 1, rows 2 0 - rows 0 2, rows 0 1 - rows 1 0]) (funext each)

private theorem spatialDerivative_contDiff {field : PhysicalSpace → E}
    (smooth : ContDiff ℝ ∞ field) (direction : Fin 3) :
    ContDiff ℝ ∞ (spatialDerivative field direction) :=
  (smooth.fderiv_right (by simp)).clm_apply contDiff_const

theorem lineLaplacian_slice (field : BasePoint → E) (time : ℝ)
    (smooth : ContDiff ℝ ∞ (slice field time)) (space : PhysicalSpace) :
    Fluid.lineLaplacian field (canonicalCauchySlicePoint time space) =
      spatialLaplacian (slice field time) space := by
  unfold Fluid.lineLaplacian spatialLaplacian
  apply Finset.sum_congr rfl
  intro direction _
  have first := derivative_slice field time smooth direction
  have derivativeSmooth : ContDiff ℝ ∞
      (slice (Fluid.coordinateLineDerivative field direction.succ) time) := by
    rw [first]
    exact spatialDerivative_contDiff smooth direction
  have second := congrFun (derivative_slice
    (Fluid.coordinateLineDerivative field direction.succ) time derivativeSmooth direction) space
  rw [first] at second
  exact second

theorem cross_slice (left right : BasePoint → PhysicalSpace) (time : ℝ) :
    slice (Fluid.cross left right) time = NativeFluidCurlCross.cross (slice left time) (slice right time) := rfl

theorem lineCurl_cross_slice (left right : BasePoint → PhysicalSpace) (time : ℝ)
    (leftSmooth : ContDiff ℝ ∞ (slice left time)) (rightSmooth : ContDiff ℝ ∞ (slice right time))
    (space : PhysicalSpace) :
    Fluid.lineCurl (Fluid.cross left right) (canonicalCauchySlicePoint time space) =
      vorticityField (NativeFluidCurlCross.cross (slice left time) (slice right time)) space := by
  have smooth : ContDiff ℝ ∞ (slice (Fluid.cross left right) time) := by
    rw [cross_slice]
    exact NativeFluidCurlCross.cross_contDiff _ _ leftSmooth rightSmooth
  simpa only [cross_slice] using lineCurl_slice (Fluid.cross left right) time smooth space

end
end SaturationMonoid.NavierStokes.NativeLineSpatialOperators
