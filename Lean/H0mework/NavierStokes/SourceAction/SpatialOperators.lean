import H0mework.Physics.Fluid.Differential
import H0mework.NavierStokes.Fourier.FullVorticityStretching

set_option autoImplicit false
open scoped BigOperators ContDiff

namespace SaturationMonoid.NavierStokes.NativeFluidSpatialOperators

open PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9CU
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFullVorticityStretching

noncomputable section

def spatialEmbedding : PhysicalSpace →L[ℝ] BasePoint :=
  ({ toFun := fun space => WithLp.toLp 2 (Fin.cases 0 (fun direction => space direction))
     map_add' := by
       intro first second
       apply PiLp.ext
       intro direction
       refine Fin.cases ?_ (fun _ => rfl) direction
       simp
     map_smul' := by
       intro scalar space
       apply PiLp.ext
       intro direction
       refine Fin.cases ?_ (fun _ => rfl) direction
       simp } : PhysicalSpace →ₗ[ℝ] BasePoint).toContinuousLinearMap

theorem spatialEmbedding_single (direction : Fin 3) :
    spatialEmbedding (EuclideanSpace.single direction 1) = coordinateDirection direction.succ := by
  apply PiLp.ext
  intro output
  refine Fin.cases ?_ (fun coordinate => ?_) output
  · simp [spatialEmbedding, coordinateDirection]
  · simp [spatialEmbedding, coordinateDirection]

def slice (time : ℝ) (space : PhysicalSpace) : BasePoint :=
  EuclideanSpace.single (0 : Fin 4) time + spatialEmbedding space

theorem slice_hasFDerivAt (time : ℝ) (space : PhysicalSpace) :
    HasFDerivAt (slice time) spatialEmbedding space :=
  spatialEmbedding.hasFDerivAt.const_add _

theorem slice_contDiff (time : ℝ) : ContDiff ℝ ∞ (slice time) :=
  contDiff_const.add spatialEmbedding.contDiff

theorem slice_time (time : ℝ) (space : PhysicalSpace) : slice time space 0 = time := by
  simp [slice, spatialEmbedding]

theorem slice_spatial (time : ℝ) (space : PhysicalSpace) (direction : Fin 3) :
    slice time space direction.succ = space direction := by
  simp [slice, spatialEmbedding]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def restrict (field : BasePoint → E) (time : ℝ) : PhysicalSpace → E := field ∘ slice time

def spatialDerivative (field : PhysicalSpace → E) (direction : Fin 3) (space : PhysicalSpace) : E :=
  fderiv ℝ field space (EuclideanSpace.single direction 1)

theorem derivative_restrict (field : BasePoint → E) (time : ℝ) (space : PhysicalSpace)
    (differentiable : DifferentiableAt ℝ field (slice time space)) (direction : Fin 3) :
    spatialDerivative (restrict field time) direction space =
      Fluid.coordinateDerivative field direction.succ (slice time space) := by
  unfold spatialDerivative restrict Fluid.coordinateDerivative
  rw [fderiv_comp space differentiable (slice_hasFDerivAt time space).differentiableAt,
    (slice_hasFDerivAt time space).fderiv, ContinuousLinearMap.comp_apply, spatialEmbedding_single]

theorem derivative_restrict_field (field : BasePoint → E) (smooth : ContDiff ℝ ∞ field)
    (time : ℝ) (direction : Fin 3) :
    spatialDerivative (restrict field time) direction = restrict (Fluid.coordinateDerivative field direction.succ) time := by
  funext space
  exact derivative_restrict field time space (smooth.differentiable (by simp) _) direction

theorem curl_restrict (field : BasePoint → PhysicalSpace) (smooth : ContDiff ℝ ∞ field)
    (time : ℝ) :
    vorticityField (restrict field time) = restrict (Fluid.curl field) time := by
  funext space
  simp only [vorticityField_apply]
  change WithLp.toLp 2 ![
    spatialDerivative (restrict field time) 1 space 2 - spatialDerivative (restrict field time) 2 space 1,
    spatialDerivative (restrict field time) 2 space 0 - spatialDerivative (restrict field time) 0 space 2,
    spatialDerivative (restrict field time) 0 space 1 - spatialDerivative (restrict field time) 1 space 0] = _
  simp only [derivative_restrict field time space (smooth.differentiable (by simp) _)]
  rfl

def spatialLaplacian (field : PhysicalSpace → E) (space : PhysicalSpace) : E :=
  ∑ direction : Fin 3, spatialDerivative (spatialDerivative field direction) direction space

theorem laplacian_restrict (field : BasePoint → PhysicalSpace) (smooth : ContDiff ℝ ∞ field)
    (time : ℝ) :
    spatialLaplacian (restrict field time) = restrict (Fluid.laplacian field) time := by
  funext space
  change (∑ direction : Fin 3, spatialDerivative (spatialDerivative (restrict field time) direction) direction space) =
    ∑ direction : Fin 3, Fluid.coordinateDerivative (Fluid.coordinateDerivative field direction.succ) direction.succ (slice time space)
  apply Finset.sum_congr rfl
  intro direction _
  rw [derivative_restrict_field field smooth time direction]
  exact derivative_restrict _ time space
    ((Fluid.coordinateDerivative_contDiff smooth direction.succ).differentiable (by simp) _) direction

end
end SaturationMonoid.NavierStokes.NativeFluidSpatialOperators
