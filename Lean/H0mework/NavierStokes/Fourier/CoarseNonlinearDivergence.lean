import H0mework.NavierStokes.Fourier.CoarseCorrelationResidual
import H0mework.NavierStokes.Fourier.CoarseFilterSpatialCommutation
import H0mework.NavierStokes.Fourier.CoarseVectorCalculus

/-!
# Spatial divergence of the generated coarse stress

This module applies the actual spatial derivative to the quadratic residual
split.  It obtains the exact divergence-level decomposition

`div filtered(u ⊗ u) = div(filtered u ⊗ filtered u) + div τ`.

This is the local nonlinear readout needed before an energy ledger can be
formed.  It still does not identify the left side with
`filter (div (u ⊗ u))`; that convolution/integration-by-parts theorem is the
remaining derivative-commutation gate for the full filtered
Navier--Stokes generator.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicCoarseNonlinearDivergence

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseFilterSpatialCommutation
open ThreeDimensionalPeriodicCoarseCorrelationResidual

noncomputable section

/-- Coordinate divergence of a physical `3 × 3` tensor field. -/
noncomputable def tensorDivergence (T : StressField) : VelocityField :=
  fun x =>
    WithLp.toLp 2 (fun i =>
      ∑ j : Coordinate,
        fderiv ℝ T x (EuclideanSpace.single j 1) i j)

/--
The coordinate divergence readout as a linear map on a single Fréchet
derivative.  Its domain and codomain are finite-dimensional physical value
spaces; no finite truncation is imposed on the spatial field carrier.
-/
noncomputable def tensorDivergenceReadoutLinear :
    (PhysicalSpace →L[ℝ] Stress) →ₗ[ℝ] Velocity where
  toFun D :=
    WithLp.toLp 2 (fun i =>
      ∑ j : Coordinate, D (EuclideanSpace.single j 1) i j)
  map_add' D E := by
    ext i
    change (∑ j : Coordinate,
      (D + E) (EuclideanSpace.single j 1) i j) =
      (∑ j : Coordinate, D (EuclideanSpace.single j 1) i j) +
      ∑ j : Coordinate, E (EuclideanSpace.single j 1) i j
    simp only [add_apply, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r D := by
    ext i
    change (∑ j : Coordinate,
      (r • D) (EuclideanSpace.single j 1) i j) =
      r • ∑ j : Coordinate, D (EuclideanSpace.single j 1) i j
    simp only [smul_apply, Pi.smul_apply, Finset.smul_sum]

noncomputable def tensorDivergenceReadout :
    (PhysicalSpace →L[ℝ] Stress) →L[ℝ] Velocity :=
  tensorDivergenceReadoutLinear.toContinuousLinearMap

theorem tensorDivergence_eq_readout (T : StressField) :
    tensorDivergence T =
      fun x => tensorDivergenceReadout (fderiv ℝ T x) :=
  rfl

theorem tensorDivergence_continuous
    (T : StressField) (hT : ContDiff ℝ 1 T) :
    Continuous (tensorDivergence T) :=
  tensorDivergenceReadout.continuous.comp
    (hT.continuous_fderiv one_ne_zero)

private noncomputable def stressCoordinateReadout
    (i j : Coordinate) : Stress →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j) ∘L
    (ContinuousLinearMap.proj i)

private lemma fderiv_velocity_coordinate_apply
    (u : VelocityField)
    (hu : Differentiable ℝ u)
    (x : PhysicalSpace) (i j : Coordinate) :
    fderiv ℝ (fun y => u y i) x
        (EuclideanSpace.single j 1) =
      fderiv ℝ u x (EuclideanSpace.single j 1) i := by
  change
    fderiv ℝ ((EuclideanSpace.proj i) ∘ u) x
        (EuclideanSpace.single j 1) = _
  rw [fderiv_comp x
    (EuclideanSpace.proj i).differentiableAt
    (hu x)]
  rw [ContinuousLinearMap.fderiv]
  rfl

private lemma fderiv_stress_coordinate_apply
    (T : StressField)
    (hT : Differentiable ℝ T)
    (x : PhysicalSpace) (i j k : Coordinate) :
    fderiv ℝ (fun y => T y i j) x
        (EuclideanSpace.single k 1) =
      fderiv ℝ T x (EuclideanSpace.single k 1) i j := by
  change
    fderiv ℝ ((stressCoordinateReadout i j) ∘ T) x
        (EuclideanSpace.single k 1) = _
  rw [fderiv_comp x
    (stressCoordinateReadout i j).differentiableAt
    (hT x)]
  rw [ContinuousLinearMap.fderiv]
  rfl

private lemma fderiv_scalar_mul_apply
    (a b : PhysicalSpace → ℝ)
    (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b)
    (x : PhysicalSpace) (j : Coordinate) :
    fderiv ℝ (fun y => a y * b y) x
        (EuclideanSpace.single j 1) =
      a x *
          fderiv ℝ b x (EuclideanSpace.single j 1) +
        b x *
          fderiv ℝ a x (EuclideanSpace.single j 1) := by
  change
    fderiv ℝ (a * b) x
        (EuclideanSpace.single j 1) = _
  rw [fderiv_mul (ha x) (hb x)]
  simp only [smul_apply, smul_eq_mul, add_apply]

/--
Vector product rule for the divergence of the actual quadratic velocity
tensor:

```text
div (u ⊗ u) = Du · u + (div u) u.
```

This is a whole-carrier derivative readout.  It generates neither a
divergence-free witness nor a Navier--Stokes solution.
-/
theorem tensorDivergence_velocityTensor_product_rule
    (u : VelocityField)
    (hu : ContDiff ℝ 1 u) :
    tensorDivergence (velocityTensor u) =
      fun x =>
        fderiv ℝ u x (u x) +
          (ThreeDimensionalPeriodicCoarseVectorCalculus.velocityDivergence
            u x) • u x := by
  have huDiff : Differentiable ℝ u :=
    hu.differentiable (by norm_num)
  have hTensorDiff :
      Differentiable ℝ (velocityTensor u) :=
    (velocityTensor_contDiff u hu).differentiable
      (by norm_num)
  funext x
  ext i
  change
    (∑ j : Coordinate,
      fderiv ℝ (velocityTensor u) x
        (EuclideanSpace.single j 1) i j) =
      fderiv ℝ u x (u x) i +
        (∑ j : Coordinate,
          fderiv ℝ u x
            (EuclideanSpace.single j 1) j) *
          u x i
  simp_rw [← fderiv_stress_coordinate_apply
    (velocityTensor u) hTensorDiff x]
  change
    (∑ j : Coordinate,
      fderiv ℝ
          (fun y => u y i * u y j)
          x (EuclideanSpace.single j 1)) = _
  have hDerivative :
      (∑ j : Coordinate,
        fderiv ℝ
            (fun y => u y i * u y j)
            x (EuclideanSpace.single j 1)) =
        ∑ j : Coordinate,
          (u x i *
              fderiv ℝ u x
                (EuclideanSpace.single j 1) j +
            u x j *
              fderiv ℝ u x
                (EuclideanSpace.single j 1) i) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_scalar_mul_apply
      (fun y => u y i) (fun y => u y j)
      ((differentiable_piLp 2).mp huDiff i)
      ((differentiable_piLp 2).mp huDiff j) x j]
    rw [fderiv_velocity_coordinate_apply u huDiff x j j,
      fderiv_velocity_coordinate_apply u huDiff x i j]
  have hDirectional :
      fderiv ℝ u x (u x) i =
        ∑ j : Coordinate,
          u x j *
            fderiv ℝ u x
              (EuclideanSpace.single j 1) i := by
    rw [←
      (EuclideanSpace.basisFun Coordinate ℝ).sum_repr
        (u x), map_sum]
    simp only [map_smul,
      EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply,
      WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, PiLp.single_apply,
      mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq]
  rw [hDerivative, Finset.sum_add_distrib,
    hDirectional]
  rw [← Finset.mul_sum]
  ring

/--
For a divergence-free field the quadratic tensor divergence is exactly the
directional derivative.  The divergence law remains an explicit consumer
premise and must be generated by each concrete source.
-/
theorem tensorDivergence_velocityTensor_of_divergence_eq_zero
    (u : VelocityField)
    (hu : ContDiff ℝ 1 u)
    (hdiv :
      ThreeDimensionalPeriodicCoarseVectorCalculus.velocityDivergence
        u = 0) :
    tensorDivergence (velocityTensor u) =
      fun x => fderiv ℝ u x (u x) := by
  rw [tensorDivergence_velocityTensor_product_rule u hu,
    hdiv]
  simp

/--
The divergence readout respects addition when both actual tensor fields are
differentiable.  This domain condition is generated below from the concrete
coarse filter; it is not stored in the residual object.
-/
theorem tensorDivergence_add (T S : StressField)
    (hT : Differentiable ℝ T) (hS : Differentiable ℝ S) :
    tensorDivergence (T + S) =
      tensorDivergence T + tensorDivergence S := by
  funext x
  ext i
  change (∑ j : Coordinate,
      fderiv ℝ (T + S) x (EuclideanSpace.single j 1) i j) =
    (∑ j : Coordinate,
      fderiv ℝ T x (EuclideanSpace.single j 1) i j) +
    ∑ j : Coordinate,
      fderiv ℝ S x (EuclideanSpace.single j 1) i j
  rw [fderiv_add (hT x) (hS x)]
  simp only [add_apply, Pi.add_apply, Finset.sum_add_distrib]

/--
The filtered quadratic update, resolved keep, and generated stress commute
with the concrete divergence readout on the whole spatial carrier.
-/
theorem tensorDivergence_filtered_eq_resolved_add_subscale
    (s : CoarseScale) (u : VelocityField)
    (hu : LocallyIntegrable u volume)
    (huu : LocallyIntegrable (velocityTensor u) volume) :
    tensorDivergence (filteredVelocityTensor s u) =
      tensorDivergence (resolvedVelocityTensor s u) +
        tensorDivergence (subscaleStress s u) := by
  rw [filteredVelocityTensor_eq_resolved_add_subscaleStress]
  exact tensorDivergence_add _ _
    ((resolvedVelocityTensor_contDiff s u hu).differentiable
      (by simp))
    ((subscaleStress_contDiff s u hu huu).differentiable
      (by simp))

/--
The missing spatial gate is now generated on the actual carrier:
filtering a tensor divergence equals taking the divergence after filtering.
-/
theorem tensorDivergence_coarseFilter_eq_coarseFilter
    (s : CoarseScale) (T : StressField)
    (hT : ContDiff ℝ 1 T) :
    tensorDivergence (coarseFilter s T) =
      coarseFilter s (tensorDivergence T) := by
  funext x
  rw [tensorDivergence_eq_readout,
    fderiv_coarseFilter_eq_coarseFilter_fderiv s T hT]
  change tensorDivergenceReadout
      (coarseFilter s (fderiv ℝ T) x) =
    coarseFilter s
      (fun y => tensorDivergenceReadout (fderiv ℝ T y)) x
  exact (coarseFilter_comp_continuousLinearMap
    s tensorDivergenceReadout (fderiv ℝ T)
    (hT.continuous_fderiv one_ne_zero).locallyIntegrable x).symm

/--
Consequently the actual filtered quadratic generator is the resolved
quadratic generator plus the divergence of the generated subscale trace.
-/
theorem coarseFilter_tensorDivergence_eq_resolved_add_subscale
    (s : CoarseScale) (u : VelocityField)
    (hu : ContDiff ℝ 1 u) :
    coarseFilter s (tensorDivergence (velocityTensor u)) =
      tensorDivergence (resolvedVelocityTensor s u) +
        tensorDivergence (subscaleStress s u) := by
  rw [← tensorDivergence_coarseFilter_eq_coarseFilter s
    (velocityTensor u) (velocityTensor_contDiff u hu)]
  exact tensorDivergence_filtered_eq_resolved_add_subscale s u
    hu.continuous.locallyIntegrable
    (velocityTensor_contDiff u hu).continuous.locallyIntegrable

theorem tensorDivergence_subscaleStress_const
    (s : CoarseScale) (c : Velocity) :
    tensorDivergence (subscaleStress s (fun _ => c)) = 0 := by
  rw [subscaleStress_const]
  funext x
  ext i
  simp [tensorDivergence]

end

end ThreeDimensionalPeriodicCoarseNonlinearDivergence
end NavierStokes
end SaturationMonoid
