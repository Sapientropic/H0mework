import Mathlib.Analysis.InnerProductSpace.Laplacian
import H0mework.NavierStokes.Fourier.CoarseFilterSpatialCommutation

/-!
# Vector calculus commuting with the concrete coarse filter

The whole-carrier Fréchet-derivative square is contracted through concrete
physical coordinate readouts.  This produces velocity divergence, scalar
gradient, and the vector Laplacian on the three-dimensional value space.

`Fin 3` appears only in these physical readouts.  The fields remain full
functions on `EuclideanSpace ℝ (Fin 3)`.
-/

open scoped Laplacian
open MeasureTheory

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicCoarseVectorCalculus

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseFilterSpatialCommutation

noncomputable section

abbrev Velocity := PhysicalSpace

abbrev VelocityField := PhysicalSpace → Velocity

abbrev ScalarField := PhysicalSpace → ℝ

/-! ## Divergence -/

noncomputable def velocityDivergenceReadoutLinear :
    (PhysicalSpace →L[ℝ] Velocity) →ₗ[ℝ] ℝ where
  toFun D :=
    ∑ i : Coordinate, D (EuclideanSpace.single i 1) i
  map_add' D E := by
    simp only [add_apply, WithLp.ofLp_add, Pi.add_apply,
      Finset.sum_add_distrib]
  map_smul' r D := by
    simp only [smul_apply, WithLp.ofLp_smul, Pi.smul_apply,
      Finset.smul_sum, RingHom.id_apply]

noncomputable def velocityDivergenceReadout :
    (PhysicalSpace →L[ℝ] Velocity) →L[ℝ] ℝ :=
  velocityDivergenceReadoutLinear.toContinuousLinearMap

noncomputable def velocityDivergence
    (u : VelocityField) : ScalarField :=
  fun x => velocityDivergenceReadout (fderiv ℝ u x)

theorem velocityDivergence_continuous
    (u : VelocityField) (hu : ContDiff ℝ 1 u) :
    Continuous (velocityDivergence u) :=
  velocityDivergenceReadout.continuous.comp
    (hu.continuous_fderiv one_ne_zero)

theorem velocityDivergence_coarseFilter
    (s : CoarseScale) (u : VelocityField)
    (hu : ContDiff ℝ 1 u) :
    velocityDivergence (coarseFilter s u) =
      coarseFilter s (velocityDivergence u) := by
  funext x
  rw [velocityDivergence,
    fderiv_coarseFilter_eq_coarseFilter_fderiv s u hu]
  change velocityDivergenceReadout
      (coarseFilter s (fderiv ℝ u) x) =
    coarseFilter s
      (fun y => velocityDivergenceReadout (fderiv ℝ u y)) x
  exact (coarseFilter_comp_continuousLinearMap
    s velocityDivergenceReadout (fderiv ℝ u)
    (hu.continuous_fderiv one_ne_zero).locallyIntegrable x).symm

/--
Incompressibility of the output is derived from the actual input
divergence law and the commuting square; it is not an output certificate.
-/
theorem velocityDivergence_coarseFilter_eq_zero
    (s : CoarseScale) (u : VelocityField)
    (hu : ContDiff ℝ 1 u)
    (hdiv : velocityDivergence u = 0) :
    velocityDivergence (coarseFilter s u) = 0 := by
  rw [velocityDivergence_coarseFilter s u hu, hdiv]
  simp [coarseFilter]

/-! ## Gradient -/

noncomputable def scalarGradientReadoutLinear :
    (PhysicalSpace →L[ℝ] ℝ) →ₗ[ℝ] Velocity where
  toFun D :=
    WithLp.toLp 2 (fun i => D (EuclideanSpace.single i 1))
  map_add' D E := by
    ext i
    change (D + E) (EuclideanSpace.single i 1) =
      D (EuclideanSpace.single i 1) +
        E (EuclideanSpace.single i 1)
    simp only [add_apply]
  map_smul' r D := by
    ext i
    change (r • D) (EuclideanSpace.single i 1) =
      r • D (EuclideanSpace.single i 1)
    simp only [smul_apply]

noncomputable def scalarGradientReadout :
    (PhysicalSpace →L[ℝ] ℝ) →L[ℝ] Velocity :=
  scalarGradientReadoutLinear.toContinuousLinearMap

noncomputable def scalarGradient
    (p : ScalarField) : VelocityField :=
  fun x => scalarGradientReadout (fderiv ℝ p x)

theorem scalarGradient_continuous
    (p : ScalarField) (hp : ContDiff ℝ 1 p) :
    Continuous (scalarGradient p) :=
  scalarGradientReadout.continuous.comp
    (hp.continuous_fderiv one_ne_zero)

theorem scalarGradient_coarseFilter
    (s : CoarseScale) (p : ScalarField)
    (hp : ContDiff ℝ 1 p) :
    scalarGradient (coarseFilter s p) =
      coarseFilter s (scalarGradient p) := by
  funext x
  rw [scalarGradient,
    fderiv_coarseFilter_eq_coarseFilter_fderiv s p hp]
  change scalarGradientReadout
      (coarseFilter s (fderiv ℝ p) x) =
    coarseFilter s
      (fun y => scalarGradientReadout (fderiv ℝ p y)) x
  exact (coarseFilter_comp_continuousLinearMap
    s scalarGradientReadout (fderiv ℝ p)
    (hp.continuous_fderiv one_ne_zero).locallyIntegrable x).symm

/-! ## Laplacian -/

abbrev SecondVelocityDerivative :=
  PhysicalSpace →L[ℝ] (PhysicalSpace →L[ℝ] Velocity)

noncomputable def vectorLaplacianReadoutLinear :
    SecondVelocityDerivative →ₗ[ℝ] Velocity where
  toFun D :=
    WithLp.toLp 2 (fun i =>
      ∑ j : Coordinate,
        D (EuclideanSpace.single j 1)
          (EuclideanSpace.single j 1) i)
  map_add' D E := by
    ext i
    change (∑ j : Coordinate,
      (D + E) (EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1) i) =
      (∑ j : Coordinate,
        D (EuclideanSpace.single j 1)
          (EuclideanSpace.single j 1) i) +
      ∑ j : Coordinate,
        E (EuclideanSpace.single j 1)
          (EuclideanSpace.single j 1) i
    simp only [add_apply, WithLp.ofLp_add, Pi.add_apply,
      Finset.sum_add_distrib]
  map_smul' r D := by
    ext i
    change (∑ j : Coordinate,
      (r • D) (EuclideanSpace.single j 1)
        (EuclideanSpace.single j 1) i) =
      r • ∑ j : Coordinate,
        D (EuclideanSpace.single j 1)
          (EuclideanSpace.single j 1) i
    simp only [smul_apply, WithLp.ofLp_smul, Pi.smul_apply,
      Finset.smul_sum]

noncomputable def vectorLaplacianReadout :
    SecondVelocityDerivative →L[ℝ] Velocity :=
  (LinearMap.toContinuousLinearMap
    (𝕜 := ℝ) (E := SecondVelocityDerivative) (F' := Velocity))
      vectorLaplacianReadoutLinear

/-- Coordinate formula for the physical vector Laplacian. -/
noncomputable def coordinateVectorLaplacian
    (u : VelocityField) : VelocityField :=
  fun x =>
    vectorLaplacianReadout (fderiv ℝ (fderiv ℝ u) x)

theorem coordinateVectorLaplacian_continuous
    (u : VelocityField) (hu : ContDiff ℝ 2 u) :
    Continuous (coordinateVectorLaplacian u) :=
  vectorLaplacianReadout.continuous.comp
    ((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      one_ne_zero)

theorem secondFDeriv_coarseFilter_eq
    (s : CoarseScale) (u : VelocityField)
    (hu : ContDiff ℝ 2 u) :
    fderiv ℝ (fderiv ℝ (coarseFilter s u)) =
      coarseFilter s (fderiv ℝ (fderiv ℝ u)) := by
  rw [fderiv_coarseFilter_eq_coarseFilter_fderiv s u
    (hu.of_le (by norm_num))]
  exact fderiv_coarseFilter_eq_coarseFilter_fderiv
    s (fderiv ℝ u)
    (hu.fderiv_right (m := 1) (by norm_num))

theorem coordinateVectorLaplacian_coarseFilter
    (s : CoarseScale) (u : VelocityField)
    (hu : ContDiff ℝ 2 u) :
    coordinateVectorLaplacian (coarseFilter s u) =
      coarseFilter s (coordinateVectorLaplacian u) := by
  funext x
  rw [coordinateVectorLaplacian,
    secondFDeriv_coarseFilter_eq s u hu]
  change vectorLaplacianReadout
      (coarseFilter s (fderiv ℝ (fderiv ℝ u)) x) =
    coarseFilter s
      (fun y => vectorLaplacianReadout
        (fderiv ℝ (fderiv ℝ u) y)) x
  exact (coarseFilter_comp_continuousLinearMap
    s vectorLaplacianReadout (fderiv ℝ (fderiv ℝ u))
    ((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      one_ne_zero).locallyIntegrable x).symm

/-- The coordinate construction agrees with Mathlib's canonical `Δ`. -/
theorem coordinateVectorLaplacian_eq_mathlib
    (u : VelocityField) :
    coordinateVectorLaplacian u = Δ u := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    u (EuclideanSpace.basisFun Coordinate ℝ)]
  funext x
  ext i
  simp only [coordinateVectorLaplacian, vectorLaplacianReadout,
    vectorLaplacianReadoutLinear, EuclideanSpace.basisFun_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  change (∑ j : Coordinate,
      (((fderiv ℝ (fderiv ℝ u) x) (EuclideanSpace.single j 1))
        (EuclideanSpace.single j 1)) i) =
    (EuclideanSpace.proj i) (∑ j : Coordinate,
      ((fderiv ℝ (fderiv ℝ u) x) (EuclideanSpace.single j 1))
        (EuclideanSpace.single j 1))
  rw [map_sum]
  rfl

theorem vectorLaplacian_continuous
    (u : VelocityField) (hu : ContDiff ℝ 2 u) :
    Continuous (Δ u) := by
  rw [← coordinateVectorLaplacian_eq_mathlib]
  exact coordinateVectorLaplacian_continuous u hu

/-- The concrete coarse filter commutes with the canonical vector Laplacian. -/
theorem vectorLaplacian_coarseFilter
    (s : CoarseScale) (u : VelocityField)
    (hu : ContDiff ℝ 2 u) :
    Δ (coarseFilter s u) = coarseFilter s (Δ u) := by
  rw [← coordinateVectorLaplacian_eq_mathlib,
    ← coordinateVectorLaplacian_eq_mathlib]
  exact coordinateVectorLaplacian_coarseFilter s u hu

end

end ThreeDimensionalPeriodicCoarseVectorCalculus
end NavierStokes
end SaturationMonoid
