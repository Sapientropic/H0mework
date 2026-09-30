import H0mework.NavierStokes.Fourier.CoarseNonlinearDivergence
import H0mework.NavierStokes.Fourier.CoarseVectorCalculus

/-!
# The filtered three-dimensional Navier--Stokes spatial generator

For positive viscosity, forcing, pressure, and velocity, the native spatial
generator is

`ν Δu + f - div(u ⊗ u) - ∇p`.

The previously generated derivative, Laplacian, gradient, and nonlinear
commuting squares now give the exact filtered generator law

`K G(u,p,f) = G(Ku,Kp,Kf) - div τₖ(u)`.

This is an actual smooth spatial-update identity on the full function
carrier.  It is not yet a time-dependent solution, a local energy identity,
a flux sign, or a global regularity theorem.
-/

open scoped Laplacian
open MeasureTheory

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicFilteredNavierStokesGenerator

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseCorrelationResidual
open ThreeDimensionalPeriodicCoarseNonlinearDivergence
open ThreeDimensionalPeriodicCoarseVectorCalculus

noncomputable section

abbrev NSVelocityField := PhysicalSpace → PhysicalSpace

abbrev NSPressureField := PhysicalSpace → ℝ

/-- The viscosity is source data and is strictly positive. -/
structure Viscosity where
  coeff : ℝ
  coeff_pos : 0 < coeff

/-- The native spatial right-hand side of incompressible Navier--Stokes. -/
noncomputable def navierStokesSpatialGenerator
    (ν : Viscosity) (forcing : NSVelocityField)
    (pressure : NSPressureField) (u : NSVelocityField) :
    NSVelocityField :=
  ν.coeff • Δ u + forcing -
    tensorDivergence (velocityTensor u) -
    scalarGradient pressure

/--
The exact filtered spatial generator law.  Every integrability condition
used to distribute convolution is generated from the displayed continuity
and smoothness hypotheses.
-/
theorem filtered_navierStokesSpatialGenerator
    (s : CoarseScale) (ν : Viscosity)
    (forcing : NSVelocityField) (pressure : NSPressureField)
    (u : NSVelocityField)
    (hforcing : Continuous forcing)
    (hpressure : ContDiff ℝ 1 pressure)
    (hu : ContDiff ℝ 2 u) :
    coarseFilter s
        (navierStokesSpatialGenerator ν forcing pressure u) =
      navierStokesSpatialGenerator ν
          (coarseFilter s forcing)
          (coarseFilter s pressure)
          (coarseFilter s u) -
        tensorDivergence (subscaleStress s u) := by
  have hLap : LocallyIntegrable (Δ u) volume :=
    (vectorLaplacian_continuous u hu).locallyIntegrable
  have hVisc : LocallyIntegrable (ν.coeff • Δ u) volume :=
    hLap.smul ν.coeff
  have hForce : LocallyIntegrable forcing volume :=
    hforcing.locallyIntegrable
  have hNonlinear :
      LocallyIntegrable
        (tensorDivergence (velocityTensor u)) volume :=
    (tensorDivergence_continuous (velocityTensor u)
      (velocityTensor_contDiff u
        (hu.of_le (by norm_num)))).locallyIntegrable
  have hPressure :
      LocallyIntegrable (scalarGradient pressure) volume :=
    (scalarGradient_continuous pressure hpressure).locallyIntegrable
  rw [navierStokesSpatialGenerator,
    coarseFilter_sub s
      (ν.coeff • Δ u + forcing -
        tensorDivergence (velocityTensor u))
      (scalarGradient pressure)
      ((hVisc.add hForce).sub hNonlinear) hPressure,
    coarseFilter_sub s (ν.coeff • Δ u + forcing)
      (tensorDivergence (velocityTensor u))
      (hVisc.add hForce) hNonlinear,
    coarseFilter_add s (ν.coeff • Δ u) forcing hVisc hForce,
    coarseFilter_smul,
    ← vectorLaplacian_coarseFilter s u hu,
    coarseFilter_tensorDivergence_eq_resolved_add_subscale s u
      (hu.of_le (by norm_num)),
    ← scalarGradient_coarseFilter s pressure hpressure]
  simp only [navierStokesSpatialGenerator,
    resolvedVelocityTensor, filteredVelocity]
  abel

end

end ThreeDimensionalPeriodicFilteredNavierStokesGenerator
end NavierStokes
end SaturationMonoid
