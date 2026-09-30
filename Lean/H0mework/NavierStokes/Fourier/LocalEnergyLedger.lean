import H0mework.NavierStokes.Fourier.LocalEnergyAlgebra

/-!
# Exact local-energy ledger for the filtered spatial generator

The pointwise product rules from
`ThreeDimensionalPeriodicLocalEnergyAlgebra` are assembled into one honest
spatial ledger.  The general theorem retains the exact compressibility
correction; its divergence-free corollary removes that correction from a
separately supplied law.

This module remains a fixed-time readout.  It does not generate a
time-dependent solution, commute the coarse filter with a time derivative,
integrate over a periodic cell, or assert a flux sign.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicLocalEnergyLedger

open ThreeDimensionalPeriodicCoarseCorrelationResidual
open ThreeDimensionalPeriodicCoarseNonlinearDivergence
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicLocalEnergyAlgebra

noncomputable section

private theorem velocityDot_add
    (u v w : LocalVelocityField) :
    velocityDot u (v + w) =
      velocityDot u v + velocityDot u w := by
  funext x
  simp only [velocityDot, Pi.add_apply, WithLp.ofLp_add]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

private theorem velocityDot_sub
    (u v w : LocalVelocityField) :
    velocityDot u (v - w) =
      velocityDot u v - velocityDot u w := by
  funext x
  simp only [velocityDot, Pi.sub_apply, WithLp.ofLp_sub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem velocityDot_const_smul
    (a : ℝ) (u v : LocalVelocityField) :
    velocityDot u (a • v) =
      a • velocityDot u v := by
  funext x
  simp only [velocityDot, Pi.smul_apply,
    WithLp.ofLp_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem velocityDivergence_add
    (v w : LocalVelocityField)
    (hv : Differentiable ℝ v)
    (hw : Differentiable ℝ w) :
    velocityDivergence (v + w) =
      velocityDivergence v + velocityDivergence w := by
  funext x
  simp only [velocityDivergence, Pi.add_apply]
  rw [fderiv_add (hv x) (hw x)]
  exact velocityDivergenceReadout.map_add _ _

private theorem velocityDivergence_sub
    (v w : LocalVelocityField)
    (hv : Differentiable ℝ v)
    (hw : Differentiable ℝ w) :
    velocityDivergence (v - w) =
      velocityDivergence v - velocityDivergence w := by
  funext x
  simp only [velocityDivergence, Pi.sub_apply]
  rw [fderiv_sub (hv x) (hw x)]
  exact velocityDivergenceReadout.map_sub _ _

private theorem velocityDivergence_const_smul
    (a : ℝ) (v : LocalVelocityField)
    (hv : Differentiable ℝ v) :
    velocityDivergence (a • v) =
      a • velocityDivergence v := by
  funext x
  simp only [velocityDivergence, Pi.smul_apply]
  rw [fderiv_const_smul (hv x) a]
  exact velocityDivergenceReadout.map_smul a _

/--
The complete local transport vector for the filtered equation.  The stress
and viscous terms use the same coordinate orientation already verified by
the product-rule module.
-/
noncomputable def localEnergyFlux
    (ν : Viscosity)
    (p : LocalScalarField) (T : StressField)
    (u : LocalVelocityField) : LocalVelocityField :=
  kineticEnergyFlux u +
    pressureEnergyFlux p u +
    stressEnergyFlux T u -
    ν.coeff • viscousEnergyFlux u

/-- Pointwise work done by the forcing. -/
def forcingWork
    (forcing u : LocalVelocityField) : LocalScalarField :=
  velocityDot u forcing

/-- Positive-coefficient local viscous dissipation density. -/
noncomputable def viscousDissipation
    (ν : Viscosity)
    (u : LocalVelocityField) : LocalScalarField :=
  fun x => ν.coeff * gradientDissipation u x

/-- The exact pressure/convection correction away from incompressibility. -/
noncomputable def compressibilityWork
    (p : LocalScalarField) (u : LocalVelocityField) :
    LocalScalarField :=
  fun x =>
    (p x - kineticEnergyDensity u x) *
      velocityDivergence u x

private theorem velocityDivergence_localEnergyFlux
    (ν : Viscosity)
    (p : LocalScalarField) (T : StressField)
    (u : LocalVelocityField)
    (hp : Differentiable ℝ p)
    (hT : Differentiable ℝ T)
    (hu : ContDiff ℝ 2 u) :
    velocityDivergence (localEnergyFlux ν p T u) =
      velocityDivergence (kineticEnergyFlux u) +
        velocityDivergence (pressureEnergyFlux p u) +
        velocityDivergence (stressEnergyFlux T u) -
        ν.coeff •
          velocityDivergence (viscousEnergyFlux u) := by
  have huDiff : Differentiable ℝ u :=
    hu.differentiable (by norm_num)
  have hKinetic :
      Differentiable ℝ (kineticEnergyFlux u) :=
    kineticEnergyFlux_differentiable u huDiff
  have hPressure :
      Differentiable ℝ (pressureEnergyFlux p u) :=
    hp.fun_smul huDiff
  have hStress :
      Differentiable ℝ (stressEnergyFlux T u) :=
    stressEnergyFlux_differentiable T u hT huDiff
  have hViscous :
      Differentiable ℝ (viscousEnergyFlux u) :=
    stressEnergyFlux_differentiable
      (velocityGradient u) u
      (velocityGradient_differentiable u hu)
      huDiff
  rw [localEnergyFlux,
    velocityDivergence_sub _ _
      ((hKinetic.add hPressure).add hStress)
      (hViscous.const_smul ν.coeff),
    velocityDivergence_add _ _
      (hKinetic.add hPressure) hStress,
    velocityDivergence_add _ _
      hKinetic hPressure,
    velocityDivergence_const_smul
      ν.coeff _ hViscous]

/--
Exact pointwise local-energy ledger for a smooth spatial state and an
additional stress divergence.

The theorem is intentionally more general than the incompressible form:
the pressure/convection correction remains visible as
`compressibilityWork`.  No time evolution or Navier--Stokes solution is a
premise or conclusion.
-/
theorem localEnergyLedger
    (ν : Viscosity)
    (forcing u : LocalVelocityField)
    (p : LocalScalarField) (T : StressField)
    (hp : ContDiff ℝ 1 p)
    (hT : ContDiff ℝ 1 T)
    (hu : ContDiff ℝ 2 u) :
    velocityDot u
        (navierStokesSpatialGenerator
            ν forcing p u -
          tensorDivergence T) =
      -velocityDivergence
          (localEnergyFlux ν p T u) +
        forcingWork forcing u -
        viscousDissipation ν u +
        stressGradientContraction T u +
        compressibilityWork p u := by
  have huDiff : Differentiable ℝ u :=
    hu.differentiable (by norm_num)
  have hpDiff : Differentiable ℝ p :=
    hp.differentiable (by norm_num)
  have hTDiff : Differentiable ℝ T :=
    hT.differentiable (by norm_num)
  rw [navierStokesSpatialGenerator]
  rw [velocityDot_sub, velocityDot_sub,
    velocityDot_sub,
    velocityDot_add, velocityDot_const_smul]
  rw [velocityDot_vectorLaplacian u hu]
  rw [velocityDot_tensorDivergence_velocityTensor
    u (hu.of_le (by norm_num))]
  rw [velocityDot_scalarGradient p u hpDiff huDiff]
  rw [velocityDot_tensorDivergence T u hTDiff huDiff]
  rw [velocityDivergence_localEnergyFlux
    ν p T u hpDiff hTDiff hu]
  funext x
  simp only [forcingWork, viscousDissipation,
    compressibilityWork, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/--
Incompressibility removes the correction from the actual general ledger;
it is not stored in the flux or in a certificate.
-/
theorem localEnergyLedger_of_divergence_free
    (ν : Viscosity)
    (forcing u : LocalVelocityField)
    (p : LocalScalarField) (T : StressField)
    (hp : ContDiff ℝ 1 p)
    (hT : ContDiff ℝ 1 T)
    (hu : ContDiff ℝ 2 u)
    (hdiv : velocityDivergence u = 0) :
    velocityDot u
        (navierStokesSpatialGenerator
            ν forcing p u -
          tensorDivergence T) =
      -velocityDivergence
          (localEnergyFlux ν p T u) +
        forcingWork forcing u -
        viscousDissipation ν u +
        stressGradientContraction T u := by
  have hCompressibility :
      compressibilityWork p u = 0 := by
    funext x
    change
      (p x - kineticEnergyDensity u x) *
          velocityDivergence u x =
        0
    rw [hdiv]
    simp
  rw [localEnergyLedger ν forcing u p T hp hT hu]
  rw [hCompressibility]
  simp

end

end ThreeDimensionalPeriodicLocalEnergyLedger
end NavierStokes
end SaturationMonoid
