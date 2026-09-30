import H0mework.NavierStokes.Fourier.LocalEnergyLedger
import H0mework.NavierStokes.Fourier.UnitCellDivergence

/-!
# Periodic transport of the local-energy flux

The algebraic local-energy flux contains a viscous term built from
`fderiv u`.  Periodicity of values alone therefore is not enough to invoke
the unit-cell divergence theorem: the derivative must be transported
through lattice translation on the same lifted carrier.

This module proves that translation law from the actual function equality,
then propagates it through the kinetic, pressure, stress, and viscous flux
formations.  The resulting cell-integrated divergence cancellation is an
analytic transporter/readout.  It does not generate a Navier--Stokes
trajectory or an energy update.
-/

open MeasureTheory

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicLocalEnergyFluxTransport

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseCorrelationResidual
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicLocalEnergyLedger
open ThreeDimensionalPeriodicUnitCellDivergence

noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
The Fréchet derivative of a lattice-periodic function is periodic on the
same lattice.  The proof differentiates the literal translated-function
equality; no periodic derivative certificate is supplied.
-/
theorem fderiv_latticePeriodic
    (f : PhysicalSpace → E)
    (hperiodic : LatticePeriodic f) :
    LatticePeriodic (fderiv ℝ f) := by
  intro z x
  have htranslated :
      (fun y => f (y + latticeShift z)) = f := by
    funext y
    exact hperiodic z y
  have hderivative :=
    congrArg
      (fun g : PhysicalSpace → E =>
        fderiv ℝ g x) htranslated
  rw [fderiv_comp_add_right] at hderivative
  exact hderivative

theorem kineticEnergyDensity_latticePeriodic
    (u : LocalVelocityField)
    (hu : LatticePeriodic u) :
    LatticePeriodic (kineticEnergyDensity u) := by
  intro z x
  unfold kineticEnergyDensity
  rw [hu z x]

theorem kineticEnergyFlux_latticePeriodic
    (u : LocalVelocityField)
    (hu : LatticePeriodic u) :
    LatticePeriodic (kineticEnergyFlux u) := by
  intro z x
  unfold kineticEnergyFlux
  rw [kineticEnergyDensity_latticePeriodic u hu z x,
    hu z x]

theorem pressureEnergyFlux_latticePeriodic
    (p : LocalScalarField) (u : LocalVelocityField)
    (hp : LatticePeriodic p)
    (hu : LatticePeriodic u) :
    LatticePeriodic (pressureEnergyFlux p u) := by
  intro z x
  unfold pressureEnergyFlux
  rw [hp z x, hu z x]

theorem stressEnergyFlux_latticePeriodic
    (T : StressField) (u : LocalVelocityField)
    (hT : LatticePeriodic T)
    (hu : LatticePeriodic u) :
    LatticePeriodic (stressEnergyFlux T u) := by
  intro z x
  unfold stressEnergyFlux
  rw [hT z x, hu z x]

theorem velocityGradient_latticePeriodic
    (u : LocalVelocityField)
    (hu : LatticePeriodic u) :
    LatticePeriodic (velocityGradient u) := by
  intro z x
  unfold velocityGradient
  rw [fderiv_latticePeriodic u hu z x]

theorem viscousEnergyFlux_latticePeriodic
    (u : LocalVelocityField)
    (hu : LatticePeriodic u) :
    LatticePeriodic (viscousEnergyFlux u) :=
  stressEnergyFlux_latticePeriodic
    (velocityGradient u) u
    (velocityGradient_latticePeriodic u hu) hu

/-- Every component of the exact local-energy flux preserves the same lattice. -/
theorem localEnergyFlux_latticePeriodic
    (ν : Viscosity)
    (p : LocalScalarField) (T : StressField)
    (u : LocalVelocityField)
    (hp : LatticePeriodic p)
    (hT : LatticePeriodic T)
    (hu : LatticePeriodic u) :
    LatticePeriodic (localEnergyFlux ν p T u) := by
  intro z x
  unfold localEnergyFlux
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [kineticEnergyFlux_latticePeriodic u hu z x,
    pressureEnergyFlux_latticePeriodic p u hp hu z x,
    stressEnergyFlux_latticePeriodic T u hT hu z x,
    viscousEnergyFlux_latticePeriodic u hu z x]

private noncomputable def
    derivativeCoordinateReadout
    (i j : Coordinate) :
    (PhysicalSpace →L[ℝ] PhysicalSpace) →L[ℝ] ℝ :=
  (EuclideanSpace.proj i) ∘L
    ((ContinuousLinearMap.apply ℝ PhysicalSpace)
      (EuclideanSpace.single j 1))

theorem kineticEnergyDensity_contDiff
    (u : LocalVelocityField)
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (kineticEnergyDensity u) := by
  unfold kineticEnergyDensity
  have hsum :
      ContDiff ℝ 1
        (fun x =>
          ∑ i : Coordinate, u x i * u x i) := by
    apply ContDiff.sum
    intro i _
    exact
      ((contDiff_piLp_apply 2).comp hu).mul
        ((contDiff_piLp_apply 2).comp hu)
  exact ContDiff.const_smul (2 : ℝ)⁻¹ hsum

theorem kineticEnergyFlux_contDiff
    (u : LocalVelocityField)
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (kineticEnergyFlux u) := by
  unfold kineticEnergyFlux
  exact (kineticEnergyDensity_contDiff u hu).fun_smul hu

theorem pressureEnergyFlux_contDiff
    (p : LocalScalarField) (u : LocalVelocityField)
    (hp : ContDiff ℝ 1 p)
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (pressureEnergyFlux p u) := by
  unfold pressureEnergyFlux
  exact hp.fun_smul hu

theorem stressEnergyFlux_contDiff
    (T : StressField) (u : LocalVelocityField)
    (hT : ContDiff ℝ 1 T)
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (stressEnergyFlux T u) := by
  rw [contDiff_piLp 2]
  intro j
  change ContDiff ℝ 1
    (fun x =>
      ∑ i : Coordinate, u x i * T x i j)
  apply ContDiff.sum
  intro i hi
  exact
    ((contDiff_piLp_apply 2).comp hu).mul
      ((contDiff_pi.mp (contDiff_pi.mp hT i) j))

/-- A spatially `C²` velocity has a spatially `C¹` gradient tensor. -/
theorem velocityGradient_contDiff
    (u : LocalVelocityField)
    (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (velocityGradient u) := by
  have hDerivative :
      ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  change ContDiff ℝ 1
    (derivativeCoordinateReadout i j ∘ fderiv ℝ u)
  exact
    (derivativeCoordinateReadout i j).contDiff.comp
      hDerivative

theorem viscousEnergyFlux_contDiff
    (u : LocalVelocityField)
    (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (viscousEnergyFlux u) := by
  unfold viscousEnergyFlux
  exact stressEnergyFlux_contDiff
    (velocityGradient u) u
    (velocityGradient_contDiff u hu)
    (hu.of_le (by norm_num))

/-- Spatial regularity needed by the periodic-cell divergence readout. -/
theorem localEnergyFlux_contDiff
    (ν : Viscosity)
    (p : LocalScalarField) (T : StressField)
    (u : LocalVelocityField)
    (hp : ContDiff ℝ 1 p)
    (hT : ContDiff ℝ 1 T)
    (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (localEnergyFlux ν p T u) := by
  unfold localEnergyFlux
  exact
    (((kineticEnergyFlux_contDiff u
        (hu.of_le (by norm_num))).add
      (pressureEnergyFlux_contDiff p u hp
        (hu.of_le (by norm_num)))).add
      (stressEnergyFlux_contDiff T u hT
        (hu.of_le (by norm_num)))).sub
      ((viscousEnergyFlux_contDiff u hu).const_smul
        ν.coeff)

/--
The complete periodic local-energy transport vector has no net divergence
through the physical fundamental cell.
-/
theorem physicalUnitCell_localEnergyFlux_divergence_integral_eq_zero
    (ν : Viscosity)
    (p : LocalScalarField) (T : StressField)
    (u : LocalVelocityField)
    (hp : ContDiff ℝ 1 p)
    (hT : ContDiff ℝ 1 T)
    (hu : ContDiff ℝ 2 u)
    (hpPeriodic : LatticePeriodic p)
    (hTPeriodic : LatticePeriodic T)
    (huPeriodic : LatticePeriodic u) :
    (∫ x in physicalUnitCell,
      velocityDivergence (localEnergyFlux ν p T u) x) = 0 :=
  physicalUnitCell_velocityDivergence_integral_eq_zero
    (localEnergyFlux ν p T u)
    (localEnergyFlux_contDiff ν p T u hp hT hu)
    (localEnergyFlux_latticePeriodic
      ν p T u hpPeriodic hTPeriodic huPeriodic)

end

end ThreeDimensionalPeriodicLocalEnergyFluxTransport
end NavierStokes
end SaturationMonoid
