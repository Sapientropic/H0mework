import H0mework.NavierStokes.NormControl.Global
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeNormControl

open Set Metric
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

noncomputable section

variable {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)

/-- Continuous observations of a bounded finite-dimensional image inherit
one bound from the original physical kinetic ball. -/
theorem proper_observation_bddAbove {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup E] (read : WholeRestartVelocityEndpointState →L[ℝ] V)
    (observe : V → E) (continuous : Continuous observe) :
    BddAbove (range fun time : ℝ => ‖observe (read (lineage.globalAbsoluteVelocityTrajectory time))‖) := by
  let radius := ‖read‖ * ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖
  obtain ⟨bound, bounds⟩ :=
    ((isCompact_closedBall (0 : V) radius).image continuous.norm).bddAbove
  refine ⟨bound, ?_⟩
  rintro _ ⟨time, rfl⟩
  apply bounds
  refine ⟨read (lineage.globalAbsoluteVelocityTrajectory time), ?_, rfl⟩
  simpa only [mem_closedBall, dist_zero_right] using global_read_norm_le lineage read time

def finiteFourierRead (waves : Finset NonzeroIntegerWavevector) :
    WholeRestartVelocityEndpointState →L[ℝ] (waves → EuclideanSpace ℂ (Fin 3)) :=
  ContinuousLinearMap.pi fun wave => lp.evalCLM ℝ _ 2 wave.1

@[simp] theorem finiteFourierRead_apply (waves : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) (wave : waves) :
    finiteFourierRead waves state wave = state wave.1 := rfl

/-- Every continuous normed readout of any fixed finite Fourier inventory
is bounded on the entire original macro path. The bound may depend on the inventory. -/
theorem finite_observation_bddAbove (waves : Finset NonzeroIntegerWavevector)
    {E : Type*} [NormedAddCommGroup E]
    (observe : (waves → EuclideanSpace ℂ (Fin 3)) → E) (continuous : Continuous observe) :
    BddAbove (range fun time : ℝ =>
      ‖observe (fun wave : waves => lineage.globalAbsoluteVelocityTrajectory time wave.1)‖) :=
  proper_observation_bddAbove lineage (finiteFourierRead waves) observe continuous

end
end SaturationMonoid.NavierStokes.NativeNormControl
