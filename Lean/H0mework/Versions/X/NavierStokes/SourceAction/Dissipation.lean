import H0mework.Versions.X.NavierStokes.SourceAction.Evolution
import H0mework.NavierStokes.Accumulation.BoundaryContinuation

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeFullOrderDissipation

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderEvolution

noncomputable section

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed]
  {seed : Seed} {radius : ℕ}

/-- Keep the source dissipation that the pure propagation bound discards.
This is the actual derivative on the original Galerkin stage, ready for a
positive-time derivative-gain consumer at the cofinal reentry seed. -/
theorem stage_energy_retained_dissipation
    (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    deriv (fun actual => weightedVelocityEnergy (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory actual)) time +
        nu.coeff * weightedVelocityDissipation (wholeRestartModes radius)
          (wordWeight order ceiling) (stage.trajectory time) ≤
      wordRate order nu * finiteStateVelocityMajorant (wholeRestartModes radius)
        (stage.trajectory time) ^ 2 * weightedVelocityEnergy (wholeRestartModes radius)
          (wordWeight order ceiling) (stage.trajectory time) := by
  have source := NativeFullOrderStress.power_young (wholeRestartModes radius) order ceiling nonnegative
    (finiteStateWholeVelocity (wholeRestartModes radius) (stage.trajectory time))
    (finite_amplitude_summable (wholeRestartModes radius) (stage.trajectory time))
    (finite_velocity_supported (wholeRestartModes radius) (stage.trajectory time)) nu.coeff nu.coeff_pos
  rw [finite_majorant_eq, finite_energy_eq, finite_dissipation_eq] at source
  rw [(stage_weightedVelocityEnergy_action_hasDerivAt stage (wordWeight order ceiling) time inside).deriv]
  rw [show 2 * weightedVelocityNonlinearWork (wholeRestartModes radius) (wordWeight order ceiling)
      (stage.trajectory time) - 2 * nu.coeff * weightedVelocityDissipation (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory time) + nu.coeff * weightedVelocityDissipation
      (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time) =
    2 * weightedVelocityNonlinearWork (wholeRestartModes radius) (wordWeight order ceiling)
      (stage.trajectory time) - nu.coeff * weightedVelocityDissipation (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory time) by ring]
  rw [finite_work_eq_stress]
  exact source

end
end SaturationMonoid.NavierStokes.NativeFullOrderDissipation
