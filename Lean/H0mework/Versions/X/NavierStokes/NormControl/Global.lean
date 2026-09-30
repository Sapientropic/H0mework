import H0mework.Versions.X.NavierStokes.NormControl.Splice
import H0mework.NavierStokes.MacroRuntime.GlobalAbsoluteVelocity

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeNormControl

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open GeneratedInfiniteWholeRestartEndpointMacroLineage

noncomputable section

variable {nu : Viscosity} (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)

theorem macro_initial_velocity_norm_le (index : Nat) :
    ‖puncturedWholeVelocityEuclideanState (lineage.current index).initialState‖ ≤
      ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ := by
  induction index with
  | zero => exact le_rfl
  | succ index prior => exact (macro_next_velocity_norm_le (lineage.step index)).trans prior

theorem finite_macro_velocity_norm_le (length : Nat) (time : ℝ) :
    ‖lineage.finiteMacroAbsoluteVelocityTrajectory length time‖ ≤
      ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ := by
  induction length with
  | zero => exact le_rfl
  | succ length prior =>
      rw [finiteMacroAbsoluteVelocityTrajectory]
      by_cases before : time ≤ lineage.macroClock length
      · rw [endpointSplice_of_le _ _ _ _ before]
        exact prior
      · rw [endpointSplice_of_lt _ _ _ _ (lt_of_not_ge before)]
        exact (macro_stage_velocity_norm_le (lineage.step length) _).trans
          (macro_initial_velocity_norm_le lineage length)

/-- The original absolute path retains one physical kinetic bound through
every macro interface, including interfaces carrying a nonzero defect. -/
theorem global_velocity_norm_le (time : ℝ) :
    ‖lineage.globalAbsoluteVelocityTrajectory time‖ ≤
      ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ :=
  finite_macro_velocity_norm_le lineage (lineage.globalAbsoluteVelocityCoverIndex time) time

theorem global_read_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (read : WholeRestartVelocityEndpointState →L[ℝ] E) (time : ℝ) :
    ‖read (lineage.globalAbsoluteVelocityTrajectory time)‖ ≤
      ‖read‖ * ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ :=
  (read.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (global_velocity_norm_le lineage time) (norm_nonneg _))

theorem global_read_bddAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (read : WholeRestartVelocityEndpointState →L[ℝ] E) :
    BddAbove (range fun time : ℝ => ‖read (lineage.globalAbsoluteVelocityTrajectory time)‖) := by
  refine ⟨‖read‖ * ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact global_read_norm_le lineage read time

end
end SaturationMonoid.NavierStokes.NativeNormControl
