import H0mework.NavierStokes.MacroAction.FiniteMacro
import H0mework.NavierStokes.GlobalAction.GlobalTail
import H0mework.NavierStokes.GlobalAction.GeneratedGlobalSpacetime
import H0mework.NavierStokes.SourceAction.GeneratedSpacetime

set_option autoImplicit false
open scoped ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeEventualTailControl

open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeReceiptTimeProfile NativeGeneratedGlobalSpacetime NativeSpacetimeControl

noncomputable section

variable {nu : Viscosity}

def terminal (seed : GeneratedWholeRestartCurrent nu) : GeneratedWholeRestartEndpointMacroTerminalRun seed :=
  Classical.choice (NativeFiniteMacroControl.source_finite_macro_terminal seed)

def sourceTail (seed : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeGlobalPhysicalTrajectory (run (terminal seed).terminal 2) :=
  NativeGlobalTailOccurrence.tail (terminal seed).globalPhysicalTrajectory 2

def sourceWindow (seed : GeneratedWholeRestartCurrent nu) : Window (run (terminal seed).terminal 2).receipt :=
  NativeGeneratedSpacetime.successorWindow (terminal seed).terminal

theorem sourceWindow_first (seed : GeneratedWholeRestartCurrent nu) : (sourceWindow seed).first = 0 := rfl

theorem sourceWindow_last (seed : GeneratedWholeRestartCurrent nu) :
    (sourceWindow seed).last = (run (terminal seed).terminal 2).duration := rfl

def offset (seed : GeneratedWholeRestartCurrent nu) : ℝ := elapsedTime (terminal seed).terminal 2

theorem sourceTail_reads_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    (sourceTail seed).physicalPath time = (terminal seed).globalPhysicalTrajectory.physicalPath (offset seed + time) :=
  NativeGlobalTailOccurrence.tail_path (terminal seed).globalPhysicalTrajectory 2 time nonnegative

theorem source_tail_spacetime_control (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field (sourceTail seed)) NativeGeneratedGlobalSpacetime.halfspace ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField (sourceTail seed)) NativeGeneratedGlobalSpacetime.halfspace ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField (sourceTail seed) modes) NativeGeneratedGlobalSpacetime.halfspace :=
  global_spacetime_control (sourceWindow seed) (sourceWindow_first seed) (sourceWindow_last seed) (sourceTail seed) modes

theorem source_tail_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain)
    (contained : domain ⊆ NativeGeneratedGlobalSpacetime.halfspace) :
    ∀ observation ∈ ({field (sourceTail seed), vorticityField (sourceTail seed), correctionField (sourceTail seed) modes} :
        Set (Spacetime → PhysicalSpace)),
      ∃ budget : ℝ, 0 ≤ budget ∧
        MemLp (iteratedFDerivWithin ℝ order observation NativeGeneratedGlobalSpacetime.halfspace) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order observation NativeGeneratedGlobalSpacetime.halfspace) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) :=
  global_all_order_Lp (sourceWindow seed) (sourceWindow_first seed) (sourceWindow_last seed)
    (sourceTail seed) modes order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeEventualTailControl
