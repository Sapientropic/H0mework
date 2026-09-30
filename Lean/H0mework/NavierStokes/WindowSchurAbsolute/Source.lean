import H0mework.NavierStokes.WindowSchurAbsolute.Carrier
import H0mework.NavierStokes.WindowSchurAbsolute.Kernel

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowTraceWholeHistory (original original_bound)
open NativeWindowKernelHalfDensity (rootKernel)
noncomputable section
variable {nu : Viscosity}

abbrev H := Lp wholePhysical 2 (volume : Measure ℝ)

theorem original_memLp (seed : GeneratedWholeRestartCurrent nu) :
    MemLp (original seed) ∞ (volume : Measure ℝ) := by
  have full:= (NativeUnifiedCompleteSource.source_Linfty seed).aestronglyMeasurable
  have measured:=NativeForwardWindowPairingReadout.meanRead.continuous.comp_aestronglyMeasurable full
  apply memLp_top_of_bound _ (NativeUnifiedCompleteSource.budget seed)
    (Eventually.of_forall (original_bound seed))
  apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
  change AEStronglyMeasurable (fun s => (NativeUnifiedCompleteSource.source seed s).fst) volume
  exact measured

def history (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : H :=
  NativeWindowAbsoluteTimeCarrier.field rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
    (original seed) (original_memLp seed) time

def rate (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : H :=
  NativeWindowAbsoluteTimeCarrier.field (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    (original seed) (original_memLp seed) time

theorem history_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    history seed time =ᵐ[volume] fun sample => rootKernel (time-sample) • original seed sample :=
  NativeWindowAbsoluteTimeCarrier.field_ae _ _ _ _ _

theorem rate_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    rate seed time =ᵐ[volume] fun sample => deriv rootKernel (time-sample) • original seed sample :=
  NativeWindowAbsoluteTimeCarrier.field_ae _ _ _ _ _

theorem root_zero_outside (x : ℝ) (outside : x∉Icc (-2:ℝ) (-1)) : rootKernel x=0 := by
  by_contra nonzero
  exact outside (NativeWindowKernelHalfDensity.support_interval ▸ (subset_closure nonzero))

theorem rate_zero_outside (x : ℝ) (outside : x∉Icc (-2:ℝ) (-1)) : deriv rootKernel x=0 :=
  by
    by_contra nonzero
    exact outside (NativeWindowKernelHalfDensity.derivative_support (subset_closure nonzero))

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    HasDerivAt (history seed) (rate seed time) time := by
  obtain ⟨A,A0,slopes⟩:=NativeWindowKernelHalfDensity.shift_quotient_bound
  obtain ⟨B,B0,point⟩:=NativeWindowKernelHalfDensity.source_derivative_bound
  exact NativeWindowAbsoluteTimeCarrier.field_hasDerivAt rootKernel (deriv rootKernel)
    (NativeWindowKernelHalfDensity.root_memLp 2) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    NativeWindowKernelHalfDensity.shifted_derivative (A+B) (add_nonneg A0 B0)
    (fun t s d => (slopes t s d).trans (le_add_of_nonneg_right B0))
    (fun x => (point x).trans (le_add_of_nonneg_left A0))
    root_zero_outside rate_zero_outside (original seed) (original_memLp seed)
    (NativeUnifiedCompleteSource.budget seed) (original_bound seed) time

def rateBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  ‖(NativeWindowKernelHalfDensity.derivative_memLp 2).toLp (deriv rootKernel)‖*
    ‖(original_memLp seed).toLp (original seed)‖

theorem source_rate_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖rate seed time‖ ≤ rateBudget seed :=
  NativeWindowAbsoluteTimeCarrier.field_norm_bound _ _ _ _ _

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeSource
