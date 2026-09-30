import H0mework.NavierStokes.WindowEnergyTraceWhole.Source
import H0mework.NavierStokes.WindowEnergyTraceTerminal.MixedWindow

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceWholeHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeEndpointVelocityCarrier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem restrict_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) (M : ℕ) :
    restrictCLM (modes M) (modes_zero M) (modes_closed M) (original seed time)=NativeWindowTraceAdjoint.value seed M time := by
  rw [NativeWindowTraceAdjoint.value,NativeWindowStageNineSource.lift_load seed time nonnegative]
  change restrictCLM (modes M) (modes_zero M) (modes_closed M) (original seed time)=
    restrictCLM (modes M) (modes_zero M) (modes_closed M) (NativeUnheatedSourceQuadraticApprox.physicalSource seed time)
  rw [NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
  rfl

theorem finiteHistory_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) (M : ℕ) :
    finiteHistory seed time M =ᵐ[averageMeasure] fun shift => includeCLM (modes M) (modes_closed M)
      (NativeWindowTraceAdjoint.value seed M (time-shift)) := by
  filter_upwards [finiteHistory_ae seed time M,NativeWindowHistoryGNS.average_support] with shift read support
  rw [read,projection,ContinuousLinearMap.comp_apply,restrict_original seed (time-shift) (by linarith) M]

def joint (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    wholePhysical →L[ℝ] wholePhysical :=
  (includeCLM (modes M) (modes_closed M)).comp
    ((LinearMap.toContinuousLinearMap (NativeWindowTraceCutOperator.jointTest seed frame (modes M) F R)).comp
      (restrictCLM (modes M) (modes_zero M) (modes_closed M)))

def jointHistory (seed : GeneratedWholeRestartCurrent nu) (frame time : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) : H :=
  (joint seed frame M F R).compLpL 2 averageMeasure (history seed time)

theorem jointHistory_ae (seed : GeneratedWholeRestartCurrent nu) (frame time : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    jointHistory seed frame time M F R =ᵐ[averageMeasure] fun shift => joint seed frame M F R (original seed (time-shift)) := by
  filter_upwards [(joint seed frame M F R).coeFn_compLpL (history seed time),history_ae seed time] with shift read actual
  change ((joint seed frame M F R).compLpL 2 averageMeasure (history seed time)) shift=_
  rw [read,actual]
  rfl

theorem jointHistory_norm (seed : GeneratedWholeRestartCurrent nu) (frame time : ℝ) (nonnegative : 0 ≤ time)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    ‖jointHistory seed frame time M F R‖^2=∫ shift,
      ‖coefficients (modes M) (NativeWindowTraceCutOperator.jointTest seed frame (modes M) F R
        (NativeWindowTraceAdjoint.value seed M (time-shift)))‖^2 ∂averageMeasure := by
  rw [norm_square]
  apply integral_congr_ae
  filter_upwards [jointHistory_ae seed frame time M F R,NativeWindowHistoryGNS.average_support] with shift read support
  rw [read,joint,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,include_norm (modes M) (modes_zero M),
    restrict_original seed (time-shift) (by linarith) M]
  rfl

theorem terminal_energy (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    ‖jointHistory seed time time M F R‖^2=NativeWindowTraceEndpointWindow.terminalEnergy seed time M F R :=
  jointHistory_norm seed time time nonnegative M F R

theorem source_mixed_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ R ≥ low,∀ cutoff ≥ low,∀ M,
      (∀ k ∈ integerWaveFrequencyCube cutoff,k ≠ 0 → k ∈ modes M) →∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,
      ‖jointHistory seed frame time M (integerWaveFrequencyCube cutoff) R‖^2 ≤
        (1+epsilon)*nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M time+C := by
  obtain ⟨low,C,C0,paid⟩ := NativeWindowTraceTerminalMixedWindow.source_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun R above cutoff covered M cover frame framed time inside => ?_⟩
  rw [jointHistory_norm seed frame time inside.1]
  exact paid R above cutoff covered M frame framed time inside cover

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem joint_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame : ℝ) (nonnegative : 0 ≤ frame)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    joint seed (step.2.clockAdvance+frame) M F R=joint step.1 frame M F R := by
  exact congrArg (fun op : Module.End ℝ (physicalSpace (modes M)) =>
    (includeCLM (modes M) (modes_closed M)).comp ((LinearMap.toContinuousLinearMap op).comp
      (restrictCLM (modes M) (modes_zero M) (modes_closed M))))
        (NativeWindowTraceCutOperator.jointTest_next seed step generated frame nonnegative (modes M) F R)

theorem jointHistory_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    jointHistory seed (step.2.clockAdvance+frame) (step.2.clockAdvance+time) M F R=jointHistory step.1 frame time M F R := by
  exact congrArg₂ (fun (op : wholePhysical →L[ℝ] wholePhysical) (v : H) => op.compLpL 2 averageMeasure v)
    (joint_next seed step generated frame frame0 M F R) (history_next seed step generated time time0)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceWholeHistory
