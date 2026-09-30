import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Energy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeActionWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowAbsoluteTimeIsometry (map)
open NativeWindowAbsoluteTimeEnergy (value energy power)
noncomputable section
variable {nu : Viscosity}
abbrev Lag := NativeWindowTraceWholeHistory.H

def word (M : ℕ) : Fin 4 → Lag →L[ℝ] Lag := Fin.cases
  ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure)
  (fun j => NativeWindowHistorySpatialWords.operator M [j])

def state (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) : Lag :=
  word M direction (NativeWindowTraceWholeHistory.finiteHistory seed time M)

def action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) : Lag :=
  word M direction (NativeWindowHistoryOseen.action seed M time
    (NativeWindowTraceWholeHistory.finiteHistory seed time M)+NativeWindowHistoryOseen.forcingHistory seed M time)

theorem state_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) :
    HasDerivAt (fun t => state seed M t direction) (action seed M time direction) time := by
  have derivative : HasDerivAt (fun t => state seed M t direction)
      (word M direction (NativeWindowHistoryOseen.rateHistory seed M time)) time :=
    (word M direction).hasFDerivAt.comp_hasDerivAt (E := Lag) (F := Lag) time
      (NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  have actual : word M direction (NativeWindowHistoryOseen.rateHistory seed M time)=action seed M time direction :=
    congrArg (fun v : Lag => word M direction v) (NativeWindowHistoryOseen.source_equation seed M time)
  exact actual ▸ derivative

theorem state_map (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) :
    map wholePhysical time (state seed M time direction)=value seed M time direction := by
  have natural (v : Lag) : map wholePhysical time (word M direction v)=
      NativeWindowAbsoluteTimeEnergy.word M direction (map wholePhysical time v) := by
    cases direction using Fin.cases <;>
      exact NativeWindowAbsoluteTimeIsometry.naturality wholePhysical _ time v
  rw [state,natural,NativeWindowAbsoluteTimeBridge.finite_map]
  exact NativeWindowAbsoluteTimeEnergy.word_project M direction (NativeWindowAbsoluteTimeSource.history seed time)

def originalEnergy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ direction,‖state seed M time direction‖^2

def originalPower (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ direction,2*inner ℝ (state seed M time direction) (action seed M time direction)

theorem energy_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    energy seed M time=originalEnergy seed M time := by
  simp only [energy,← state_map,LinearIsometry.norm_map,originalEnergy]

theorem originalEnergy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (originalEnergy seed M) (originalPower seed M time) time := by
  simpa only [originalEnergy,originalPower,Finset.sum_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun direction _ =>
      HasDerivAt.norm_sq (F := Lag) (state_hasDerivAt seed M time direction))

theorem power_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    power seed M time=originalPower seed M time := by
  have actual:=NativeWindowAbsoluteTimeEnergy.energy_hasDerivAt seed M time
  rw [funext (energy_original seed M)] at actual
  exact actual.unique (originalEnergy_hasDerivAt seed M time)

theorem source_native_power_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,
      originalEnergy seed M time ≤ C ∧ |originalPower seed M time| ≤ C := by
  obtain ⟨C,C0,paid⟩:=NativeWindowAbsoluteTimeEnergy.source_energy_power_bound seed horizon
  refine ⟨C,C0,fun M time inside => ?_⟩
  simpa only [energy_original,power_original] using paid M time inside

def clockWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ direction,2*inner ℝ (value seed M time direction)
    (NativeWindowAbsoluteTimeEnergy.word M direction (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time))

theorem action_map (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) :
    map wholePhysical time (action seed M time direction)=
      NativeWindowAbsoluteTimeEnergy.tangent seed M time direction+
        NativeWindowAbsoluteTimeEnergy.word M direction (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time) := by
  have natural (v : Lag) : map wholePhysical time (word M direction v)=
      NativeWindowAbsoluteTimeEnergy.word M direction (map wholePhysical time v) := by
    cases direction using Fin.cases <;>
      exact NativeWindowAbsoluteTimeIsometry.naturality wholePhysical _ time v
  have acted : action seed M time direction=word M direction (NativeWindowHistoryOseen.rateHistory seed M time) :=
    congrArg (fun v : Lag => word M direction v) (NativeWindowHistoryOseen.source_equation seed M time).symm
  rw [acted,natural]
  have connection:=NativeWindowAbsoluteTimeBridge.sampleDerivative_original seed M time
  have read:=congrArg (fun v : NativeWindowAbsoluteTimeSource.H => NativeWindowAbsoluteTimeEnergy.word M direction v) connection
  have split:=(NativeWindowAbsoluteTimeEnergy.word M direction).map_sub
    (map wholePhysical time (NativeWindowHistoryOseen.rateHistory seed M time))
    (NativeWindowAbsoluteTimeBridge.finiteRate seed M time)
  have projected : NativeWindowAbsoluteTimeEnergy.word M direction
      (NativeWindowAbsoluteTimeBridge.finiteRate seed M time)=NativeWindowAbsoluteTimeEnergy.tangent seed M time direction :=
    NativeWindowAbsoluteTimeEnergy.word_project M direction (NativeWindowAbsoluteTimeSource.rate seed time)
  have expanded:=(read.trans split).trans (congrArg (fun v : NativeWindowAbsoluteTimeSource.H =>
    NativeWindowAbsoluteTimeEnergy.word M direction
      (map wholePhysical time (NativeWindowHistoryOseen.rateHistory seed M time))-v) projected)
  exact (sub_eq_iff_eq_add.mp expanded.symm).trans (add_comm _ _)

theorem source_clock_work_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    clockWork seed M time=0 := by
  have each (j : Fin 4) : 2*inner ℝ (state seed M time j) (action seed M time j)=
      2*inner ℝ (value seed M time j) (NativeWindowAbsoluteTimeEnergy.actionRate seed M time j)+
      2*inner ℝ (value seed M time j)
        (NativeWindowAbsoluteTimeEnergy.word M j (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time)) := by
    have paired:=NativeWindowAbsoluteTimeIsometry.pairing wholePhysical time
      (state seed M time j) (action seed M time j)
    rw [state_map,action_map,NativeWindowAbsoluteTimeEnergy.source_action,inner_add_right (𝕜 := ℝ) (E := NativeWindowAbsoluteTimeSource.H)] at paired
    linarith only [paired]

  have equality : originalPower seed M time=power seed M time+clockWork seed M time := by
    simp only [originalPower,each,Finset.sum_add_distrib,power,clockWork]
  rw [power_original] at equality
  linarith

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem original_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    originalEnergy seed M (step.2.clockAdvance+time)=originalEnergy step.1 M time ∧
      originalPower seed M (step.2.clockAdvance+time)=originalPower step.1 M time := by
  simpa only [energy_original,power_original] using
    NativeWindowAbsoluteTimeEnergy.energy_power_next seed M step generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeActionWork
