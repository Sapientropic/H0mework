import H0mework.NavierStokes.WindowEnergyTraceWhole.HistoryPreparation

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySpatialWords
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceWholeHistory (H finiteHistory)
open NativeWindowHistoryOseen (action adjoint forcingHistory)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section
variable {nu : Viscosity}

def fiber (M : ℕ) (directions : List Coordinate) : wholePhysical →L[ℝ] wholePhysical :=
  NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap
    (NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) directions))

def operator (M : ℕ) (directions : List Coordinate) : H →L[ℝ] H :=
  (fiber M directions).compLpL 2 averageMeasure

def history (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) : H :=
  operator M directions (finiteHistory seed time M)

theorem history_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    history seed M directions time =ᵐ[averageMeasure] fun shift => includeCLM (modes M) (modes_closed M)
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift)) := by
  filter_upwards [(fiber M directions).coeFn_compLpL (finiteHistory seed time M),
    NativeWindowHistoryOseen.history_original seed M time] with shift read original
  have first : history seed M directions time shift=fiber M directions (finiteHistory seed time M shift) := read
  rw [first,original]
  exact NativeWindowHistoryOseen.lift_included M _ _

def commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) : H →L[ℝ] H :=
  (operator M directions).comp (action seed M time)-(action seed M time).comp (operator M directions)

def rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) : H :=
  operator M directions (NativeWindowHistoryOseen.rateHistory seed M time)

private theorem linear_source_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D A : E →L[ℝ] E) (v f : E) : D (A v+f)=A (D v)+(D.comp A-A.comp D) v+D f := by
  simp only [map_add,sub_apply,ContinuousLinearMap.comp_apply]
  abel

theorem rate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    rate seed M directions time=action seed M time (history seed M directions time)+
      commutator seed M directions time (finiteHistory seed time M)+operator M directions (forcingHistory seed M time) :=
  (congrArg (fun v : H => operator M directions v) (NativeWindowHistoryOseen.source_equation seed M time)).trans
    (linear_source_identity (E := H) (operator M directions) (action seed M time)
      (finiteHistory seed time M) (forcingHistory seed M time))

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    HasDerivAt (history seed M directions) (rate seed M directions time) time := by
  exact (operator M directions).hasFDerivAt.comp_hasDerivAt (E := H) (F := H) time (NativeWindowHistoryOseen.history_hasDerivAt seed M time)

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate) (time : ℝ) :
    HasDerivAt (history seed M directions)
      (action seed M time (history seed M directions time)+commutator seed M directions time (finiteHistory seed time M)+
        operator M directions (forcingHistory seed M time)) time := by
  rw [← rate_original]
  exact source_hasDerivAt seed M directions time

theorem source_preparation (M : ℕ) (directions : List Coordinate) :
    history stackedShortCurrent M directions (-2)=NativeWindowHistoryPreparedEnergy.initial M directions := by
  apply Lp.ext
  filter_upwards [history_original stackedShortCurrent M directions (-2),
    NativeWindowTraceWholeHistory.constant_ae (includeCLM (modes M) (modes_closed M)
      (NativeWindowStageNineSource.coefficient stackedShortCurrent M directions 0)),
    NativeWindowTraceEndpointWindow.average_interval] with shift source fixed support
  have initial : NativeWindowHistoryPreparedEnergy.initial M directions shift=includeCLM (modes M) (modes_closed M)
      (NativeWindowStageNineSource.coefficient stackedShortCurrent M directions 0) := fixed
  rw [source,initial]
  simp only [NativeWindowStageNineSource.coefficient,
    NativeWindowHierarchyPairWindow.state_before stackedShortCurrent (-2-shift) (by linarith [support.1])]

theorem source_initial_budget (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ B : ℝ,0 ≤ B ∧∀ R ≥ low,∀ cutoff ≥ low,∀ M,∀ frame ∈ Icc 0 horizon,∀ directions : List Coordinate,
      inner ℝ (history stackedShortCurrent M directions (-2))
        (NativeWindowTraceWholeHistory.metricAction stackedShortCurrent frame M (integerWaveFrequencyCube cutoff) R
          (history stackedShortCurrent M directions (-2))) ≤ NativeWindowHistoryPreparedEnergy.budget B directions := by
  obtain ⟨low,B,B0,paid⟩ := NativeWindowHistoryPreparedEnergy.source_all_word_bound horizon nonnegative
  refine ⟨low,B,B0,fun R above cutoff covered M frame inside directions => ?_⟩
  have same := congrArg (fun v : H => inner ℝ v
    (NativeWindowTraceWholeHistory.metricAction stackedShortCurrent frame M (integerWaveFrequencyCube cutoff) R v))
    (source_preparation M directions)
  exact same.trans_le (paid R above cutoff covered M frame inside directions)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem history_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    history seed M directions (step.2.clockAdvance+time)=history step.1 M directions time :=
  congrArg (fun v : H => operator M directions v)
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

theorem rate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (directions : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    rate seed M directions (step.2.clockAdvance+time)=rate step.1 M directions time :=
  congrArg (fun v : H => operator M directions v)
    (NativeWindowHistoryOseen.rateHistory_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySpatialWords
