import H0mework.Versions.X.NavierStokes.WindowEnergyTraceCut.CutActionPhysical
import H0mework.Versions.X.NavierStokes.WindowHistoryOseen.Equation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCutAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryOseen (H action adjoint forcingHistory)
open NativeWindowTraceWholeHistory (finiteHistory joint)
noncomputable section
variable {nu : Viscosity}

def jointAction (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : H →L[ℝ] H := (joint seed frame M F R).compLpL 2 averageMeasure

def terminal (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : H := jointAction seed frame M F R (finiteHistory seed time M)

theorem joint_included (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : physicalSpace (modes M)) :
    joint seed frame M F R (includeCLM (modes M) (modes_closed M) v)=
      includeCLM (modes M) (modes_closed M) (NativeWindowTraceCutOperator.jointTest seed frame (modes M) F R v) := by
  simp only [joint,ContinuousLinearMap.comp_apply,restrict_include]
  rfl

theorem terminal_ae (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : terminal seed frame M F R time =ᵐ[averageMeasure]
      fun shift => includeCLM (modes M) (modes_closed M) (NativeWindowTraceEndpointWindow.terminal seed frame M F R (time-shift)) := by
  filter_upwards [(joint seed frame M F R).coeFn_compLpL (finiteHistory seed time M),
    NativeWindowHistoryOseen.history_original seed M time] with shift read original
  change terminal seed frame M F R time shift=_ at read
  rw [read,original]
  exact joint_included seed frame M F R _

theorem terminal_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : terminal seed frame M F R time=
      NativeWindowTraceWholeHistory.jointHistory seed frame time M F R := by
  apply Lp.ext
  filter_upwards [terminal_ae seed frame M F R time,NativeWindowTraceWholeHistory.jointHistory_ae seed frame time M F R]
    with shift first last
  rw [first,last,joint,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    NativeWindowHistoryOseen.restrict_original_total]
  rfl

def forcing (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : H :=
  jointAction seed frame M F R (action seed M time (finiteHistory seed time M))+
    adjoint seed M time (terminal seed frame M F R time)+jointAction seed frame M F R (forcingHistory seed M time)

def actual (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (forcing seed frame M F R time) (finiteHistory seed time M)+
    inner ℝ (forcingHistory seed M time) (terminal seed frame M F R time)

def diagonal (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (finiteHistory seed time M) (terminal seed frame M F R time)

theorem terminal_continuous (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : Continuous (terminal seed frame M F R) :=
  (jointAction seed frame M F R).continuous.comp (NativeWindowHistoryOseen.history_continuous seed M)

private theorem mapped_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →L[ℝ] E) (f : ℝ → E) (a b : ℝ) (paid : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => J (f t)) volume a b :=
  ⟨J.integrable_comp paid.1,J.integrable_comp paid.2⟩

theorem forcing_rate (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : forcing seed frame M F R time=
      jointAction seed frame M F R (NativeWindowHistoryOseen.rateHistory seed M time)+
        adjoint seed M time (terminal seed frame M F R time) := by
  rw [NativeWindowHistoryOseen.source_equation]
  simp only [forcing,map_add]
  abel

theorem forcing_integrable (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (a b : ℝ) : IntervalIntegrable (forcing seed frame M F R) volume a b := by
  let J:=jointAction seed frame M F R
  have first:=mapped_integrable (E := H) J (NativeWindowHistoryOseen.rateHistory seed M) a b
    (NativeWindowHistoryOseen.rateHistory_integrable seed M a b)
  have second:Continuous (fun t => adjoint seed M t (terminal seed frame M F R t)) :=
    Continuous.clm_apply (𝕜 := ℝ) (E := H) (F := H)
      (by exact NativeWindowHistoryOseen.adjoint_continuous seed M) (terminal_continuous seed frame M F R)
  have same:forcing seed frame M F R=(fun t => J (NativeWindowHistoryOseen.rateHistory seed M t)+
      adjoint seed M t (terminal seed frame M F R t)) := funext (forcing_rate seed frame M F R)
  rw [same]
  exact first.add (second.intervalIntegrable a b)

theorem terminal_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : HasDerivAt (terminal seed frame M F R)
      (forcing seed frame M F R time-adjoint seed M time (terminal seed frame M F R time)) time := by
  convert! HasFDerivAt.comp_hasDerivAt (F := H) (E := H) time (jointAction seed frame M F R).hasFDerivAt
    (by exact NativeWindowHistoryOseen.source_hasDerivAt seed M time) using 1
  simp only [forcing,map_add]
  abel

theorem diagonal_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : HasDerivAt (diagonal seed frame M F R)
      (actual seed frame M F R time) time := by
  convert! HasDerivAt.inner (E := H) ℝ
    (by exact NativeWindowHistoryOseen.source_hasDerivAt seed M time)
    (by exact terminal_derivative seed frame M F R time) using 1
  simp only [actual]
  rw [inner_sub_right (𝕜 := ℝ) (finiteHistory seed time M),
    inner_add_left (𝕜 := ℝ) (action seed M time (finiteHistory seed time M))]
  have dual:=NativeWindowHistoryOseen.action_adjoint seed M time (finiteHistory seed time M) (terminal seed frame M F R time)
  have commute:=real_inner_comm (forcing seed frame M F R time) (finiteHistory seed time M)
  linarith only [dual,commute]

theorem diagonal_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : diagonal seed frame M F R time=
      NativeWindowHierarchyPairWindow.window seed (NativeWindowTraceCutAction.form seed frame M F R) 0 time := by
  rw [diagonal,L2.inner_def]
  calc
    _=(∫shift,NativeWindowTraceCutAction.diagonal seed frame M F R (time-shift) ∂averageMeasure) := by
      apply integral_congr_ae
      filter_upwards [NativeWindowHistoryOseen.history_original seed M time,terminal_ae seed frame M F R time]
        with shift first last
      rw [first,last]
      change inner ℝ (includeCLM (modes M) (modes_closed M) _) (includeCLM (modes M) (modes_closed M) _)=_
      rw [include_inner (modes M) (modes_zero M) (modes_closed M),restrict_include]
      rfl
    _=_ := by rw [NativeForwardWindowPairingReadout.density_integral]; rfl

theorem actual_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : actual seed frame M F R time=
      NativeWindowHierarchyPairWindow.window seed (NativeWindowTraceCutAction.form seed frame M F R) 1 time := by
  have same:diagonal seed frame M F R=NativeWindowHierarchyPairWindow.window seed (NativeWindowTraceCutAction.form seed frame M F R) 0 :=
    funext (diagonal_original seed frame M F R)
  have first:=diagonal_derivative seed frame M F R time
  rw [same] at first
  exact first.unique (NativeWindowHierarchyPairWindow.window_hasDerivAt seed (NativeWindowTraceCutAction.form seed frame M F R) 0 time)

theorem actual_continuous (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : Continuous (actual seed frame M F R) := by
  have same:actual seed frame M F R=NativeWindowHierarchyPairWindow.window seed (NativeWindowTraceCutAction.form seed frame M F R) 1 :=
    funext (actual_original seed frame M F R)
  rw [same]
  exact continuous_iff_continuousAt.mpr (fun time => (NativeWindowHierarchyPairWindow.window_hasDerivAt seed _ 1 time).continuousAt)

theorem source_write (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (a b : ℝ) :
    diagonal seed frame M F R b-diagonal seed frame M F R a=∫time in a..b,actual seed frame M F R time :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => diagonal_derivative seed frame M F R time)
    ((actual_continuous seed frame M F R).intervalIntegrable a b)).symm

theorem source_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ R≥low,∀ cutoff≥low,∀ M : ℕ,
      ∀ frame∈Icc 0 horizon,∀ time∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
        ‖actual seed frame M (integerWaveFrequencyCube cutoff) R time‖≤C := by
  obtain ⟨low,paid⟩:=NativeWindowTraceCutActionPhysical.pair_uniform seed horizon nonnegative
  obtain ⟨C,C0,bounded⟩:=paid 1
  refine ⟨low,C,C0,fun R above cutoff covered M frame fi time ti cover => ?_⟩
  rw [actual_original]
  exact bounded R above cutoff covered M frame fi time ti cover

theorem preparation_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : diagonal seed frame M F R (-2)=
      NativeWindowTraceCutAction.diagonal seed frame M F R 0 := by
  rw [diagonal_original,NativeWindowHierarchyPairWindow.window_initial seed _ (-2) le_rfl]
  rfl

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jointAction_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame : ℝ) (frame0 : 0≤frame)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    jointAction seed (step.2.clockAdvance+frame) M F R=jointAction step.1 frame M F R :=
  congrArg (fun J : wholePhysical →L[ℝ] wholePhysical => J.compLpL 2 averageMeasure)
    (NativeWindowTraceWholeHistory.joint_next seed step generated frame frame0 M F R)

theorem terminal_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame time : ℝ) (frame0 : 0≤frame) (time0 : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    terminal seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time)=terminal step.1 frame M F R time :=
  congrArg₂ (fun (J : H →L[ℝ] H) (v : H) => J v)
    (jointAction_next seed step generated frame frame0 M F R)
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0 M)

theorem forcing_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame time : ℝ) (frame0 : 0≤frame) (time0 : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    forcing seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time)=forcing step.1 frame M F R time := by
  have operators:=NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  simp only [forcing,jointAction_next seed step generated frame frame0,operators.1,operators.2,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0,
    terminal_next seed step generated frame time frame0 time0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

theorem actual_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame time : ℝ) (frame0 : 0≤frame) (time0 : 0≤time)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    actual seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time)=actual step.1 frame M F R time := by
  rw [actual_original,actual_original,NativeWindowTraceCutAction.form_next seed step generated frame frame0,
    NativeWindowHierarchyPairWindow.window_next seed _ 1 step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCutAction
