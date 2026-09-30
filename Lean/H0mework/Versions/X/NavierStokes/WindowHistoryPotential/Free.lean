import H0mework.Versions.X.NavierStokes.WindowHistoryPotential.Control

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPotentialFree
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowTraceWholeHistory (metric metricAction projection projected finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowHistoryPotentialAction (fiber lifted)
open NativeWindowHistoryPotentialControl (nonlinearWork massBudget)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem lift_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T I L P : E →L[ℝ] E) (c : ℝ) (same : ∀ x,T x=I x+c • L x+P x) (v : Lp E 2 averageMeasure) :
    T.compLpL 2 averageMeasure v=I.compLpL 2 averageMeasure v+c • L.compLpL 2 averageMeasure v+P.compLpL 2 averageMeasure v := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLpL v,I.coeFn_compLpL v,L.coeFn_compLpL v,P.coeFn_compLpL v,
    Lp.coeFn_add (I.compLpL 2 averageMeasure v+c • L.compLpL 2 averageMeasure v) (P.compLpL 2 averageMeasure v),
    Lp.coeFn_add (I.compLpL 2 averageMeasure v) (c • L.compLpL 2 averageMeasure v),Lp.coeFn_smul c (L.compLpL 2 averageMeasure v)]
    with lag t i l p sum part smul
  rw [t,sum,Pi.add_apply,part,Pi.add_apply,smul,Pi.smul_apply,i,l,p,same]

theorem source_metric_split (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) :
    metricAction seed frame M F R (finiteHistory seed time M)=finiteHistory seed time M+
      nu.coeff • laplacianAction nu M (finiteHistory seed time M)+lifted seed frame M F R (finiteHistory seed time M) := by
  have original := lift_sum (E := wholePhysical) (metric seed frame M F R) (projection M) (laplacianFiber nu M)
    (fiber seed frame M F R) nu.coeff (NativeWindowHistoryPotentialAction.metric_split seed frame M F R) (finiteHistory seed time M)
  have same : projected M (finiteHistory seed time M)=finiteHistory seed time M :=
    NativeWindowTraceWholeHistory.projected_idempotent M (NativeWindowTraceWholeHistory.history seed time)
  have read : metricAction seed frame M F R (finiteHistory seed time M)=projected M (finiteHistory seed time M)+
    nu.coeff • laplacianAction nu M (finiteHistory seed time M)+lifted seed frame M F R (finiteHistory seed time M) := by
    simpa only [metricAction,projected,laplacianAction,lifted] using! original
  exact read.trans (congrArg (fun v : H => v+nu.coeff • laplacianAction nu M (finiteHistory seed time M)+
    lifted seed frame M F R (finiteHistory seed time M)) same)

/-- The original full nonlinear and shadow-forcing work in I + nu Laplacian. -/
def freeWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  let h:=finiteHistory seed time M
  let z:=action seed M time h+nu.coeff • laplacianAction nu M h+forcingHistory seed M time
  2*inner ℝ h z+2*nu.coeff*inner ℝ (laplacianAction nu M h) z

theorem source_input (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    action seed M time (finiteHistory seed time M)+nu.coeff • laplacianAction nu M (finiteHistory seed time M)+forcingHistory seed M time=
      NativeWindowHistoryOseen.rateHistory seed M time+nu.coeff • laplacianAction nu M (finiteHistory seed time M) := by
  have original := congrArg (fun v : H => v+nu.coeff • laplacianAction nu M (finiteHistory seed time M))
    (NativeWindowHistoryOseen.source_equation seed M time)
  exact (add_right_comm _ _ _).trans original.symm

private theorem green_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h t p l a f : E) (nu : ℝ) (same : t=h+nu • l+p) :
    2*inner ℝ t (a+f)= -2*nu*inner ℝ t l+
      (2*inner ℝ h (a+nu • l+f)+2*nu*inner ℝ l (a+nu • l+f))+2*inner ℝ p (a+nu • l+f) := by
  rw [same]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  ring

theorem source_green (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) :
    NativeWindowMetricGraphGreen.sourceRate seed frame M F R time=
      -2*nu.coeff*inner ℝ (metricAction seed frame M F R (finiteHistory seed time M))
        (laplacianAction nu M (finiteHistory seed time M))+freeWork seed M time+nonlinearWork seed frame M F R time := by
  have symmetric := NativeWindowMetricGraphHistory.action_symmetric seed frame M F R (finiteHistory seed time M)
    (action seed M time (finiteHistory seed time M)+forcingHistory seed M time)
  have first := congrArg (fun x : ℝ => 2*x) symmetric.symm
  have last := green_algebra (E := H) (finiteHistory seed time M) (metricAction seed frame M F R (finiteHistory seed time M))
    (lifted seed frame M F R (finiteHistory seed time M)) (laplacianAction nu M (finiteHistory seed time M))
    (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time) nu.coeff
    (source_metric_split seed frame M F R time)
  exact first.trans last

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ R≥low,∀ cutoff≥low,∀ M,
      ∀ frame∈Icc 0 horizon,∀ time∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
      NativeWindowMetricGraphGreen.sourceRate seed frame M (integerWaveFrequencyCube cutoff) R time ≤
        -(nu.coeff^2/2)*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C+freeWork seed M time := by
  have first := @NativeWindowMetricGraphHistory.source_history_bound nu seed horizon nonnegative
  rcases first with ⟨one,C1,C10,heat⟩
  obtain ⟨two,C2,C20,nonlinear⟩ := NativeWindowHistoryPotentialControl.source_nonlinear_bound seed horizon nonnegative
    (nu.coeff^2/2) (by positivity [nu.coeff_pos])
  refine ⟨max one two,C1*massBudget seed+C2,by positivity [NativeWindowHistoryPotentialControl.massBudget_nonnegative seed],
    fun R above cutoff covered M frame frameInside time timeInside cover => ?_⟩
  have h := (heat R ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered) M frame frameInside
    (finiteHistory seed time M)).2
  have p := nonlinear R ((le_max_right _ _).trans above) cutoff ((le_max_right _ _).trans covered)
    M frame frameInside time timeInside cover
  have mass := mul_le_mul_of_nonneg_left (NativeWindowHistoryPotentialControl.source_mass_bound seed M time timeInside.1) C10
  have original := source_green seed frame M (integerWaveFrequencyCube cutoff) R time
  have signed := le_abs_self (nonlinearWork seed frame M (integerWaveFrequencyCube cutoff) R time)
  linarith only [h,p,mass,original,signed]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem freeWork_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (time : ℝ) (time0 : 0≤time) :
    freeWork seed M (step.2.clockAdvance+time)=freeWork step.1 M time := by
  have operators:=NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  simp only [freeWork,operators.1,NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPotentialFree
