import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.History
import H0mework.Versions.X.NavierStokes.WindowSchur.CutActionSource
import H0mework.Versions.X.NavierStokes.WindowHistory.ForcingWork

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPotentialAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowTraceWholeHistory (metric metricAction projection joint finiteHistory gradient)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowMetricGraphPotential (potential)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def fiber (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : wholePhysical →L[ℝ] wholePhysical :=
  NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap
    (potential (modes M) F (NativeWindowTraceCutTime.fieldJet seed F R 0 frame)))

def lifted (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : H →L[ℝ] H := (fiber seed frame M F R).compLpL 2 averageMeasure

theorem metric_split (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : wholePhysical) :
    metric seed frame M F R v=projection M v+nu.coeff • laplacianFiber nu M v+fiber seed frame M F R v := by
  rw [NativeWindowTraceWholeHistory.metric_original,
    NativeWindowMetricGraphPotential.test_split seed frame (modes M) F R (modes_zero M) (modes_closed M)]
  simp only [map_add,map_smul]
  rfl

theorem fiber_joint (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : wholePhysical) :
    fiber seed frame M F R v= -joint seed frame M F R v-nu.coeff • laplacianFiber nu M v := by
  have actual:=metric_split seed frame M F R v
  change projection M v-joint seed frame M F R v=_ at actual
  rw [← sub_eq_iff_eq_add'] at actual
  exact actual.symm.trans (by abel)

private theorem lift_neg_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A J L : E →L[ℝ] E) (c : ℝ) (same : ∀ v,A v= -J v-c • L v) (v : Lp E 2 averageMeasure) :
    A.compLpL 2 averageMeasure v= -J.compLpL 2 averageMeasure v-c • L.compLpL 2 averageMeasure v := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL v,J.coeFn_compLpL v,L.coeFn_compLpL v,
    Lp.coeFn_sub (-J.compLpL 2 averageMeasure v) (c • L.compLpL 2 averageMeasure v),
    Lp.coeFn_neg (J.compLpL 2 averageMeasure v),Lp.coeFn_smul c (L.compLpL 2 averageMeasure v)]
    with lag first second third sub neg smul
  rw [first,sub,Pi.sub_apply,neg,Pi.neg_apply,smul,Pi.smul_apply,second,third,same]

theorem lifted_joint (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) : lifted seed frame M F R v=
      -NativeWindowHistoryCutAction.jointAction seed frame M F R v-nu.coeff • laplacianAction nu M v := by
  simpa only [lifted,NativeWindowHistoryCutAction.jointAction,laplacianAction] using!
    lift_neg_sub (E := wholePhysical) (fiber seed frame M F R) (joint seed frame M F R) (laplacianFiber nu M)
      nu.coeff (fiber_joint seed frame M F R) v

def energy (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (finiteHistory seed time M) (lifted seed frame M F R (finiteHistory seed time M))

def rate (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (finiteHistory seed time M) (lifted seed frame M F R
    (action seed M time (finiteHistory seed time M)+forcingHistory seed M time))+
  inner ℝ (action seed M time (finiteHistory seed time M)+forcingHistory seed M time)
    (lifted seed frame M F R (finiteHistory seed time M))

private theorem paired_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) {f : ℝ → E} {d : E} {t : ℝ} (original : HasDerivAt f d t) :
    HasDerivAt (fun s => inner ℝ (f s) (T (f s))) (inner ℝ (f t) (T d)+inner ℝ d (T (f t))) t :=
  original.inner ℝ (T.hasFDerivAt.comp_hasDerivAt t original)

theorem energy_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) :
    HasDerivAt (energy seed frame M F R) (rate seed frame M F R time) time := by
  simpa only [energy,rate] using! paired_derivative (E := H) (lifted seed frame M F R)
    (NativeWindowHistoryOseen.source_hasDerivAt seed M time)

private theorem paired_neg_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) (c : ℝ) : inner ℝ x (-y-c • z)= -inner ℝ x y-c*inner ℝ x z := by
  rw [inner_sub_right,inner_neg_right,real_inner_smul_right]

theorem energy_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) :
    energy seed frame M F R time= -NativeWindowHistoryCutAction.diagonal seed frame M F R time-
      nu.coeff*gradient M (finiteHistory seed time M) := by
  have first := congrArg (fun v : H => inner ℝ (finiteHistory seed time M) v)
    (lifted_joint seed frame M F R (finiteHistory seed time M))
  have second := paired_neg_sub (E := H) (finiteHistory seed time M)
    (NativeWindowHistoryCutAction.jointAction seed frame M F R (finiteHistory seed time M))
    (laplacianAction nu M (finiteHistory seed time M)) nu.coeff
  have last := congrArg (fun x : ℝ => -NativeWindowHistoryCutAction.diagonal seed frame M F R time-nu.coeff*x)
    (NativeWindowMetricGraphHistory.history_gradient nu M (finiteHistory seed time M))
  exact (first.trans second).trans last

def graphRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  inner ℝ (finiteHistory seed time M) (laplacianAction nu M
    (action seed M time (finiteHistory seed time M)+forcingHistory seed M time))+
  inner ℝ (action seed M time (finiteHistory seed time M)+forcingHistory seed M time)
    (laplacianAction nu M (finiteHistory seed time M))

theorem gradient_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun s => gradient M (finiteHistory seed s M)) (graphRate seed M time) time := by
  simpa only [NativeWindowMetricGraphHistory.history_gradient nu M,graphRate] using!
    paired_derivative (E := H) (laplacianAction nu M) (NativeWindowHistoryOseen.source_hasDerivAt seed M time)

theorem graphRate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (time0 : 0 ≤ time) :
    graphRate seed M time=NativeWindowAugmentedPayment.graphJet seed (modes M) 1 time := by
  have first := (gradient_derivative seed M time).hasDerivWithinAt (s := Ici (0 : ℝ))
  have last := (NativeWindowAugmentedPayment.graphJet_hasDerivAt seed (modes M) 0 time).hasDerivWithinAt (s := Ici (0 : ℝ))
  have actual := last.congr_of_mem (fun s inside => NativeWindowHistoryForcingWork.gradient_original seed M s inside) time0
  have same := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) ((uniqueDiffOn_Ici (0 : ℝ)).eq time0 first actual)
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,one_smul] using same

theorem rate_original (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) (time0 : 0 ≤ time) :
    rate seed frame M F R time= -NativeWindowHistoryCutAction.actual seed frame M F R time-
      nu.coeff*NativeWindowAugmentedPayment.graphJet seed (modes M) 1 time := by
  have derivative := (NativeWindowHistoryCutAction.diagonal_derivative seed frame M F R time).neg.sub
    ((gradient_derivative seed M time).const_mul nu.coeff)
  have source := energy_derivative seed frame M F R time
  have same : energy seed frame M F R=(fun t => -NativeWindowHistoryCutAction.diagonal seed frame M F R t-
    nu.coeff*gradient M (finiteHistory seed t M)) := funext (energy_original seed frame M F R)
  rw [same] at source
  have actual := source.unique derivative
  simpa only [graphRate_original seed M time time0] using actual

theorem rate_physical (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) (time0 : 0 ≤ time)
    (cover : ∀ k∈F,k≠0 →k∈modes M) :
    rate seed frame M F R time= -NativeWindowTraceCutActionPhysical.matrix seed frame time F R 1 := by
  rw [rate_original seed frame M F R time time0,NativeWindowHistoryCutAction.actual_original,
    NativeWindowTraceCutActionPhysical.pair_window_physical seed frame time time0 M F R 1 cover]
  ring

theorem source_rate_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ R≥low,∀ cutoff≥low,∀ M,
      ∀ frame∈Icc 0 horizon,∀ time∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
      |rate seed frame M (integerWaveFrequencyCube cutoff) R time| ≤ C := by
  obtain ⟨low,C,C0,source⟩ := NativeWindowHistoryCutAction.source_uniform seed horizon nonnegative
  let B:=|NativeWindowAugmentedPayment.graphBudget seed 1 horizon|
  refine ⟨low,C+nu.coeff*B,by dsimp only [B]; positivity [nu.coeff_pos],
    fun R above cutoff covered M frame frameInside time timeInside cover => ?_⟩
  rw [rate_original seed frame M _ R time timeInside.1]
  have one := source R above cutoff covered M frame frameInside time timeInside cover
  have two := (NativeWindowAugmentedPayment.graphJet_bound seed (modes M) 1 time horizon timeInside).trans
    (le_abs_self _)
  have one' : |NativeWindowHistoryCutAction.actual seed frame M (integerWaveFrequencyCube cutoff) R time|≤C := by
    simpa only [Real.norm_eq_abs] using one
  have two' : |NativeWindowAugmentedPayment.graphJet seed (modes M) 1 time|≤B := by
    simpa only [Real.norm_eq_abs] using two
  have normed := abs_sub (-NativeWindowHistoryCutAction.actual seed frame M (integerWaveFrequencyCube cutoff) R time)
    (nu.coeff*NativeWindowAugmentedPayment.graphJet seed (modes M) 1 time)
  simp only [abs_neg,abs_mul,abs_of_nonneg nu.coeff_pos.le] at normed
  exact normed.trans (add_le_add one' (mul_le_mul_of_nonneg_left two' nu.coeff_pos.le))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem lifted_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (frame : ℝ) (frame0 : 0≤frame) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    lifted seed (step.2.clockAdvance+frame) M F R=lifted step.1 frame M F R := by
  simp only [lifted,fiber,NativeWindowTraceCutTime.fieldJet_next seed F R 0 step generated frame frame0]

theorem source_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (frame time : ℝ) (frame0 : 0≤frame) (time0 : 0≤time) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    (energy seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time),
      rate seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time))=
      (energy step.1 frame M F R time,rate step.1 frame M F R time) := by
  have operators:=NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  simp only [energy,rate,operators.1,lifted_next seed step generated frame frame0,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPotentialAction
