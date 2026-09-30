import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Source
import H0mework.Versions.X.NavierStokes.WindowHistoryAnnihilation.Control
import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffOperatorInverse

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint NativeWindowOperatorGreen NativeWholeH1Mixed
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner include_norm restrict_include)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (metric metricAction projection)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem projection_norm (M : ℕ) (v : wholePhysical) : ‖projection M v‖ ≤ ‖v‖ := by
  have read : inner ℝ (projection M v) v=‖projection M v‖^2 := by
    rw [projection,ContinuousLinearMap.comp_apply,include_inner _ (modes_zero M)]
    exact (NativeWindowTraceWholeHistory.projection_square M v).symm
  have bound := real_inner_le_norm (projection M v) v
  rw [read] at bound
  by_cases zero : ‖projection M v‖=0
  · rw [zero]; exact norm_nonneg v
  · have positive : 0 < ‖projection M v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    nlinarith only [bound,positive]

theorem restricted_norm (M : ℕ) (v : wholePhysical) :
    ‖coefficients (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)‖ ≤ ‖v‖ := by
  have source := projection_norm M v
  simpa only [projection,ContinuousLinearMap.comp_apply,include_norm (modes M) (modes_zero M)] using source

theorem metric_pairing (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (x y : wholePhysical) :
    inner ℝ x (metric seed frame M F R y)=pairing (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) x)
      (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) y)) := by
  rw [NativeWindowTraceWholeHistory.metric_original,real_inner_comm,include_inner _ (modes_zero M),pairing_symmetric]

theorem metric_symmetric (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (x y : wholePhysical) :
    inner ℝ (metric seed frame M F R x) y=inner ℝ x (metric seed frame M F R y) := by
  rw [real_inner_comm,metric_pairing,metric_pairing]
  exact NativeWindowTraceCutInverse.test_symmetric seed frame (modes M) F R _ _

theorem metric_adjoint (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) : (metric seed frame M F R).adjoint=metric seed frame M F R := by
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (metric_symmetric seed frame M F R)).adjoint_eq

theorem action_symmetric (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (x y : H) :
    inner ℝ (metricAction seed frame M F R x) y=inner ℝ x (metricAction seed frame M F R y) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(metric seed frame M F R).coeFn_compLpL x,(metric seed frame M F R).coeFn_compLpL y]
    with lag first last
  change inner ℝ (((metric seed frame M F R).compLpL 2 averageMeasure x) lag) (y lag)=
    inner ℝ (x lag) (((metric seed frame M F R).compLpL 2 averageMeasure y) lag)
  rw [first,last,metric_symmetric]

theorem laplacian_norm (nu : Viscosity) (M : ℕ) (v : wholePhysical) :
    ‖laplacianFiber nu M v‖=‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))‖ :=
  include_norm (modes M) (modes_zero M) (modes_closed M) _

theorem fiber_gradient (nu : Viscosity) (M : ℕ) (v : wholePhysical) :
    inner ℝ v (laplacianFiber nu M v)=curlPair (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1 := by
  rw [real_inner_comm]
  change inner ℝ (includeCLM (modes M) (modes_closed M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))) v=_
  rw [include_inner _ (modes_zero M),pairing_symmetric,laplacian_pairing]

theorem history_gradient (nu : Viscosity) (M : ℕ) (v : H) :
    inner ℝ v (laplacianAction nu M v)=NativeWindowTraceWholeHistory.gradient M v := by
  rw [L2.inner_def,NativeWindowTraceWholeHistory.gradient]
  apply integral_congr_ae
  filter_upwards [(laplacianFiber nu M).coeFn_compLpL v] with lag actual
  change inner ℝ (v lag) (((laplacianFiber nu M).compLpL 2 averageMeasure v) lag)=_
  rw [actual,fiber_gradient]

theorem gradient_bound (nu : Viscosity) (M : ℕ) (v : H) :
    NativeWindowTraceWholeHistory.gradient M v ≤ ‖v‖*‖laplacianAction nu M v‖ := by
  rw [← history_gradient]
  exact real_inner_le_norm v (laplacianAction nu M v)

private theorem norm_test (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : wholePhysical) :
    ‖metric seed frame M F R v‖=‖coefficients (modes M) (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))‖ := by
  rw [NativeWindowTraceWholeHistory.metric_original,include_norm _ (modes_zero M)]

private theorem mixed_test (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : wholePhysical) :
    inner ℝ (metric seed frame M F R v) (laplacianFiber nu M v)=pairing (modes M)
      (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := by
  rw [NativeWindowTraceWholeHistory.metric_original,include_inner _ (modes_zero M)]
  rw [show restrictCLM (modes M) (modes_zero M) (modes_closed M) (laplacianFiber nu M v)=
    laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) from restrict_include _ _ _ _]

private theorem point_upper (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame : ℝ) (F : Finset IntegerWavevector)
    (R : ℕ) (C : ℝ) (C0 : 0 ≤ C) (v : wholePhysical)
    (paid : ∀ w : physicalSpace (modes M),‖coefficients (modes M) (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R w)‖^2 ≤
      C*(‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu w)‖^2+‖coefficients (modes M) w‖^2)) :
    ‖metric seed frame M F R v‖^2 ≤ C*(‖laplacianFiber nu M v‖^2+‖v‖^2) := by
  let w:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
  have mass := pow_le_pow_left₀ (norm_nonneg (coefficients (modes M) w)) (restricted_norm M v) 2
  have more := mul_le_mul_of_nonneg_left mass C0
  rw [norm_test,laplacian_norm]
  nlinarith only [paid w,more]

private theorem point_heat (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame : ℝ) (F : Finset IntegerWavevector)
    (R : ℕ) (C : ℝ) (C0 : 0 ≤ C) (v : wholePhysical)
    (paid : ∀ w : physicalSpace (modes M),-2*nu.coeff*pairing (modes M)
      (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R w)
        (laplacian (modes M) (modes_zero M) (modes_closed M) nu w) ≤
      -nu.coeff^2*‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu w)‖^2+C*‖coefficients (modes M) w‖^2) :
    -2*nu.coeff*inner ℝ (metric seed frame M F R v) (laplacianFiber nu M v) ≤ -nu.coeff^2*‖laplacianFiber nu M v‖^2+C*‖v‖^2 := by
  let w:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
  have mass := pow_le_pow_left₀ (norm_nonneg (coefficients (modes M) w)) (restricted_norm M v) 2
  have more := mul_le_mul_of_nonneg_left mass C0
  rw [mixed_test,laplacian_norm]
  linarith only [paid w,more]

theorem source_point_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,∀ frame ∈ Icc 0 horizon,∀ v : wholePhysical,
      ‖metric seed frame M (integerWaveFrequencyCube cutoff) radius v‖^2 ≤ C*(‖laplacianFiber nu M v‖^2+‖v‖^2) ∧
      -2*nu.coeff*inner ℝ (metric seed frame M (integerWaveFrequencyCube cutoff) radius v) (laplacianFiber nu M v) ≤
        -nu.coeff^2*‖laplacianFiber nu M v‖^2+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩ := NativeWindowMetricGraphSource.source_graph_bound seed horizon nonnegative
  exact ⟨low,C,C0,fun radius above cutoff covered M frame inside v =>
    ⟨point_upper seed M frame _ radius C C0 v (fun w => (source radius above cutoff covered (modes M) (modes_zero M) (modes_closed M) frame inside w).1),
      point_heat seed M frame _ radius C C0 v (fun w => (source radius above cutoff covered (modes M) (modes_zero M) (modes_closed M) frame inside w).2)⟩⟩

theorem lift_upper (C : ℝ) (T L : wholePhysical →L[ℝ] wholePhysical)
    (bound : ∀ v : wholePhysical,‖T v‖^2 ≤ C*(‖L v‖^2+‖v‖^2)) (v : H) :
    ‖T.compLpL 2 averageMeasure v‖^2 ≤ C*(‖L.compLpL 2 averageMeasure v‖^2+‖v‖^2) := by
  have m := (Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have t := (Lp.memLp (T.compLpL 2 averageMeasure v)).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have l := (Lp.memLp (L.compLpL 2 averageMeasure v)).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have paid := integral_mono_ae t ((l.add m).const_mul C) (by
    filter_upwards [T.coeFn_compLpL v,L.coeFn_compLpL v] with lag first last
    simp only [Pi.add_apply]
    rw [first,last]
    exact bound (v lag))
  have sumRead := integral_add l m
  simp only [Pi.add_apply] at sumRead paid
  rw [integral_const_mul,sumRead] at paid
  simpa only [← NativeWindowTraceWholeHistory.norm_square] using paid

private theorem generic_norm_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Lp E 2 averageMeasure) : ‖v‖^2=∫ lag,‖v lag‖^2 ∂averageMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem integrated_heat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nu C : ℝ) (x y v : Lp E 2 averageMeasure)
    (bound : ∀ᵐ lag ∂averageMeasure,-2*nu*inner ℝ (x lag) (y lag) ≤ -nu^2*‖y lag‖^2+C*‖v lag‖^2) :
    -2*nu*inner ℝ x y ≤ -nu^2*‖y‖^2+C*‖v‖^2 := by
  have m := (Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have l := (Lp.memLp y).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have pair := L2.integrable_inner (𝕜 := ℝ) x y
  have paid := integral_mono_ae (pair.const_mul (-2*nu)) ((l.const_mul (-nu^2)).add (m.const_mul C)) bound
  have sumRead := integral_add (l.const_mul (-nu^2)) (m.const_mul C)
  simp only [Pi.add_apply] at sumRead paid
  rw [sumRead] at paid
  have pairRead := L2.inner_def (𝕜 := ℝ) x y
  simpa only [integral_const_mul,← generic_norm_square,← pairRead] using paid

theorem lift_heat (nu C : ℝ) (T L : wholePhysical →L[ℝ] wholePhysical)
    (bound : ∀ v : wholePhysical,-2*nu*inner ℝ (T v) (L v) ≤ -nu^2*‖L v‖^2+C*‖v‖^2) (v : H) :
    -2*nu*inner ℝ (T.compLpL 2 averageMeasure v) (L.compLpL 2 averageMeasure v) ≤
      -nu^2*‖L.compLpL 2 averageMeasure v‖^2+C*‖v‖^2 := by
  apply integrated_heat (E := wholePhysical) nu C (T.compLpL 2 averageMeasure v) (L.compLpL 2 averageMeasure v) v
  filter_upwards [T.coeFn_compLpL v,L.coeFn_compLpL v] with lag first last
  rw [first,last]
  exact bound (v lag)

theorem source_history_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,∀ frame ∈ Icc 0 horizon,∀ v : H,
      ‖metricAction seed frame M (integerWaveFrequencyCube cutoff) radius v‖^2 ≤ C*(‖laplacianAction nu M v‖^2+‖v‖^2) ∧
      -2*nu.coeff*inner ℝ (metricAction seed frame M (integerWaveFrequencyCube cutoff) radius v) (laplacianAction nu M v) ≤
        -nu.coeff^2*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  have fact := @source_point_bound nu seed horizon nonnegative
  rcases fact with ⟨low,C,C0,source⟩
  exact ⟨low,C,C0,fun radius above cutoff covered M frame inside v =>
    ⟨lift_upper C (metric seed frame M (integerWaveFrequencyCube cutoff) radius) (laplacianFiber nu M)
      (fun x => (source radius above cutoff covered M frame inside x).1) v,
      lift_heat nu.coeff C (metric seed frame M (integerWaveFrequencyCube cutoff) radius) (laplacianFiber nu M)
        (fun x => (source radius above cutoff covered M frame inside x).2) v⟩⟩

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphHistory
