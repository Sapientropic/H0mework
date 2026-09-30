import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CommonResponse

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCommonResponseWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryCommonResponse (response sample transpose nonlinear)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction graphCost)
open NativeWindowHistorySchurTemporalControl (temporalResponse temporalBudget massBudget)
open NativeWindowTraceWholeHistory (projected projection finiteHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem source_transpose_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,∀ u : H,
      ‖transpose seed M order time u‖^2 ≤ epsilon*‖laplacianAction nu M u‖^2+C*‖u‖^2 := by
  obtain ⟨C,C0,point⟩ := NativeWindowHistorySchurTranspose.exists_finite_bound nu
    (NativeWindowHistoryCommonForceBounds.budget seed horizon order/nu.coeff)
    (div_nonneg (NativeWindowHistoryCommonForceBounds.budget_nonnegative seed horizon order) nu.coeff_pos.le) epsilon positive
  refine ⟨C,C0,fun M time inside u => ?_⟩
  have bound : ∀ᵐ lag ∂averageMeasure,‖transpose seed M order time u lag‖^2 ≤
      epsilon*graphCost nu M u lag+C*‖u lag‖^2 := by
    filter_upwards [NativeWindowHistoryCommonResponse.transpose_ae seed M order time u] with lag original
    rw [original,NativeWindowHistorySchurAdvectorFiber.family_original,restrict_include,include_norm (modes M) (modes_zero M)]
    have paid := point M (NativeWindowHistoryAnnihilationRows.input M u lag) (sample seed M order time lag)
      (NativeWindowHistoryCommonResponse.source_sample_gradient seed horizon M order time inside lag)
    have mass := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (NativeWindowHistorySchurTranspose.input_norm M (u lag)) 2) C0
    have graph : ‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (NativeWindowHistoryAnnihilationRows.input M u lag))‖^2=graphCost nu M u lag :=
      (real_inner_self_eq_norm_sq _).symm
    exact paid.trans (add_le_add (congrArg (epsilon*·) graph).le mass)
  have leftPaid := (Lp.memLp (transpose seed M order time u)).integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have massPaid := (Lp.memLp u).integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have graphPaid := NativeWindowHistoryAnnihilationControl.graph_integrable nu M u
  have paid := integral_mono_ae leftPaid ((graphPaid.const_mul epsilon).add (massPaid.const_mul C)) bound
  have graphRead := (integral_const_mul epsilon (graphCost nu M u)).trans
    (congrArg (epsilon*·) (NativeWindowHistoryAnnihilationControl.laplacian_square nu M u).symm)
  have massRead := (integral_const_mul C (fun lag => ‖u lag‖^2)).trans
    (congrArg (C*·) (NativeWindowTraceWholeHistory.norm_square u).symm)
  have sumRead := (integral_add (graphPaid.const_mul epsilon) (massPaid.const_mul C)).trans
    (congrArg₂ (fun a b : ℝ => a+b) graphRead massRead)
  exact (NativeWindowTraceWholeHistory.norm_square (transpose seed M order time u)).trans_le (paid.trans_eq sumRead)

private theorem projection_pairing (M : ℕ) (u v : wholePhysical) : inner ℝ (projection M u) v=inner ℝ u (projection M v) := by
  have first := include_inner (modes M) (modes_zero M) (modes_closed M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) u) v
  have last := include_inner (modes M) (modes_zero M) (modes_closed M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) u
  exact first.trans ((NativeResolventAdjoint.pairing_symmetric (modes M) _ _).trans (last.symm.trans (real_inner_comm _ _)))

private theorem laplacian_pairing (nu : Viscosity) (M : ℕ) (u v : wholePhysical) :
    inner ℝ (laplacianFiber nu M u) v=inner ℝ u (laplacianFiber nu M v) := by
  change inner ℝ (includeCLM (modes M) (modes_closed M)
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) u))) v=_
  rw [include_inner (modes M) (modes_zero M)]
  have first := NativeWindowAugmentedGreen.laplacian_adjoint (nu := nu) (modes M) (modes_zero M) (modes_closed M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) u) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
  have last := include_inner (modes M) (modes_zero M) (modes_closed M)
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) u
  exact first.trans ((NativeResolventAdjoint.pairing_symmetric (modes M) _ _).trans (last.symm.trans (real_inner_comm _ _)))

private theorem lifted_pairing (A : wholePhysical →L[ℝ] wholePhysical)
    (symmetric : ∀ u v,inner ℝ (A u) v=inner ℝ u (A v)) (u v : H) :
    inner ℝ (A.compLpL 2 averageMeasure u) v=inner ℝ u (A.compLpL 2 averageMeasure v) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL u,A.coeFn_compLpL v] with lag first last
  rw [first,last,symmetric]

private theorem symmetric_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P L : E → E) (pSym : ∀ u v,inner ℝ (P u) v=inner ℝ u (P v))
    (lSym : ∀ u v,inner ℝ (L u) v=inner ℝ u (L v)) (c : ℝ) (u v : E) :
    inner ℝ (P u+c • L u) v=inner ℝ u (P v+c • L v) := by
  rw [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,pSym,lSym]

theorem principal_pairing (nu : Viscosity) (M : ℕ) (u v : H) :
    inner ℝ (projected M u+nu.coeff • laplacianAction nu M u) v=
      inner ℝ u (projected M v+nu.coeff • laplacianAction nu M v) := by
  simpa only [] using! symmetric_sum (E := H) (projected M) (laplacianAction nu M)
    (lifted_pairing (projection M) (projection_pairing M))
    (lifted_pairing (laplacianFiber nu M) (laplacian_pairing nu M)) nu.coeff u v

theorem temporal_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : mean (temporalResponse seed M time)=0 := by
  have source := congrArg mean (NativeWindowHistorySchurCompletion.source_split seed M time)
  rw [map_add,NativeWindowHistorySchurCompletion.completion_mean] at source
  exact add_left_cancel (source.symm.trans (add_zero _).symm)

theorem response_heat (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    response seed M order time+nu.coeff • laplacianAction nu M (response seed M order time)=
      embed (includeCLM (modes M) (modes_closed M) (NativeWindowHistoryCommonForceTime.jet seed M order time))+nonlinear seed M order time := by
  have source := NativeWindowHistoryCommonResponse.equation seed M order time
  rw [NativeWindowHistoryCommonResponse.nonlinear_original,neg_smul] at source
  calc
    _=(response seed M order time-(-(nu.coeff • laplacianAction nu M (response seed M order time))+nonlinear seed M order time))+nonlinear seed M order time := by abel
    _=_ := congrArg (fun v : H => v+nonlinear seed M order time) source

def work (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  2*inner ℝ (projected M (temporalResponse seed M time)+nu.coeff • laplacianAction nu M (temporalResponse seed M time))
    (response seed M order time)

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    work seed M order time=2*inner ℝ (temporalResponse seed M time) (nonlinear seed M order time) := by
  have constant : inner ℝ (temporalResponse seed M time)
      (embed (includeCLM (modes M) (modes_closed M) (NativeWindowHistoryCommonForceTime.jet seed M order time)))=0 := by
    rw [real_inner_comm (F := H),NativeWindowHistoryMeanProjection.embed_pairing,temporal_mean,inner_zero_right]
  unfold work
  rw [principal_pairing,NativeWindowHistoryCommonResponse.response_projected,response_heat,
    inner_add_right (𝕜 := ℝ) (temporalResponse seed M time)
      (embed (includeCLM (modes M) (modes_closed M) (NativeWindowHistoryCommonForceTime.jet seed M order time))) (nonlinear seed M order time),constant,zero_add]

private theorem inner_young {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    |2*inner ℝ u v| ≤ ‖u‖^2+‖v‖^2 := by
  have cauchy := abs_real_inner_le_norm u v
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  nlinarith only [cauchy,sq_nonneg (‖u‖-‖v‖)]

private theorem temporal_mass (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) : ‖temporalResponse seed M time‖^2 ≤ temporalBudget seed horizon := by
  have temporal := NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  have gradient0 := NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (temporalResponse seed M time)
  unfold NativeWindowHistorySchurTemporalControl.energy at temporal
  nlinarith only [temporal,mul_nonneg nu.coeff_pos.le gradient0]

theorem source_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M : ℕ,∀ time∈Icc 0 horizon,
      |work seed M order time| ≤ epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  obtain ⟨K,K0,paid⟩ := source_transpose_bound seed horizon order epsilon positive
  refine ⟨temporalBudget seed horizon+K*massBudget seed,
    add_nonneg (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon)
      (mul_nonneg K0 (NativeWindowHistorySchurTemporalControl.massBudget_nonnegative seed)),fun M time inside => ?_⟩
  have nonlinearBound := paid M time inside (finiteHistory seed time M)
  change ‖nonlinear seed M order time‖^2 ≤ _ at nonlinearBound
  have originalMass := NativeWindowHistorySchurTemporalControl.source_mass seed M time inside.1
  have mass := temporal_mass seed horizon M time inside
  have cauchy : |work seed M order time| ≤ ‖temporalResponse seed M time‖^2+‖nonlinear seed M order time‖^2 := by
    rw [work_original]
    simpa only [] using! inner_young (E := H) (temporalResponse seed M time) (nonlinear seed M order time)
  have small := mul_le_mul_of_nonneg_left originalMass K0
  linarith only [cauchy,mass,nonlinearBound,small]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    work seed M order (step.2.clockAdvance+time)=work step.1 M order time :=
  congrArg₂ (fun w y : H => 2*inner ℝ (projected M w+nu.coeff • laplacianAction nu M w) y)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
    (NativeWindowHistoryCommonResponse.response_next seed M order step generated time time0)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCommonResponseWork
