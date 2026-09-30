import H0mework.NavierStokes.WindowHistoryAnnihilation.Rows

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAnnihilationControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativePhysicalFourier NativeCommonAdvectorAction
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWindowHistoryAnnihilationRows (input read gradientRead current averageGradient)
open NativeWindowHistoryCreationGeometry (gradientSquare)
open NativeWindowHistoryCreationCovariance (centered trace)
open NativeWindowStressHeatSource (physical)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem scalar_pair (f g : ℝ → ℝ) (hf : MemLp f 2 averageMeasure) (hg : MemLp g 2 averageMeasure) :
    inner ℝ (hf.toLp f) (hg.toLp g)=∫lag,f lag*g lag ∂averageMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with lag first last
  rw [first,last]
  change g lag*f lag=f lag*g lag
  ring

theorem cauchy_square (f g : ℝ → ℝ) (hf : MemLp f 2 averageMeasure) (hg : MemLp g 2 averageMeasure) :
    (∫lag,f lag*g lag ∂averageMeasure)^2≤(∫lag,(f lag)^2 ∂averageMeasure)*(∫lag,(g lag)^2 ∂averageMeasure) := by
  have first:‖hf.toLp f‖^2=∫lag,(f lag)^2 ∂averageMeasure := by
    rw [← real_inner_self_eq_norm_sq,scalar_pair]
    simp only [pow_two]
  have last:‖hg.toLp g‖^2=∫lag,(g lag)^2 ∂averageMeasure := by
    rw [← real_inner_self_eq_norm_sq,scalar_pair]
    simp only [pow_two]
  have paid:=pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)) 2
  rw [scalar_pair,Real.norm_eq_abs,sq_abs,mul_pow,first,last] at paid
  exact paid

private theorem sum_product (A B : Coordinate → ℝ) (A0 : ∀j,0≤A j) (B0 : ∀j,0≤B j) :
    (∑j,A j*B j)≤(∑j,A j)*(∑j,B j) := by
  calc
    _≤∑j,A j*(∑k,B k) := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun k _ => B0 k) (Finset.mem_univ j)) (A0 j)
    _=_ := (Finset.sum_mul _ _ _).symm

theorem point_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) (point : Torus) :
    (∑ i : Coordinate,(current seed M time r i point)^2)≤3*trace seed M time point*averageGradient M r point := by
  let u:=fun j lag => read M j (centered seed M time (time-lag)) point
  let d:=fun j i lag => gradientRead M j i (input M r lag) point
  have up (j : Coordinate):MemLp (u j) 2 averageMeasure :=
    (NativeWindowHistoryAnnihilationRows.center_read_memLp seed M time j).continuousLinearMap_comp (ContinuousMap.evalCLM ℝ point)
  have dp (j i : Coordinate):MemLp (d j i) 2 averageMeasure :=
    (NativeWindowHistoryAnnihilationRows.gradient_read_memLp M r j i).continuousLinearMap_comp (ContinuousMap.evalCLM ℝ point)
  let A:=fun j => ∫lag,(u j lag)^2 ∂averageMeasure
  let B:=fun j i => ∫lag,(d j i lag)^2 ∂averageMeasure
  have A0 (j : Coordinate):0≤A j := integral_nonneg fun _ => sq_nonneg _
  have B0 (j i : Coordinate):0≤B j i := integral_nonneg fun _ => sq_nonneg _
  have rho:trace seed M time point=∑j,A j := by
    rw [NativeWindowHistoryCreationCovariance.trace_matrix]
    simp only [ContinuousMap.sum_apply,NativeWindowHistoryCreationCovariance.covariance_point]
    apply Finset.sum_congr rfl
    intro j _
    change (∫lag,u j lag*u j lag ∂averageMeasure)=A j
    simp only [A,pow_two]
  have grad:averageGradient M r point=∑i,∑j,B j i := by
    rw [NativeWindowHistoryAnnihilationRows.averageGradient_point]
    have same:(fun lag => gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag) point)=
        fun lag => ∑i,∑j,(d j i lag)^2 := by
      funext lag
      change (∑j : Coordinate,∑i : Coordinate,(d j i lag)*(d j i lag))=_
      rw [Finset.sum_comm]
      simp only [pow_two]
    rw [same,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (dp j i).integrable_sq))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => (dp j i).integrable_sq)
  have row (i : Coordinate):(current seed M time r i point)^2≤3*(∑j,A j)*(∑j,B j i) := by
    let I:=fun j => ∫lag,u j lag*d j i lag ∂averageMeasure
    have actual:current seed M time r i point=-(∑j,I j) := by
      have crossed (j : Coordinate):Integrable (fun lag => u j lag*d j i lag) averageMeasure :=
        (up j).integrable_mul (dp j i)
      rw [NativeWindowHistoryAnnihilationRows.current_point]
      change (∫lag,-(∑j : Coordinate,u j lag*d j i lag) ∂averageMeasure)=_
      rw [integral_neg,integral_finsetSum _ (fun j _ => crossed j)]
    have finite:((∑j,I j)^2)≤3*(∑j,(I j)^2) := by
      simpa only [one_mul,one_pow,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate) (fun _ => (1:ℝ)) I
    have product: (∑j,(I j)^2)≤(∑j,A j)*(∑j,B j i) :=
      (Finset.sum_le_sum fun j _ => cauchy_square (u j) (d j i) (up j) (dp j i)).trans (sum_product A (fun j => B j i) A0 (fun j => B0 j i))
    rw [actual,neg_sq]
    exact (finite.trans (mul_le_mul_of_nonneg_left product (by norm_num))).trans_eq (by ring)
  exact (Finset.sum_le_sum fun i _ => row i).trans_eq (by rw [rho,grad,← Finset.mul_sum])

theorem stress_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time) (r : H) :
    ‖annihilation seed M time r‖^2≤3*(∫point : Torus,NativeWindowTraceGradient.traceStress seed time
      (integerWaveFrequencyCube M) point*averageGradient M r point) := by
  apply (NativeWindowHistoryAnnihilationRows.pressure_bound seed M time r).trans
  simp only [NativeWindowTraceTerminalSynthesis.physical_square]
  have rows (i : Coordinate):Integrable (fun point : Torus => (current seed M time r i point)^2) :=
    ((current seed M time r i).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum Finset.univ (fun i _ => rows i),← integral_const_mul]
  have positive (point : Torus):0≤averageGradient M r point := by
    rw [NativeWindowHistoryAnnihilationRows.averageGradient_point]
    exact integral_nonneg fun _ => NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ _ point
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    ((((NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)).continuous.mul
      (averageGradient M r).continuous).const_mul 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  exact Eventually.of_forall fun point => (point_bound seed M time r point).trans (by
    have bound:=mul_le_mul_of_nonneg_right (NativeWindowHistoryCreationCovariance.trace_le_stress seed M time nonnegative point) (positive point)
    change 3*trace seed M time point*averageGradient M r point≤3*(NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point*averageGradient M r point)
    nlinarith only [bound])

def laplacianFiber (nu : Viscosity) (M : ℕ) : wholePhysical →L[ℝ] wholePhysical :=
  NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu))

def laplacianAction (nu : Viscosity) (M : ℕ) : H →L[ℝ] H := (laplacianFiber nu M).compLpL 2 averageMeasure

def graphCost (nu : Viscosity) (M : ℕ) (r : H) (lag : ℝ) : ℝ :=
  let v:=NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu (input M r lag)
  pairing (modes M) v v

theorem laplacian_point (nu : Viscosity) (M : ℕ) (r : H) :
    ∀ᵐ lag ∂averageMeasure,‖laplacianAction nu M r lag‖^2=graphCost nu M r lag := by
  filter_upwards [(laplacianFiber nu M).coeFn_compLpL r] with lag actual
  change ((laplacianAction nu M r) lag)=_ at actual
  rw [actual]
  change ‖includeCLM (modes M) (modes_closed M)
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu (input M r lag))‖^2=_
  rw [include_norm (modes M) (modes_zero M) (modes_closed M)]
  exact (real_inner_self_eq_norm_sq _).symm

theorem graph_integrable (nu : Viscosity) (M : ℕ) (r : H) : Integrable (graphCost nu M r) averageMeasure :=
  ((Lp.memLp (laplacianAction nu M r)).integrable_norm_pow (by decide : (2:ℕ)≠0)).congr (laplacian_point nu M r)

theorem laplacian_square (nu : Viscosity) (M : ℕ) (r : H) :
    ‖laplacianAction nu M r‖^2=∫lag,graphCost nu M r lag ∂averageMeasure := by
  rw [NativeWindowTraceWholeHistory.norm_square]
  exact integral_congr_ae (laplacian_point nu M r)

private theorem testing_original (f w : C(Torus,ℝ)) :
    ((innerSL ℝ (physical f)).comp physical) w=∫point : Torus,f point*w point := by
  rw [ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatSource.physical_inner]

theorem potential_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    (∫point : Torus,NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M) point*
      gradientSquare (modes M) (modes_zero M) (modes_closed M) v point)≤
    epsilon*pairing (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)+
      NativeWindowHistoryCreationSource.budget seed horizon epsilon*curlPair (modes M) v.1 v.1 := by
  apply (NativeWindowHistoryCreationGeometry.gradient_absorption _ (modes M) (modes_zero M) (modes_closed M) nu v epsilon positive).trans
  have coefficient:=NativeWindowHistoryCreationSource.trace_bound seed M time horizon inside
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left coefficient (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap:NativeWindowHistoryCreationForm.budget
      ‖physical (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M))‖ (epsilon*(2*Real.pi)^2)≤
      NativeWindowHistoryCreationSource.budget seed horizon epsilon :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have gradient0:0≤curlPair (modes M) v.1 v.1 := by
    rw [NativeWindowHistoryCreationGeometry.curl_mass (modes M) (modes_zero M)]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => mul_nonneg (integerWaveNormSq_nonneg k)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right cap gradient0)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) : ℝ :=
  3*NativeWindowHistoryCreationSource.budget seed horizon (epsilon/3)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    0≤budget seed horizon epsilon := mul_nonneg (by norm_num)
      (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon (epsilon/3) (by positivity))

theorem source_annihilation_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) (r : H) :
    ‖annihilation seed M time r‖^2≤epsilon*‖laplacianAction nu M r‖^2+
      budget seed horizon epsilon*NativeWindowTraceWholeHistory.gradient M r := by
  let f:=NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube M)
  let testing:=(innerSL ℝ (physical f)).comp physical
  have integrable:Integrable (fun lag => testing (gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag))) averageMeasure :=
    testing.integrable_comp (NativeWindowHistoryAnnihilationRows.gradient_integrable M r)
  have gradPaid:Integrable (fun lag => curlPair (modes M) (input M r lag).1 (input M r lag).1) averageMeasure :=
    NativeWindowTraceWholeHistory.gradient_integrable nu M r
  have estimate:∀lag,testing (gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag))≤
      (epsilon/3)*graphCost nu M r lag+NativeWindowHistoryCreationSource.budget seed horizon (epsilon/3)*
        curlPair (modes M) (input M r lag).1 (input M r lag).1 := by
    intro lag
    rw [show testing _=∫point : Torus,f point*gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag) point from testing_original _ _]
    exact potential_bound seed horizon (epsilon/3) (by positivity) M time inside _
  have paid:=integral_mono_ae integrable (((graph_integrable nu M r).const_mul (epsilon/3)).add
    (gradPaid.const_mul (NativeWindowHistoryCreationSource.budget seed horizon (epsilon/3)))) (Eventually.of_forall estimate)
  have actual:(∫point : Torus,f point*averageGradient M r point)=
      ∫lag,testing (gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag)) ∂averageMeasure :=
    (testing_original f (averageGradient M r)).symm.trans
      (testing.integral_comp_comm (NativeWindowHistoryAnnihilationRows.gradient_integrable M r)).symm
  have source:=stress_bound seed M time inside.1 r
  change _≤3*(∫point : Torus,f point*averageGradient M r point) at source
  rw [actual] at source
  apply (source.trans (mul_le_mul_of_nonneg_left paid (by norm_num))).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add ((graph_integrable nu M r).const_mul (epsilon/3))
    (gradPaid.const_mul (NativeWindowHistoryCreationSource.budget seed horizon (epsilon/3))),integral_const_mul,integral_const_mul]
  have gradRead:(∫lag,curlPair (modes M) (input M r lag).1 (input M r lag).1 ∂averageMeasure)=
      NativeWindowTraceWholeHistory.gradient M r := rfl
  exact (congrArg₂ (fun x y : ℝ => 3*((epsilon/3)*x+NativeWindowHistoryCreationSource.budget seed horizon (epsilon/3)*y))
    (laplacian_square nu M r).symm gradRead).trans (by unfold budget; ring)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem annihilation_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    annihilation seed M (step.2.clockAdvance+time)=annihilation step.1 M time := by
  have source:=congrArg (fun C : wholePhysical →L[ℝ] H => -(ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := wholePhysical) (F := H) C))
    (NativeWindowHistoryMeanBlocks.creation_next seed M step generated time nonnegative)
  exact (NativeWindowHistoryMeanBlocks.annihilation_adjoint seed M (step.2.clockAdvance+time)).trans
    (source.trans (NativeWindowHistoryMeanBlocks.annihilation_adjoint step.1 M time).symm)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAnnihilationControl
