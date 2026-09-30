import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorAction
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Synthesis

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurTranspose
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalFourier
open NativeWindowHistoryOseen (H)
open NativeWindowHistorySchurAdvectorFiber (family xProfile)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowHistoryCreationGeometry (transport square gradientSquare)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowHistoryAnnihilationControl (laplacianAction graphCost)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def transposeAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (family nu M).flip.holderL averageMeasure ∞ 2 2 (xProfile seed M time)

theorem transpose_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : H) :
    transposeAction seed M time u=ᵐ[averageMeasure] fun lag => family nu M (u lag) (completion seed M time lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (family nu M).flip (xProfile seed M time) u,NativeWindowHistorySchurAdvectorFiber.xProfile_ae seed M time]
    with lag applied source
  change transposeAction seed M time u lag=family nu M (u lag) (xProfile seed M time lag) at applied
  rw [applied,source]

theorem finite_bound (nu : Viscosity) (M : ℕ) (u x : physicalSpace (modes M)) :
    ‖coefficients (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu u x)‖^2 ≤
      (∑ i : Coordinate,‖evaluate (modes M) (modes M) i u‖^2)*curlPair (modes M) x.1 x.1 := by
  apply (NativeWindowHistoryCreationGeometry.transport_bound (modes M) (modes_zero M) (modes_closed M) nu u x).trans
  have paid:=integral_mono_of_nonneg (Eventually.of_forall fun point => mul_nonneg
    (show 0 ≤ square (modes M) u point by
      simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ x point))
    ((continuous_const.mul (gradientSquare (modes M) (modes_zero M) (modes_closed M) x).continuous).integrable_of_hasCompactSupport (μ := volume)
      (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall fun point => mul_le_mul_of_nonneg_right
      (show square (modes M) u point ≤ ∑ i : Coordinate,‖evaluate (modes M) (modes M) i u‖^2 by
        simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
        apply Finset.sum_le_sum
        intro i _
        simpa only [← pow_two,Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg ((evaluate (modes M) (modes M) i u) point))
          ((evaluate (modes M) (modes M) i u).norm_coe_le_norm point) 2)
      (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ x point))
  exact paid.trans_eq (by simp only [Pi.mul_apply]; rw [integral_const_mul,NativeWindowHistorySchurWeakPairing.gradient_integral])

theorem exists_finite_bound (nu : Viscosity) (B : ℝ) (B0 : 0 ≤ B) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ u x : physicalSpace (modes M),curlPair (modes M) x.1 x.1 ≤ B →
      ‖coefficients (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu u x)‖^2 ≤
        epsilon*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖^2+
          C*‖coefficients (modes M) u‖^2 := by
  let delta:=Real.sqrt (epsilon/(6*(B+1)))
  have denominator:0 < 6*(B+1):=by linarith
  have delta0:0 < delta:=Real.sqrt_pos.mpr (div_pos positive denominator)
  have deltaSquare:delta^2*(6*(B+1))=epsilon := by
    rw [show delta^2=epsilon/(6*(B+1)) from Real.sq_sqrt (div_nonneg positive.le denominator.le)]
    exact div_mul_cancel₀ _ denominator.ne'
  have small:6*B*delta^2 ≤ epsilon := by nlinarith only [deltaSquare,sq_nonneg delta]
  obtain ⟨K,K0,point⟩:=NativeWindowMetricGraphSynthesis.exists_evaluate_bound nu delta delta0
  refine ⟨6*B*K^2,by positivity,fun M u x bounded => ?_⟩
  let L:=‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖
  let U:=‖coefficients (modes M) u‖
  have row (i : Coordinate) : ‖evaluate (modes M) (modes M) i u‖^2 ≤ 2*delta^2*L^2+2*K^2*U^2 := by
    have bound:=pow_le_pow_left₀ (norm_nonneg _) (point (modes M) (modes M) (modes_zero M) (modes_closed M) u i) 2
    change _ ≤ (delta*L+K*U)^2 at bound
    nlinarith only [bound,sq_nonneg (delta*L-K*U)]
  have sum: (∑ i : Coordinate,‖evaluate (modes M) (modes M) i u‖^2) ≤ 6*delta^2*L^2+6*K^2*U^2 :=
    (Finset.sum_le_sum fun i _ => row i).trans_eq (by simp only [Fin.sum_univ_three]; ring)
  have paid:=(finite_bound nu M u x).trans (mul_le_mul sum bounded
    (NativeWindowHistorySchurSampleControl.gradient_nonnegative M x) (by positivity))
  have absorbed:=mul_le_mul_of_nonneg_right small (sq_nonneg L)
  nlinarith only [paid,absorbed]

theorem input_norm (M : ℕ) (u : wholePhysical) :
    ‖coefficients (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)‖ ≤ ‖u‖ := by
  have bound:‖NativeWindowTraceWholeHistory.projection M u‖ ≤ ‖u‖ := by
    change ‖(NativeWindowTraceWholeHistory.projection M u).1‖ ≤ ‖u.1‖
    exact (congrArg (fun v : NativeResolventCompactness.State => ‖v‖)
      (NativeWindowHistoryMeanTime.projection_read M u)).trans_le (NativeWindowHistoryMeanTime.read_bound M u.1)
  simpa only [] using! (include_norm (modes M) (modes_zero M) (modes_closed M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)).symm.trans_le bound

theorem source_finite_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ∀ᵐ lag ∂averageMeasure,∀ u : physicalSpace (modes M),
        ‖coefficients (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu u
          (NativeWindowHistorySchurSampleControl.sample seed M time lag))‖^2 ≤
          epsilon*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖^2+
            C*‖coefficients (modes M) u‖^2 := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowHistorySchurSampleControl.source_sample_bound seed horizon nonnegative
  obtain ⟨C,C0,point⟩:=exists_finite_bound nu (B/nu.coeff) (div_nonneg B0 nu.coeff_pos.le) epsilon positive
  refine ⟨low,C,C0,fun M above time inside => ?_⟩
  filter_upwards [source M above time inside] with lag bound
  intro u
  have grad:curlPair (modes M) (NativeWindowHistorySchurSampleControl.sample seed M time lag).1
      (NativeWindowHistorySchurSampleControl.sample seed M time lag).1 ≤ B/nu.coeff := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    have mass0:=real_inner_self_nonneg (x := coefficients (modes M) (NativeWindowHistorySchurSampleControl.sample seed M time lag))
    change 0 ≤ pairing (modes M) _ _ at mass0
    unfold NativeWindowHistorySchurSampleControl.sampleEnergy at bound
    nlinarith only [bound,mass0]
  exact point M u _ grad

theorem source_point_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,∀ u : H,
      ∀ᵐ lag ∂averageMeasure,‖transposeAction seed M time u lag‖^2 ≤
        epsilon*graphCost nu M u lag+C*‖u lag‖^2 := by
  obtain ⟨low,C,C0,point⟩:=source_finite_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above time inside u => ?_⟩
  filter_upwards [transpose_ae seed M time u,point M above time inside] with lag original bound
  rw [original,NativeWindowHistorySchurAdvectorFiber.family_original,include_norm (modes M) (modes_zero M)]
  have first:=bound (NativeWindowHistoryAnnihilationRows.input M u lag)
  have lower:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (input_norm M (u lag)) 2) C0
  have graph : ‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M)
      (modes_zero M) (modes_closed M) nu (NativeWindowHistoryAnnihilationRows.input M u lag))‖^2=
      graphCost nu M u lag :=
    (real_inner_self_eq_norm_sq (coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M)
      (modes_zero M) (modes_closed M) nu (NativeWindowHistoryAnnihilationRows.input M u lag)))).symm
  exact first.trans (add_le_add (congrArg (epsilon*·) graph).le lower)

theorem source_graph_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,∀ u : H,
      ‖transposeAction seed M time u‖^2 ≤ epsilon*‖laplacianAction nu M u‖^2+C*‖u‖^2 := by
  obtain ⟨low,C,C0,point⟩:=source_point_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above time inside u => ?_⟩
  have leftPaid:=((Lp.memLp (transposeAction seed M time u)).integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have massPaid:=((Lp.memLp u).integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have graphPaid:=NativeWindowHistoryAnnihilationControl.graph_integrable nu M u
  have paid:=integral_mono_ae leftPaid ((graphPaid.const_mul epsilon).add (massPaid.const_mul C)) (point M above time inside u)
  have graphRead : (∫ lag,epsilon*graphCost nu M u lag ∂averageMeasure)=epsilon*‖laplacianAction nu M u‖^2 :=
    (integral_const_mul epsilon (graphCost nu M u)).trans
      (congrArg (epsilon*·) (NativeWindowHistoryAnnihilationControl.laplacian_square nu M u).symm)
  have massRead : (∫ lag,C*‖u lag‖^2 ∂averageMeasure)=C*‖u‖^2 :=
    (integral_const_mul C (fun lag => ‖u lag‖^2)).trans
      (congrArg (C*·) (NativeWindowTraceWholeHistory.norm_square u).symm)
  have sumRead := (integral_add (graphPaid.const_mul epsilon) (massPaid.const_mul C)).trans
    (congrArg₂ (fun x y : ℝ => x+y) graphRead massRead)
  exact (NativeWindowTraceWholeHistory.norm_square (transposeAction seed M time u)).trans_le
    (paid.trans_eq sumRead)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem transpose_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    transposeAction seed M (step.2.clockAdvance+time)=transposeAction step.1 M time := by
  have same:=congrArg Prod.fst (NativeWindowHistorySchurAdvectorFiber.profiles_next seed M step generated time nonnegative)
  exact congrArg ((family nu M).flip.holderL averageMeasure ∞ 2 2) same

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurTranspose
