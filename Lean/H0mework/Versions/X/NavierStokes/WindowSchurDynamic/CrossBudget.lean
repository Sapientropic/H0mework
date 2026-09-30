import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.CrossWindow

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCrossBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryHeatDual (energy heatEnergy form heatMap)
open NativeWindowHistoryFrozenInverse (physical)
open NativeWindowHistoryCrossWindow (heat row input value)
noncomputable section
variable {nu : Viscosity}

theorem heat_include (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) :
    heat nu M (includeCLM (modes M) (modes_closed M) v)=
      includeCLM (modes M) (modes_closed M) (heatMap nu M v) := by
  simp only [heat,add_apply,ContinuousLinearMap.id_apply,smul_apply,
    NativeWindowHistoryAnnihilationControl.laplacianFiber,NativeWindowHistoryOseen.lift_included,
    heatMap,LinearMap.add_apply,LinearMap.id_apply,LinearMap.smul_apply,map_add,map_smul]
  rfl

theorem row_physical (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ)
    (f : physicalSpace (modes M)) :
    row seed M sample (includeCLM (modes M) (modes_closed M) f)=
      form nu M (NativeWindowTraceAdjoint.value seed M sample) (physical seed M sample f) := by
  change inner ℝ (NativeWindowHistoryOseen.velocityPath seed M sample)
    (heat nu M (NativeWindowHistoryFrozenInverse.kernel seed M sample (includeCLM (modes M) (modes_closed M) f)))=_
  rw [NativeWindowHistoryHeatWindow.included,heat_include,NativeWindowHistoryOseen.velocityPath,
    include_inner (modes M) (modes_zero M),restrict_include]
  rfl

private theorem product_bound (a b z C : ℝ) (a0 : 0≤a) (b0 : 0≤b)
    (paired : |z|≤Real.sqrt a*Real.sqrt b) (bounded : b≤C) : |z|≤a+C := by
  have square:=sq_nonneg (Real.sqrt a-Real.sqrt b)
  have first:=Real.sq_sqrt a0
  have last:=Real.sq_sqrt b0
  nlinarith only [paired,square,first,last,a0,b0,bounded]

theorem row_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M forceOrder : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (sample : ℝ) :
    |row seed M sample (input seed M forceOrder time)|≤
      energy nu M (NativeWindowTraceAdjoint.value seed M sample)+
      NativeWindowHistoryCommonForceBounds.budget seed horizon forceOrder := by
  let f:=NativeWindowHistoryCommonForceTime.jet seed M forceOrder time
  rw [input,row_physical]
  exact product_bound _ _ _ _ (NativeWindowHistoryHeatDual.energy_nonnegative nu M _)
    (NativeWindowHistoryHeatDual.energy_nonnegative nu M _)
    (NativeWindowHistoryHeatDual.form_bound nu M _ _)
    ((NativeWindowHistoryHeatDual.source_bound seed M sample f).trans
      (NativeWindowHistoryCommonForceBounds.source_bound seed horizon M forceOrder time inside))

def pointEnergy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) : ℝ :=
  energy nu M (NativeWindowTraceAdjoint.value seed M sample)

theorem pointEnergy_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    Continuous (pointEnergy seed M) := by
  have original (sample : ℝ) : pointEnergy seed M sample=
      pairing (modes M) (NativeWindowTraceAdjoint.value seed M sample)
        (heatMap nu M (NativeWindowTraceAdjoint.value seed M sample)) :=
    (NativeWindowHistoryHeatDual.form_self nu M _).symm
  simp only [funext original]
  exact NativeWindowTraceDualWindow.pairing_continuous seed M LinearMap.id (heatMap nu M)

theorem pointEnergy_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ)
    (nonnegative : 0 ≤ sample) :
    pointEnergy seed M sample≤(NativeUnifiedCompleteSource.budget seed)^2+
      nu.coeff*NativeWindowAugmentedPayment.graphSample seed (modes M) sample := by
  have gradient:curlPair (modes M) (NativeWindowTraceAdjoint.value seed M sample).1
      (NativeWindowTraceAdjoint.value seed M sample).1=NativeWindowAugmentedPayment.graphSample seed (modes M) sample :=
    (NativeWindowOperatorGreen.laplacian_pairing (modes M) (modes_zero M) (modes_closed M) nu _ _).symm.trans
      (NativeWindowTraceCutActionPhysical.graph_original seed M sample nonnegative)
  rw [pointEnergy,energy,gradient]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _)
    (NativeWindowTraceAdjoint.value_mass_bound seed M sample nonnegative) 2) le_rfl

def energyBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  (NativeUnifiedCompleteSource.budget seed)^2*(horizon+2)+nu.coeff*(2*Real.pi)^2*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)

theorem source_energy_integral (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) (M : ℕ) :
    (∫sample in 0..horizon+2,pointEnergy seed M sample)≤energyBudget seed horizon := by
  have ordered:0 ≤ horizon+2 := by linarith
  have first:IntervalIntegrable (fun _ : ℝ => (NativeUnifiedCompleteSource.budget seed)^2) volume 0 (horizon+2) :=
    intervalIntegrable_const
  have last:IntervalIntegrable (NativeWindowAugmentedPayment.graphSample seed (modes M)) volume 0 (horizon+2) :=
    (NativeWindowAugmentedPayment.graphSample_continuous seed (modes M)).intervalIntegrable 0 (horizon+2)
  have source:=intervalIntegral.integral_mono_on ordered
    ((pointEnergy_continuous seed M).intervalIntegrable (μ := volume) 0 (horizon+2))
    (first.add (last.const_mul nu.coeff)) (fun sample inside => pointEnergy_bound seed M sample inside.1)
  have graph:=mul_le_mul_of_nonneg_left
    (NativeUnheatedGlobalGradient.source_interval_bound seed 0 (horizon+2) le_rfl ordered
      ((modes M).subtype (fun k => k≠0))) (sq_nonneg (2*Real.pi))
  have graphRead:(∫sample in 0..horizon+2,NativeWindowAugmentedPayment.graphSample seed (modes M) sample)≤
      (2*Real.pi)^2*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2) := by
    simpa only [NativeWindowAugmentedPayment.graphSample,intervalIntegral.integral_const_mul] using graph
  rw [intervalIntegral.integral_add first (last.const_mul nu.coeff),intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,sub_zero,smul_eq_mul] at source
  exact source.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left graphRead nu.coeff_pos.le)).trans_eq (by
    unfold energyBudget
    ring))

theorem source_window_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    (∫sample in time+1..time+2,pointEnergy seed M sample)≤energyBudget seed horizon := by
  have comparison:=intervalIntegral.integral_mono_interval
    (by linarith [inside.1] : 0 ≤ time+1) (by linarith : time+1 ≤ time+2)
    (by linarith [inside.2] : time+2 ≤ horizon+2)
    (Eventually.of_forall fun sample => NativeWindowHistoryHeatDual.energy_nonnegative nu M
      (NativeWindowTraceAdjoint.value seed M sample))
    ((pointEnergy_continuous seed M).intervalIntegrable (μ := volume) 0 (horizon+2))
  exact comparison.trans (source_energy_integral seed horizon (inside.1.trans inside.2) M)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order forceOrder : ℕ) : ℝ :=
  NativeWindowFiniteStressUniform.kernelBound order*
    (energyBudget seed horizon+NativeWindowHistoryCommonForceBounds.budget seed horizon forceOrder)

theorem source_value_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M order forceOrder : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    |value seed M order forceOrder time|≤budget seed horizon order forceOrder := by
  let C:=NativeWindowHistoryCommonForceBounds.budget seed horizon forceOrder
  let K:=NativeWindowFiniteStressUniform.kernelBound order
  have majorant:IntervalIntegrable (fun sample => K*(pointEnergy seed M sample+C)) volume (time+1) (time+2) :=
    (((pointEnergy_continuous seed M).add continuous_const).const_mul K).intervalIntegrable (time+1) (time+2)
  have point:∀ sample : ℝ,
      ‖NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample * row seed M sample (input seed M forceOrder time)‖≤
        K*(pointEnergy seed M sample+C) := by
    intro sample
    rw [norm_mul,Real.norm_eq_abs]
    have first:‖NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample‖≤K := by
      simpa only [NativeUnheatedStressPairEvolution.kernelWeight,zero_add,mul_one] using
        NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)
    exact mul_le_mul first (row_bound seed horizon M forceOrder time inside sample)
      (abs_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive order).le
  have paid:=intervalIntegral.norm_integral_le_of_norm_le (by linarith : time+1≤time+2)
    (Eventually.of_forall fun sample _ => point sample) majorant
  rw [← NativeWindowHistoryCrossWindow.value_interval,Real.norm_eq_abs] at paid
  have original:(∫sample in time+1..time+2,K*(pointEnergy seed M sample+C))=
      K*((∫sample in time+1..time+2,pointEnergy seed M sample)+C) := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      ((pointEnergy_continuous seed M).intervalIntegrable (μ := volume) (time+1) (time+2)) intervalIntegrable_const,
      intervalIntegral.integral_const,show time+2-(time+1)=(1 : ℝ) by ring,one_smul]
  exact paid.trans (original.trans_le (mul_le_mul_of_nonneg_left
    (add_le_add (source_window_energy seed horizon M time inside) le_rfl)
    (NativeWindowFiniteStressUniform.kernelBound_positive order).le))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCrossBudget
