import H0mework.Versions.X.NavierStokes.HigherTreeOctic.TemporalResponse

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticTemporalResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeResolventCompactness NativeUnheatedTreeTime NativeUnheatedGlobalNegativeOne
open NativeUnheatedSourceGradient NativeUnheatedIntegralBilinear
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def responseRate (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (time : ℝ) : ℂ :=
  bilinear (nu := nu) nodes leaf p q (rate seed time) (state seed time)+
    bilinear (nu := nu) nodes leaf p q (state seed time) (rate seed time)

def responseConstant (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  6*(2*nu.coeff)⁻¹*NativeUnifiedCompleteSource.budget seed

theorem responseConstant_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ responseConstant seed := by
  have paid := NativeUnheatedSourceWeightedTail.state_bound seed 0
  unfold responseConstant
  positivity [nu.coeff_pos, (norm_nonneg _).trans paid]

theorem responseRate_bound (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (time : ℝ) :
    ‖responseRate seed nodes leaf p q time‖ ≤ responseConstant seed*‖rate seed time‖ := by
  have source := NativeUnheatedSourceWeightedTail.state_bound seed time
  have first := (bilinear_bound nodes leaf p q (rate seed time) (state seed time)).trans
    (mul_le_mul_of_nonneg_left source (by positivity [nu.coeff_pos]))
  have last := (bilinear_bound nodes leaf p q (state seed time) (rate seed time)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left source (by positivity [nu.coeff_pos])) (norm_nonneg _))
  exact (norm_add_le _ _).trans ((add_le_add first last).trans_eq (by unfold responseConstant; ring))

theorem response_bound (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (time : ℝ) :
    ‖response seed nodes leaf p q time‖ ≤ (3*(2*nu.coeff)⁻¹)*NativeUnifiedCompleteSource.budget seed^2 := by
  have source := NativeUnheatedSourceWeightedTail.state_bound seed time
  apply (bilinear_bound nodes leaf p q (state seed time) (state seed time)).trans
  have product := mul_le_mul source source (norm_nonneg _) ((norm_nonneg _).trans source)
  calc
    _ = (3*(2*nu.coeff)⁻¹)*(‖state seed time‖*‖state seed time‖) := by ring
    _ ≤ (3*(2*nu.coeff)⁻¹)*(NativeUnifiedCompleteSource.budget seed*NativeUnifiedCompleteSource.budget seed) :=
      mul_le_mul_of_nonneg_left product (by positivity [nu.coeff_pos])
    _ = _ := by ring

theorem responseRate_integrable (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (responseRate seed nodes leaf p q) (volume.restrict (Icc 0 horizon)) := by
  have field := ((state_continuousOn seed).mono (Icc_subset_Ici_self : Icc 0 horizon ⊆ Ici 0)).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have rateMeas := (rate_measurable seed).restrict (s := Icc 0 horizon)
  let B := bilinear (nu := nu) nodes leaf p q
  have measurable := (B.aestronglyMeasurable_comp₂ rateMeas field).add (B.aestronglyMeasurable_comp₂ field rateMeas)
  exact ((rate_integrable seed horizon nonnegative).norm.const_mul (responseConstant seed)).mono' measurable
    (Eventually.of_forall (responseRate_bound seed nodes leaf p q))

theorem response_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (response seed nodes leaf p q)
      (responseRate seed nodes leaf p q time) time := by
  filter_upwards [source_hasDerivAt_ae seed] with time actual positive
  have generated := ((bilinear (nu := nu) nodes leaf p q).hasFDerivAt.comp_hasDerivAt time (actual positive)).clm_apply (actual positive)
  simpa only [response, responseRate, Function.comp_def] using! generated

theorem response_ac (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    AbsolutelyContinuousOnInterval (response seed nodes leaf p q) first last :=
  diagonal_ac (bilinear (nu := nu) nodes leaf p q) (NativeUnheatedPairGlobalEvolution.state_ac seed first last first0 last0)

theorem response_write (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    response seed nodes leaf p q last-response seed nodes leaf p q first =
      ∫ time in first..last, responseRate seed nodes leaf p q time := by
  have paid : IntegrableOn (responseRate seed nodes leaf p q) (Icc 0 (max first last)) :=
    responseRate_integrable seed nodes leaf p q (max first last) (first0.trans (le_max_left _ _))
  apply integral_of_ac_derivative _ _ (response_ac seed nodes leaf p q first last first0 last0)
    ((paid.mono_set (fun _ inside => ⟨(le_min first0 last0).trans inside.1, inside.2⟩)).intervalIntegrable)
  filter_upwards [response_hasDerivAt_ae seed nodes leaf p q, volume.ae_ne (0 : ℝ)] with time actual nonzero
  intro inside
  exact actual (lt_of_le_of_ne ((le_min first0 last0).trans inside.1) (Ne.symm nonzero))

theorem response_increment (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (first last : ℝ) (first0 : 0 ≤ first) (ordered : first ≤ last) :
    ‖response seed nodes leaf p q last-response seed nodes leaf p q first‖ ≤
      responseConstant seed*(∫ time in first..last, ‖rate seed time‖) := by
  have last0 := first0.trans ordered
  have paid : IntegrableOn (responseRate seed nodes leaf p q) (Icc 0 last) :=
    responseRate_integrable seed nodes leaf p q last last0
  have interval := (paid.mono_set (uIcc_subset_Icc ⟨first0,ordered⟩ ⟨last0,le_rfl⟩)).intervalIntegrable
  rw [response_write seed nodes leaf p q first last first0 last0]
  apply (intervalIntegral.norm_integral_le_integral_norm ordered).trans
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on ordered interval.norm
    ((rate_intervalIntegrable seed first last first0 last0).norm.const_mul _) (fun time _ => responseRate_bound seed nodes leaf p q time)

theorem response_next (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    response seed nodes leaf p q (step.2.clockAdvance+time) = response step.1 nodes leaf p q time := by
  simp only [response, state_next seed step generated time nonnegative]

def variation (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ :=
  ∫ actual in 0..time, ‖rate seed actual‖

theorem variation_continuous (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ContinuousOn (variation seed) (Icc 0 horizon) := by
  change ContinuousOn (fun time => ∫ actual in 0..time, ‖rate seed actual‖) (Icc 0 horizon)
  simpa only [uIcc_of_le nonnegative] using intervalIntegral.continuousOn_primitive_interval'
    (rate_intervalIntegrable seed 0 horizon le_rfl nonnegative).norm left_mem_uIcc

theorem variation_increment (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    variation seed last-variation seed first = ∫ time in first..last, ‖rate seed time‖ :=
  intervalIntegral.integral_interval_sub_left
    (rate_intervalIntegrable seed 0 last le_rfl last0).norm (rate_intervalIntegrable seed 0 first le_rfl first0).norm

theorem variation_range (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time ∈ Icc 0 horizon) : 0 ≤ variation seed time ∧ variation seed time ≤ variation seed horizon := by
  refine ⟨intervalIntegral.integral_nonneg_of_forall inside.1 (fun _ => norm_nonneg _), ?_⟩
  have positive := intervalIntegral.integral_nonneg_of_forall (μ := volume) inside.2 (fun actual => norm_nonneg (rate seed actual))
  rw [← variation_increment seed time horizon inside.1 (inside.1.trans inside.2)] at positive
  linarith

theorem variation_source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    variation seed horizon ≤ NativeNegativeOneMomentum.coefficient nu*
      (horizon+NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon) := by
  have action := (rate_integrable seed horizon nonnegative).norm
  have gradient := mass_integrable seed horizon nonnegative
  have positive := NativeNegativeOneMomentum.coefficient_nonnegative nu
  have upper := integral_mono_ae action (((integrable_const 1).add gradient).const_mul (NativeNegativeOneMomentum.coefficient nu))
    (Eventually.of_forall (rate_bound seed))
  have convertIntegral : (∫ time in Icc 0 horizon, ‖rate seed time‖) = variation seed horizon := by
    rw [variation, intervalIntegral.integral_of_le nonnegative, integral_Icc_eq_integral_Ioc]
  rw [convertIntegral, integral_const_mul] at upper
  simp only [Pi.add_apply] at upper
  rw [integral_add (integrable_const 1) gradient] at upper
  have length : (∫ _ : ℝ in Icc 0 horizon, (1 : ℝ)) = horizon := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le nonnegative, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, mul_one]
  rw [length] at upper
  exact upper.trans (mul_le_mul_of_nonneg_left (by linarith [mass_integral_bound seed horizon nonnegative]) positive)

theorem responseRate_integral_bound (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, ‖responseRate seed nodes leaf p q time‖) ≤
      responseConstant seed*NativeNegativeOneMomentum.coefficient nu*
        (horizon+NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon) := by
  have upper := integral_mono_ae (responseRate_integrable seed nodes leaf p q horizon nonnegative).norm
    ((rate_integrable seed horizon nonnegative).norm.const_mul (responseConstant seed))
    (Eventually.of_forall (responseRate_bound seed nodes leaf p q))
  have actual : (∫ time in Icc 0 horizon, ‖rate seed time‖) = variation seed horizon := by
    rw [variation, intervalIntegral.integral_of_le nonnegative, integral_Icc_eq_integral_Ioc]
  rw [integral_const_mul, actual] at upper
  exact upper.trans ((mul_le_mul_of_nonneg_left (variation_source_bound seed horizon nonnegative)
    (responseConstant_nonnegative seed)).trans_eq (by ring))

def correlation (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ) : ℝ :=
  ∫ time in Icc 0 horizon, mass seed time*(variation seed (time+shift)-variation seed time)

theorem correlation_original (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ) (positive : 0 ≤ shift) :
    correlation seed horizon shift =
      ∫ time in Icc 0 horizon, mass seed time*(∫ actual in time..(time+shift), ‖rate seed actual‖) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro time inside
  dsimp only
  rw [variation_increment seed time (time+shift) inside.1 (add_nonneg inside.1 positive)]

theorem increment_continuous (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ)
    (nonnegative : 0 ≤ horizon) (positive : 0 ≤ shift) :
    ContinuousOn (fun time => variation seed (time+shift)-variation seed time) (Icc 0 horizon) := by
  have whole := variation_continuous seed (horizon+shift) (add_nonneg nonnegative positive)
  exact (whole.comp (continuousOn_id.add continuousOn_const) (fun time inside =>
    ⟨add_nonneg inside.1 positive, by dsimp; linarith [inside.2]⟩)).sub
      (whole.mono (fun time inside => ⟨inside.1, by linarith [inside.2]⟩))

theorem increment_range (seed : GeneratedWholeRestartCurrent nu) (horizon shift time : ℝ)
    (positive : 0 ≤ shift) (inside : time ∈ Icc 0 horizon) :
    0 ≤ variation seed (time+shift)-variation seed time ∧
      variation seed (time+shift)-variation seed time ≤ variation seed (horizon+shift) := by
  have first := variation_range seed (horizon+shift) time ⟨inside.1, by linarith [inside.2]⟩
  have last := variation_range seed (horizon+shift) (time+shift)
    ⟨add_nonneg inside.1 positive, by linarith [inside.2]⟩
  refine ⟨?_, by linarith⟩
  rw [variation_increment seed time (time+shift) inside.1 (add_nonneg inside.1 positive)]
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => norm_nonneg _)

theorem correlation_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ)
    (nonnegative : 0 ≤ horizon) (positive : 0 ≤ shift) :
    IntegrableOn (fun time => mass seed time*(variation seed (time+shift)-variation seed time)) (Icc 0 horizon) :=
  IntegrableOn.mul_continuousOn (mass_integrable seed horizon nonnegative)
    (increment_continuous seed horizon shift nonnegative positive) isCompact_Icc

theorem correlation_bound (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ)
    (nonnegative : 0 ≤ horizon) (positive : 0 ≤ shift) :
    0 ≤ correlation seed horizon shift ∧ correlation seed horizon shift ≤
      variation seed (horizon+shift)*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  have upper := integral_mono_ae (correlation_integrable seed horizon shift nonnegative positive)
    ((mass_integrable seed horizon nonnegative).mul_const (variation seed (horizon+shift))) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
      exact mul_le_mul_of_nonneg_left (increment_range seed horizon shift time positive inside).2 (mass_nonnegative seed time))
  rw [integral_mul_const] at upper
  refine ⟨setIntegral_nonneg measurableSet_Icc (fun time inside =>
    mul_nonneg (mass_nonnegative seed time) (increment_range seed horizon shift time positive inside).1), ?_⟩
  exact upper.trans ((mul_le_mul_of_nonneg_right (mass_integral_bound seed horizon nonnegative)
    (variation_range seed (horizon+shift) (horizon+shift) ⟨add_nonneg nonnegative positive,le_rfl⟩).1).trans_eq (by ring))

theorem weighted_response_increment (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (horizon shift : ℝ) (nonnegative : 0 ≤ horizon) (positive : 0 ≤ shift) :
    (∫ time in Icc 0 horizon, mass seed time*‖response seed nodes leaf p q (time+shift)-response seed nodes leaf p q time‖) ≤
      responseConstant seed*correlation seed horizon shift := by
  have whole := (response_ac seed nodes leaf p q 0 (horizon+shift) le_rfl (add_nonneg nonnegative positive)).continuousOn
  rw [uIcc_of_le (add_nonneg nonnegative positive)] at whole
  have continuous := ((whole.comp (continuousOn_id.add continuousOn_const) (fun time (inside : time ∈ Icc 0 horizon) =>
    ⟨add_nonneg inside.1 positive, by dsimp; linarith [inside.2]⟩)).sub
      (whole.mono (fun time (inside : time ∈ Icc 0 horizon) => ⟨inside.1,by linarith [inside.2]⟩))).norm
  have integrable := IntegrableOn.mul_continuousOn (mass_integrable seed horizon nonnegative) continuous isCompact_Icc
  have upper := integral_mono_ae integrable ((correlation_integrable seed horizon shift nonnegative positive).const_mul (responseConstant seed)) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
    have paid := response_increment seed nodes leaf p q time (time+shift) inside.1 (by linarith)
    rw [← variation_increment seed time (time+shift) inside.1 (add_nonneg inside.1 positive)] at paid
    exact (mul_le_mul_of_nonneg_left paid (mass_nonnegative seed time)).trans_eq (by ring))
  simpa only [integral_const_mul, correlation, Function.comp_def, Pi.sub_apply, Pi.add_apply, id_eq] using! upper

theorem correlation_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (correlation seed horizon) (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) := by
  let whole := horizon+1
  have whole0 : 0 ≤ whole := by dsimp [whole]; linarith
  have shifts : ∀ᶠ shift : ℝ in 𝓝[Ici (0 : ℝ)] 0, shift ∈ Icc 0 1 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with shift lower upper
    exact ⟨lower,upper.le⟩
  have dominating := (mass_integrable seed horizon nonnegative).mul_const (variation seed whole)
  have convergence := tendsto_integral_filter_of_dominated_convergence
    (fun time => mass seed time*variation seed whole)
    (shifts.mono fun shift inside => (correlation_integrable seed horizon shift nonnegative inside.1).aestronglyMeasurable)
    (shifts.mono fun shift inside => by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with time actual
      have range := increment_range seed horizon shift time inside.1 actual
      have final := (variation_range seed whole (horizon+shift)
        ⟨add_nonneg nonnegative inside.1, by dsimp [whole]; linarith [inside.2]⟩).2
      rw [Real.norm_of_nonneg (mul_nonneg (mass_nonnegative seed time) range.1)]
      exact mul_le_mul_of_nonneg_left (range.2.trans final) (mass_nonnegative seed time))
    dominating (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with time actual
      have shifted : Tendsto (fun shift : ℝ => time+shift) (𝓝[Ici (0 : ℝ)] 0) (𝓝[Icc 0 whole] time) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨?_, shifts.mono fun shift inside => ⟨add_nonneg actual.1 inside.1, ?_⟩⟩
        · have argument : Tendsto (fun shift : ℝ => shift) (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) :=
            (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
          simpa only [add_zero] using (tendsto_const_nhds (x := time)).add argument
        · dsimp [whole]; linarith [actual.2, inside.2]
      have atTime : Tendsto (variation seed) (𝓝[Icc 0 whole] time) (𝓝 (variation seed time)) :=
        variation_continuous seed whole whole0 time ⟨actual.1, by dsimp [whole]; linarith [actual.2]⟩
      have point := atTime.comp shifted
      simpa only [sub_self, mul_zero, Function.comp_def] using! (tendsto_const_nhds (x := mass seed time)).mul (point.sub_const (variation seed time)))
  simpa only [correlation, integral_zero] using! convergence

theorem weighted_response_tendsto (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun shift => ∫ time in Icc 0 horizon,
      mass seed time*‖response seed nodes leaf p q (time+shift)-response seed nodes leaf p q time‖)
      (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) := by
  have positive : ∀ᶠ shift : ℝ in 𝓝[Ici (0 : ℝ)] 0, 0 ≤ shift := self_mem_nhdsWithin
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun time => mul_nonneg (mass_nonnegative seed time) (norm_nonneg _))))
    (positive.mono (fun shift after => weighted_response_increment seed nodes leaf p q horizon shift nonnegative after))
  simpa only [mul_zero] using (correlation_tendsto seed horizon nonnegative).const_mul (responseConstant seed)

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticTemporalResponse
