import H0mework.Versions.Y.Arithmetic.RiemannDivision.DirectRightResolvent

/-! Actual dilation continuity pays the full L² source resolvent. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem schwartzDilation_inner_continuous (left right : SchwartzMap ℝ ℂ) :
    Continuous fun h : ℝ => inner ℂ (left.toLp 2 volume)
      (burnolMultiplicativeDilation h (right.toLp 2 volume)) := by
  let kernel (h x : ℝ) : ℂ := inner ℂ (left x)
    ((Real.exp (h / 2) : ℂ) * right (Real.exp h * x))
  have read (h : ℝ) : inner ℂ (left.toLp 2 volume)
      (burnolMultiplicativeDilation h (right.toLp 2 volume)) = ∫ x : ℝ, kernel h x := by
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x)
        volume volume := by
      simpa only [smul_eq_mul] using
        (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
          (r := Real.exp h) (Real.exp_ne_zero h))
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [left.coeFn_toLp 2 volume,
      burnolMultiplicativeDilation_coeFn h (right.toLp 2 volume),
      qmp.ae (right.coeFn_toLp 2 volume)] with x hl hr hsource
    rw [hl, hr]
    unfold burnolL2RawNormalizedDilation
    rw [hsource]
  simp_rw [read]
  apply continuous_iff_continuousAt.mpr
  intro h₀
  let bound (x : ℝ) : ℝ :=
    (Real.exp ((h₀ + 1) / 2) * (SchwartzMap.seminorm ℝ 0 0) right) * ‖left x‖
  apply continuousAt_of_dominated (bound := bound)
  · exact Filter.Eventually.of_forall fun h =>
      (show Continuous (kernel h) by dsimp only [kernel]; fun_prop).aestronglyMeasurable
  · filter_upwards [Iio_mem_nhds (lt_add_one h₀)] with h hh
    filter_upwards with x
    calc
      ‖kernel h x‖ ≤ ‖left x‖ * ‖(Real.exp (h / 2) : ℂ) * right (Real.exp h * x)‖ :=
        norm_inner_le_norm _ _
      _ = ‖left x‖ * (Real.exp (h / 2) * ‖right (Real.exp h * x)‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ ‖left x‖ * (Real.exp ((h₀ + 1) / 2) *
          (SchwartzMap.seminorm ℝ 0 0) right) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul (Real.exp_le_exp.mpr (by
          have hh' : h < h₀ + 1 := hh
          linarith))
          (SchwartzMap.norm_le_seminorm ℝ right _) (norm_nonneg _)
          (Real.exp_nonneg _)
      _ = bound x := mul_comm _ _
  · exact left.integrable.norm.const_mul _
  · filter_upwards with x
    apply Continuous.continuousAt
    dsimp only [kernel]
    fun_prop

private theorem schwartzDilation_continuous (test : SchwartzMap ℝ ℂ) :
    Continuous fun h : ℝ => burnolMultiplicativeDilation h (test.toLp 2 volume) := by
  apply continuous_iff_continuousAt.mpr
  intro h₀
  let value := test.toLp 2 volume
  let fixed := burnolMultiplicativeDilation h₀ value
  have scalar : Continuous fun h : ℝ =>
      inner ℂ fixed (burnolMultiplicativeDilation h value) := by
    have native := schwartzDilation_inner_continuous
      (coPoissonSchwartzEnergyTranslationEquiv h₀ test) test
    simpa only [← burnolMultiplicativeDilation_schwartz] using native
  have square : Continuous fun h : ℝ => ‖burnolMultiplicativeDilation h value - fixed‖ ^ 2 := by
    have formula (h : ℝ) : ‖burnolMultiplicativeDilation h value - fixed‖ ^ 2 =
        ‖value‖ ^ 2 - 2 * (inner ℂ fixed (burnolMultiplicativeDilation h value)).re +
          ‖fixed‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), (burnolMultiplicativeDilation h).norm_map,
        inner_re_symm]
      rfl
    simp_rw [formula]
    exact (continuous_const.sub ((Complex.continuous_re.comp scalar).const_mul 2)).add
      continuous_const
  have limit : Tendsto (fun h : ℝ => ‖burnolMultiplicativeDilation h value - fixed‖ ^ 2)
      (𝓝 h₀) (𝓝 0) := by
    simpa only [fixed, sub_self, norm_zero, zero_pow (by decide : (2 : Nat) ≠ 0)] using
      square.continuousAt.tendsto (x := h₀)
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  have small := limit.eventually (Iio_mem_nhds (sq_pos_of_pos positive))
  filter_upwards [small] with h hh
  rw [dist_eq_norm]
  change ‖burnolMultiplicativeDilation h value - fixed‖ ^ 2 < ε ^ 2 at hh
  change ‖burnolMultiplicativeDilation h value - fixed‖ < ε
  nlinarith [norm_nonneg (burnolMultiplicativeDilation h value - fixed)]

private theorem isometryFamily_continuous
    (action : ℝ → BurnolL2 ≃ₗᵢ[ℂ] BurnolL2)
    (sourceContinuous : ∀ test : SchwartzMap ℝ ℂ,
      Continuous fun h : ℝ => action h (test.toLp 2 volume)) (value : BurnolL2) :
    Continuous fun h : ℝ => action h value := by
  have dense : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ))) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num : (2 : ENNReal) ≠ ⊤)
  have joint : Continuous fun pair : ℝ × BurnolL2 =>
      action pair.1 pair.2 := by
    apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1 dense
    · intro h
      exact (action h).isometry.lipschitz
    · rintro _ ⟨test, rfl⟩
      exact sourceContinuous test
  exact joint.comp (continuous_id.prodMk continuous_const)

theorem burnolMultiplicativeDilation_stronglyContinuous (value : BurnolL2) :
    Continuous fun h : ℝ => burnolMultiplicativeDilation h value :=
  isometryFamily_continuous burnolMultiplicativeDilation schwartzDilation_continuous value

theorem burnolDirectRightResolventIntegrand_integrableOn (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : BurnolL2) :
    IntegrableOn (burnolDirectRightResolventIntegrand z value) (Ioi 0) := by
  let decay : ℝ → ℝ := fun h => Real.exp (-(z.re - 1 / 4) * h) * ‖value‖
  have decayIntegrable : IntegrableOn decay (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr rightQuarter)).mul_const ‖value‖
  have continuous : Continuous (burnolDirectRightResolventIntegrand z value) := by
    unfold burnolDirectRightResolventIntegrand
    exact (positiveMellinQuarterRightResolventWeight_continuous z).smul
      ((burnolMultiplicativeDilation_stronglyContinuous value).comp (by fun_prop))
  apply Integrable.mono' decayIntegrable.norm continuous.aestronglyMeasurable.restrict
  filter_upwards with h
  have exactNorm : ‖burnolDirectRightResolventIntegrand z value h‖ = decay h := by
    simp only [burnolDirectRightResolventIntegrand, norm_smul,
      (burnolMultiplicativeDilation (-h / 2)).norm_map,
      norm_positiveMellinQuarterRightResolventWeight, decay]
  rw [exactNorm, Real.norm_of_nonneg]
  positivity

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
