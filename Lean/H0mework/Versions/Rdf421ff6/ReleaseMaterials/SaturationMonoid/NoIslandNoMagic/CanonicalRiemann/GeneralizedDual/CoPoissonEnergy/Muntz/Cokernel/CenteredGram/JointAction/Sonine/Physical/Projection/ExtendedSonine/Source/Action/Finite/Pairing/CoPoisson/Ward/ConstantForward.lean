import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientFourier

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ConstantForward

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private def weight (u : ℝ) : ℂ := (u : ℂ)⁻¹
private def slope (u : ℝ) : ℂ := -1 / (u : ℂ) ^ 2

private theorem weight_measurable : Measurable weight := by unfold weight; fun_prop
private theorem slope_measurable : Measurable slope := by unfold slope; fun_prop

private theorem derivative (u : ℝ) (positive : 0 < u) : HasDerivAt weight (slope u) u := by
  exact Complex.ofRealCLM.hasDerivAt.inv (Complex.ofReal_ne_zero.mpr positive.ne')

private theorem slope_continuous : ContinuousOn slope (Ioi 0) := by
  intro u positive
  unfold slope
  exact (continuousAt_const.div (Complex.continuous_ofReal.continuousAt.pow 2)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr positive.ne'))).continuousWithinAt

private theorem weight_integrable : IntegrableOn (InfiniteWeightedProgram.weight slope) (Ioi 4) := by
  have reference := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 4)).const_mul 3
  apply reference.mono' ((slope_measurable.norm.mul (Real.continuous_sqrt.measurable.add_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u large
  have positive : 0 < u := (by norm_num : (0 : ℝ) < 4).trans large
  change ‖‖slope u‖ * (Real.sqrt u + 2)‖ ≤ 3 * u ^ (-(3 / 2 : ℝ))
  rw [Real.norm_of_nonneg (by positivity), slope, norm_div, norm_neg, norm_one,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive, one_div, ← inv_pow]
  have root : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr ((by norm_num : (1 : ℝ) ≤ 4).trans large.le)
  have same : u⁻¹ ^ 2 * Real.sqrt u = u ^ (-(3 / 2 : ℝ)) := by
    rw [show u⁻¹ ^ 2 = u ^ (-2 : ℝ) by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow],
      Real.sqrt_eq_rpow, ← Real.rpow_add positive]
    norm_num
  calc
    _ ≤ u⁻¹ ^ 2 * (3 * Real.sqrt u) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ = _ := by rw [← same]; ring

private theorem head_zero : Tendsto (fun u : ℝ => Real.sqrt u * ‖weight u‖) atTop (𝓝 0) := by
  apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u positive
  rw [weight, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive,
    Real.sqrt_eq_rpow, ← Real.rpow_neg_one u, ← Real.rpow_add positive]
  norm_num

private theorem seed_eq_cutoff (upper : ℝ) (large : 4 ≤ upper) :
    burnolWeightedReciprocalStepSource 4 upper weight slope =
      ConstantDual.seed - originalPhysicalCutoff upper⁻¹ ConstantDual.seed := by
  have source := weighted_source_coeFn 4 upper weight slope (by norm_num) large
    (fun u inside => derivative u ((by norm_num : (0 : ℝ) < 4).trans_le inside.1))
    (slope_continuous.mono (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1)) slope_measurable
  apply Lp.ext
  filter_upwards [source, Lp.coeFn_sub ConstantDual.seed (originalPhysicalCutoff upper⁻¹ ConstantDual.seed),
    originalPhysicalCutoff_coeFn upper⁻¹ ConstantDual.seed, ConstantDual.seed_coeFn,
    volume.ae_ne (0 : ℝ)] with x sourceAt subAt cutoffAt original nonzero
  rw [sourceAt, subAt, Pi.sub_apply, cutoffAt]
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have positive : 0 < upper := (by norm_num : (0 : ℝ) < 4).trans_le large
  have lower : 4 ≤ |x|⁻¹ ↔ |x| ≤ q := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) absolute]
    norm_num
  have beyond : |x|⁻¹ < upper ↔ x ∉ symmetricInterval upper⁻¹ := by
    rw [inv_lt_comm₀ absolute positive]
    exact lt_iff_not_ge.trans (not_congr abs_le)
  by_cases small : x ∈ symmetricInterval upper⁻¹
  · rw [indicator_of_mem small, sub_self, burnolReciprocalStepSourceRaw,
      if_neg (fun active => (beyond.mp active.2) small), mul_zero]
  · rw [indicator_of_notMem small, sub_zero, original]
    by_cases inside : |x| ≤ q
    · rw [burnolReciprocalStepSourceRaw, if_pos ⟨lower.mpr inside, beyond.mpr small⟩,
        ConstantDual.seedRaw, if_pos inside, weight, Complex.ofReal_inv, inv_inv]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr absolute.ne')
    · rw [burnolReciprocalStepSourceRaw, if_neg (fun active => inside (lower.mp active.1)),
        mul_zero, ConstantDual.seedRaw, if_neg inside]

private theorem small_cutoff_tendsto (value : BurnolL2) :
    Tendsto (fun upper : ℝ => originalPhysicalCutoff upper⁻¹ value) atTop (𝓝 0) := by
  let raw := fun upper : ℝ => (symmetricInterval upper⁻¹).indicator (value : ℝ → ℂ)
  have member (upper : ℝ) : MemLp (raw upper) 2 volume :=
    (Lp.memLp value).indicator (measurableSet_symmetricInterval _)
  have rawLimit : ∀ᵐ x : ℝ ∂volume, Tendsto (fun upper : ℝ => raw upper x) atTop (𝓝 0) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop |x|⁻¹] with upper large
    have positive : 0 < upper := (inv_pos.mpr (abs_pos.mpr nonzero)).trans large
    have outside : x ∉ symmetricInterval upper⁻¹ := by
      intro inside
      exact (not_le_of_gt ((inv_lt_comm₀ positive (abs_pos.mpr nonzero)).mpr large)) (abs_le.mpr inside)
    simp only [raw, indicator_of_notMem outside]
  have squareLimit : Tendsto (fun upper : ℝ => ∫ x : ℝ, ‖raw upper x‖ ^ 2) atTop (𝓝 0) := by
    have result := tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => ‖value x‖ ^ 2)
      (F := fun upper x => ‖raw upper x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall (fun upper => (member upper).norm.integrable_sq.aestronglyMeasurable))
      (Eventually.of_forall (fun upper => by
        filter_upwards with x
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        by_cases inside : x ∈ symmetricInterval upper⁻¹
        · simp only [raw, indicator_of_mem inside]
          exact le_rfl
        · simp only [raw, indicator_of_notMem inside, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
          exact sq_nonneg _))
      (Lp.memLp value).norm.integrable_sq
      (rawLimit.mono (fun x limit => by simpa using limit.norm.pow 2))
    simpa using result
  have eLpLimit : Tendsto (fun upper : ℝ => eLpNorm (raw upper - (0 : ℝ → ℂ)) 2 volume) atTop (𝓝 0) := by
    have realLimit := squareLimit.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    have result := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using realLimit)
    convert! result using 1
    · funext upper
      rw [sub_zero, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (member upper)]
      simp
    · simp
  have actual := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' raw member (0 : ℝ → ℂ) MemLp.zero).mpr eLpLimit
  simp only [MemLp.toLp_zero] at actual
  apply actual.congr'
  filter_upwards with upper
  apply Lp.ext
  exact (member upper).coeFn_toLp.trans (originalPhysicalCutoff_coeFn upper⁻¹ value).symm

private theorem seed_tendsto : Tendsto (fun upper : ℝ => burnolWeightedReciprocalStepSource 4 upper weight slope)
    atTop (𝓝 ConstantDual.seed) := by
  have actual := (tendsto_const_nhds (x := ConstantDual.seed)).sub (small_cutoff_tendsto ConstantDual.seed)
  simp only [sub_zero] at actual
  apply actual.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper large
  exact (seed_eq_cutoff upper large).symm

/-- The forward limit is generated by the same primitive programme of the original constant source. -/
def value : BurnolL2 := InfiniteWeightedProgram.program slope burnolUnitCountingPrimitiveL2

private theorem finite_source (N : ℕ) : FiniteForcing.source N ConstantDual.seed =
    InfiniteWeightedProgram.program slope (Prefix.primitiveL2 N) := by
  have sourceLimit := ((FiniteSourceContinuity.source_continuous N).tendsto ConstantDual.seed).comp seed_tendsto
  have programmeLimit := InfiniteWeightedProgram.finite_program_tendsto weight slope slope_measurable
    weight_integrable head_zero (Prefix.primitiveL2 N)
  have sameLimit := sourceLimit.congr' (show _ =ᶠ[atTop]
      (fun upper : ℝ => WeightedProgram.program 4 upper weight slope (Prefix.primitiveL2 N)) from by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper large
    exact (weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (by norm_num) large
      (fun u inside => derivative u ((by norm_num : (0 : ℝ) < 4).trans_le inside.1))
      (slope_continuous.mono (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1))
      slope_measurable weight_measurable).symm)
  exact tendsto_nhds_unique sameLimit programmeLimit

theorem original_tendsto : Tendsto (fun N : ℕ => FiniteForcing.source N ConstantDual.seed) atTop (𝓝 value) := by
  have generated := InfiniteWeightedProgram.program_tendsto slope slope_measurable weight_integrable
    Prefix.primitiveL2 burnolUnitCountingPrimitiveL2 Prefix.primitive_tendsto
  exact generated.congr' (Eventually.of_forall (fun N => (finite_source N).symm))

/-- The same finite cutoffs also generate the original full comb-remainder realization. -/
theorem original_realizes (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead ConstantDual.seed test = (value : TemperedDistribution ℝ ℂ) test := by
  have sourceLimit := ((burnolRemainderSourceReadCLM test).continuous.tendsto ConstantDual.seed).comp seed_tendsto
  have continuousRead : Continuous (fun value : BurnolL2 => (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) := by fun_prop
  have waveLimit := (continuousRead.tendsto _).comp
    (InfiniteWeightedProgram.finite_program_tendsto weight slope slope_measurable weight_integrable head_zero
      burnolUnitCountingPrimitiveL2)
  have actual := sourceLimit.congr' (show _ =ᶠ[atTop]
      (fun upper : ℝ => (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolWeightedReciprocalStepWave 4 upper weight slope)) test) from by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper large
    dsimp only [Function.comp_apply]
    rw [burnolRemainderSourceReadCLM_apply]
    exact AmbientFourier.weighted_realizes upper large weight slope
      (slope_continuous.mono (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1)) test)
  simp only [WeightedProgram.program_original] at waveLimit
  simpa only [burnolRemainderSourceReadCLM_apply, value, Lp.toTemperedDistributionCLM_apply] using
    tendsto_nhds_unique actual waveLimit

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ConstantForward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
