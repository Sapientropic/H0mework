import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualEuler
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def seed : BurnolL2 := burnolQuarterZeroExtension (intervalConstant q)

private def read (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

private def eulerRead (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp GapEuler.euler).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

def edgeRead (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  -eulerRead test - (1 / 2 : ℂ) • read test

theorem edgeRead_apply (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    edgeRead test value = -GapEuler.euler (value : TemperedDistribution ℝ ℂ) test -
      (1 / 2 : ℂ) * (value : TemperedDistribution ℝ ℂ) test := rfl

theorem seed_edge (test : SchwartzMap ℝ ℂ) : edgeRead test seed = GapEuler.edge q test := by
  rw [edgeRead_apply, seed,
    Translator.ForcingCutoff.euler_zeroExtension_pairing _ _ (intervalConstant_coeFn q),
    Translator.ForcingCutoff.zeroExtension_pairing _ _ (intervalConstant_coeFn q)]
  have derivative := DualEuler.edgeChannel_derivative 1 (by norm_num) test
  simp only [DualEuler.edgeChannel, Real.sqrt_one, Complex.ofReal_one, inv_one,
    Real.log_one, neg_zero, coPoissonSchwartzEnergyTranslation_zero, one_mul, div_one] at derivative
  simp only [mul_one, one_mul]
  rw [derivative]
  ring

private theorem channel_edge (a : ℝ) (test : SchwartzMap ℝ ℂ) :
    edgeRead test (ContinuousChannels.channel 1 a seed) = DualEuler.edgeChannel a test := by
  rw [edgeRead_apply]
  change -eulerRead test (ContinuousChannels.channel 1 a seed) -
    (1 / 2 : ℂ) * read test (ContinuousChannels.channel 1 a seed) = _
  simp only [ContinuousChannels.channel, one_mul, map_smul, smul_eq_mul]
  change -((Real.sqrt a : ℂ)⁻¹ * GapEuler.euler (burnolMultiplicativeDilation (Real.log a) seed :
      TemperedDistribution ℝ ℂ) test) -
    (1 / 2 : ℂ) * ((Real.sqrt a : ℂ)⁻¹ *
      (burnolMultiplicativeDilation (Real.log a) seed : TemperedDistribution ℝ ℂ) test) = _
  rw [OriginalRieszFiniteResponse.original_euler_action, OriginalRieszFiniteResponse.original_read]
  have original := seed_edge (coPoissonSchwartzEnergyTranslation (-Real.log a) test)
  rw [edgeRead_apply] at original
  rw [DualEuler.edgeChannel, ← original]
  ring

/-- The full contact is consumed by the same finite reverse source of the original constant. -/
theorem finite_edge (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    DualEuler.edgeProgramme N test = edgeRead test (DualSource.source N seed) := by
  rw [DualSource.source, map_sub, map_sum,
    ← (edgeRead test).integral_comp_comm (ContinuousChannels.channel_integrable 1 N seed)]
  simp only [channel_edge, DualEuler.edgeProgramme]

def seedRaw (x : ℝ) : ℂ := if |x| ≤ q then 1 else 0

theorem seed_coeFn : (seed : ℝ → ℂ) =ᵐ[volume] seedRaw := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (intervalConstant_coeFn q)
  filter_upwards [burnolQuarterZeroExtension_coe (intervalConstant q), localRead] with x extension constant
  change burnolQuarterZeroExtension (intervalConstant q) x = _
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, constant inside, seedRaw, if_pos (abs_le.mpr inside)]
  · rw [indicator_of_notMem inside, seedRaw, if_neg (fun h => inside (abs_le.mp h))]

theorem seedRaw_measurable : Measurable seedRaw := by
  unfold seedRaw
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const measurable_const

def raw (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, seedRaw ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw (a * x)

theorem original_coeFn (N : ℕ) :
    (DualSource.source N seed : ℝ → ℂ) =ᵐ[volume] raw N := by
  have normalization : ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) :
      ℝ → ℂ) =ᵐ[volume] fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw (a * x) := by
    apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn
      (volume.restrict (Ioc 0 (N : ℝ))) _ (ContinuousChannels.channel_integrable 1 N seed)
      (fun point : ℝ × ℝ => seedRaw (point.1 * point.2))
      (seedRaw_measurable.comp (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    exact DualSourceRaw.channel_coeFn seed seedRaw seed_coeFn a inside.1
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) seed x = seedRaw ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn seed seedRaw seed_coeFn (n : ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed)
    (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) seed),
    normalization, channels] with x differenceAt sumAt integralAt channelAt
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) seed) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed : BurnolL2) x = _
  rw [differenceAt, Pi.sub_apply, sumAt, integralAt]
  unfold raw
  congr 1
  exact Finset.sum_congr rfl (fun n inside => channelAt ⟨n, inside⟩)

theorem continuous_raw (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw (a * x)) = (min (N : ℝ) (q / |x|) : ℝ) := by
  have same : (fun a : ℝ => seedRaw (a * x)) =ᵐ[volume.restrict (Ioc 0 (N : ℝ))]
      (Ioc 0 (q / |x|)).indicator (fun _ : ℝ => (1 : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    have incidence : |a * x| ≤ q ↔ a ∈ Ioc 0 (q / |x|) := by
      rw [abs_mul, abs_of_pos inside.1, mem_Ioc,
        and_iff_right inside.1, le_div_iff₀ (abs_pos.mpr nonzero)]
    by_cases included : a ∈ Ioc 0 (q / |x|)
    · rw [seedRaw, if_pos (incidence.mpr included), indicator_of_mem included]
    · rw [seedRaw, if_neg (fun h => included (incidence.mp h)), indicator_of_notMem included]
  rw [integral_congr_ae same, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_self, setIntegral_const,
    Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul, mul_one, min_comm]

def finiteRaw (N : ℕ) (x : ℝ) : ℂ :=
  ((min ⌊q / |x|⌋₊ (N - 1) : ℕ) : ℂ) - ((min (N : ℝ) (q / |x|) : ℝ) : ℂ)

def sawtoothRaw (x : ℝ) : ℂ := -((Int.fract (q / |x|) : ℝ) : ℂ)

private theorem discrete_raw (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    (∑ n ∈ Finset.Ico 1 N, seedRaw ((n : ℝ) * x)) = ((min ⌊q / |x|⌋₊ (N - 1) : ℕ) : ℂ) := by
  have incidence (n : ℕ) (positive : 1 ≤ n) :
      |(n : ℝ) * x| ≤ q ↔ n ≤ ⌊q / |x|⌋₊ := by
    rw [Nat.le_floor_iff' (by omega), abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
      le_div_iff₀ (abs_pos.mpr nonzero)]
  have equal : (Finset.Ico 1 N).filter (fun n : ℕ => |(n : ℝ) * x| ≤ q) =
      Finset.Icc 1 (min ⌊q / |x|⌋₊ (N - 1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨positive, upper⟩, member⟩
      exact ⟨positive, (incidence n positive).mp member, by omega⟩
    · rintro ⟨positive, upper, cutoff⟩
      exact ⟨⟨positive, by omega⟩, (incidence n positive).mpr upper⟩
  simp only [seedRaw, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    equal, Nat.card_Icc, Nat.add_sub_cancel]

theorem raw_eq_finite (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) : raw N x = finiteRaw N x := by
  rw [raw, discrete_raw N x nonzero, continuous_raw N x nonzero]
  rfl

theorem finite_coeFn (N : ℕ) :
    (DualSource.source N seed : ℝ → ℂ) =ᵐ[volume] finiteRaw N := by
  filter_upwards [original_coeFn N, volume.ae_ne (0 : ℝ)] with x source nonzero
  exact source.trans (raw_eq_finite N x nonzero)

theorem finite_measurable (N : ℕ) : Measurable (finiteRaw N) := by
  unfold finiteRaw
  fun_prop

theorem sawtooth_measurable : Measurable sawtoothRaw := by
  unfold sawtoothRaw
  fun_prop

theorem finite_stabilizes (N : ℕ) (x : ℝ) (included : q / |x| < (N : ℝ)) :
    finiteRaw N x = sawtoothRaw x := by
  have nonnegative : 0 ≤ q / |x| := by positivity
  have floorBelow : ⌊q / |x|⌋₊ < N := by
    exact_mod_cast (Nat.floor_le nonnegative).trans_lt included
  rw [finiteRaw, min_eq_left (show ⌊q / |x|⌋₊ ≤ N - 1 by omega), min_eq_right included.le,
    sawtoothRaw, Int.fract]
  have casts := natCast_floor_eq_intCast_floor nonnegative
  rw [← casts]
  push_cast
  ring

theorem finite_clipped (N : ℕ) (positive : 0 < N) (x : ℝ)
    (excluded : (N : ℝ) ≤ q / |x|) : finiteRaw N x = -1 := by
  have below : N ≤ ⌊q / |x|⌋₊ := (Nat.le_floor_iff' positive.ne').mpr excluded
  rw [finiteRaw, min_eq_right (by omega : N - 1 ≤ ⌊q / |x|⌋₊),
    min_eq_left excluded, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  push_cast
  ring

theorem finite_zero (x : ℝ) : finiteRaw 0 x = 0 := by
  rw [finiteRaw, Nat.zero_sub, min_zero, Nat.cast_zero, Nat.cast_zero,
    min_eq_left (by positivity : (0 : ℝ) ≤ q / |x|)]
  simp

theorem sawtooth_bounds (x : ℝ) : ‖sawtoothRaw x‖ ≤ 1 ∧ ‖sawtoothRaw x‖ ≤ q / |x| := by
  rw [sawtoothRaw, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg _)]
  exact ⟨(Int.fract_lt_one _).le, by
    rw [Int.fract, sub_le_self_iff]
    exact_mod_cast Int.floor_nonneg.mpr (show 0 ≤ q / |x| by positivity)⟩

theorem finite_bounds (N : ℕ) (x : ℝ) : ‖finiteRaw N x‖ ≤ 1 ∧ ‖finiteRaw N x‖ ≤ q / |x| := by
  by_cases zero : N = 0
  · subst N
    rw [finite_zero, norm_zero]
    exact ⟨by norm_num, by positivity⟩
  by_cases included : q / |x| < (N : ℝ)
  · rw [finite_stabilizes N x included]
    exact sawtooth_bounds x
  · rw [finite_clipped N (Nat.pos_of_ne_zero zero) x (le_of_not_gt included), norm_neg, norm_one]
    exact ⟨le_rfl, (show (1 : ℝ) ≤ N by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero).trans
      (le_of_not_gt included)⟩

theorem sawtooth_tail (x : ℝ) (outside : q < |x|) :
    sawtoothRaw x = -((q / |x| : ℝ) : ℂ) := by
  rw [sawtoothRaw, Int.fract_eq_self.mpr ⟨by positivity,
    (div_lt_one (by linarith : 0 < |x|)).mpr outside⟩]

private def envelopeRaw (x : ℝ) : ℂ :=
  (symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ)) x + burnolUnitReciprocalPrimitiveRaw x

private theorem envelope_memLp : MemLp envelopeRaw 2 volume := by
  have tail : MemLp burnolUnitReciprocalPrimitiveRaw 2 volume :=
    (Lp.memLp burnolUnitReciprocalPrimitiveL2).ae_eq burnolUnitReciprocalPrimitive_coeFn
  have head : MemLp ((symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval 1) 1 (Or.inr (by simp [symmetricInterval]))
  exact head.add tail

private theorem le_envelope (x : ℝ) (z : ℂ) (bounded : ‖z‖ ≤ 1 ∧ ‖z‖ ≤ q / |x|) :
    ‖z‖ ≤ ‖envelopeRaw x‖ := by
  by_cases small : |x| ≤ 1
  · unfold envelopeRaw
    rw [indicator_of_mem (show x ∈ symmetricInterval 1 from abs_le.mp small)]
    simpa [burnolUnitReciprocalPrimitiveRaw, not_lt.mpr small] using bounded.1
  · have large := lt_of_not_ge small
    unfold envelopeRaw
    rw [indicator_of_notMem (show x ∉ symmetricInterval 1 from fun hx => large.not_ge (abs_le.mpr hx))]
    simp only [burnolUnitReciprocalPrimitiveRaw, if_pos large, zero_add, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact bounded.2.trans (by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right (by norm_num) (abs_nonneg x))

theorem finite_memLp (N : ℕ) : MemLp (finiteRaw N) 2 volume :=
  (Lp.memLp (DualSource.source N seed)).ae_eq (finite_coeFn N)

theorem sawtooth_memLp : MemLp sawtoothRaw 2 volume :=
  envelope_memLp.mono sawtooth_measurable.aestronglyMeasurable
    (Eventually.of_forall (fun x => le_envelope x _ (sawtooth_bounds x)))

def value : BurnolL2 := sawtooth_memLp.toLp sawtoothRaw

theorem value_coeFn : (value : ℝ → ℂ) =ᵐ[volume] sawtoothRaw := sawtooth_memLp.coeFn_toLp

theorem finite_eventually (x : ℝ) : ∀ᶠ N : ℕ in atTop, finiteRaw N x = sawtoothRaw x := by
  refine eventually_atTop.mpr ⟨⌊q / |x|⌋₊ + 1, fun N after => ?_⟩
  exact finite_stabilizes N x ((Nat.lt_floor_add_one (q / |x|)).trans_le (by exact_mod_cast after))

/-- The actual nonzero-mean source converges strongly with its complete exterior tail. -/
theorem original_tendsto : Tendsto (fun N : ℕ => DualSource.source N seed) atTop (𝓝 value) := by
  have squareLimit : Tendsto (fun N => ∫ x : ℝ, ‖finiteRaw N x - sawtoothRaw x‖ ^ 2) atTop (𝓝 0) := by
    have limit := tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 4 * ‖envelopeRaw x‖ ^ 2)
      (F := fun N x => ‖finiteRaw N x - sawtoothRaw x‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun N => (((finite_measurable N).sub sawtooth_measurable).norm.pow_const 2).aestronglyMeasurable)
      (envelope_memLp.norm.integrable_sq.const_mul 4) ?_ ?_
    · simpa using limit
    · intro N
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have bound : ‖finiteRaw N x - sawtoothRaw x‖ ≤ 2 * ‖envelopeRaw x‖ := by
        calc
          _ ≤ ‖finiteRaw N x‖ + ‖sawtoothRaw x‖ := norm_sub_le _ _
          _ ≤ _ := by linarith [le_envelope x _ (finite_bounds N x), le_envelope x _ (sawtooth_bounds x)]
      nlinarith [sq_nonneg (‖finiteRaw N x - sawtoothRaw x‖ - 2 * ‖envelopeRaw x‖),
        norm_nonneg (finiteRaw N x - sawtoothRaw x), norm_nonneg (envelopeRaw x)]
    · filter_upwards with x
      have pointwise : Tendsto (fun N => finiteRaw N x) atTop (𝓝 (sawtoothRaw x)) :=
        tendsto_const_nhds.congr' ((finite_eventually x).mono (fun _ h => h.symm))
      simpa using (pointwise.sub (tendsto_const_nhds (x := sawtoothRaw x))).norm.pow 2
  have source_eq (N : ℕ) : DualSource.source N seed = (finite_memLp N).toLp (finiteRaw N) := by
    apply Lp.ext
    exact (finite_coeFn N).trans (finite_memLp N).coeFn_toLp.symm
  simp_rw [source_eq]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (finiteRaw ·) finite_memLp sawtoothRaw sawtooth_memLp).mpr
  have rootLimit := squareLimit.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
  have limit := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert limit using 1
  · ext N
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((finite_memLp N).sub sawtooth_memLp)]
    simp
  · simp

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
