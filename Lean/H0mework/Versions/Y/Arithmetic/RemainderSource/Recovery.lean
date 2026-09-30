import H0mework.Versions.Y.Arithmetic.RemainderSource.FaithfulForward
import H0mework.Versions.Y.Arithmetic.RiemannDivision.RightDivisionRepresentative
import H0mework.Arithmetic.MuntzAction.GaussianSchwartz

/-! All even inner-gap L² sources are faithfully recovered from the actual remainder action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

private theorem innerGapWeight_memLp (power : ℕ) (positive : 0 < power) :
    MemLp (fun x : ℝ => if (1 / 4 : ℝ) < |x| then (|x| ^ power)⁻¹ else 0) 2 volume := by
  let tail := burnolRadiusMellinTailKernelRaw (1 / 4) (power : ℂ)
  have rightHalf : (1 / 2 : ℝ) < (power : ℂ).re := by
    simp only [Complex.natCast_re]
    have atLeastOne : (1 : ℝ) ≤ power := by exact_mod_cast positive
    linarith
  have tailMem : MemLp tail 2 volume := burnolRadiusMellinTailKernelRaw_memLp
    (by norm_num) (power : ℂ) rightHalf
  have fullMem := (tailMem.add (tailMem.comp_measurePreserving negMeasurePreserving)).norm
  apply fullMem.ae_eq
  filter_upwards with x
  change ‖tail x + tail (-x)‖ = _
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative]
    have negativeOutside : ¬ -x ∈ Ioi (1 / 4 : ℝ) := by simp only [mem_Ioi]; linarith
    simp only [tail, burnolRadiusMellinTailKernelRaw, negativeOutside, if_false, add_zero, mem_Ioi]
    split_ifs with hx
    · simp only [star_natCast, Complex.cpow_neg, Complex.cpow_natCast, norm_inv, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonnegative]
    · simp only [norm_zero]
  · have negative : x < 0 := lt_of_not_ge nonnegative
    rw [abs_of_neg negative]
    have positiveOutside : ¬ x ∈ Ioi (1 / 4 : ℝ) := by simp only [mem_Ioi]; linarith
    simp only [tail, burnolRadiusMellinTailKernelRaw, positiveOutside, if_false, zero_add, mem_Ioi]
    split_ifs with hx
    · simp only [star_natCast, Complex.cpow_neg, Complex.cpow_natCast, norm_inv, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (neg_pos.mpr negative)]
    · simp only [norm_zero]

private theorem innerGap_weighted_integrable (raw : ℝ → ℂ) (memLp : MemLp raw 2 volume)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0) (power : ℕ) (positive : 0 < power) :
    Integrable (fun x : ℝ => ‖raw x‖ / |x| ^ power) := by
  apply (memLp.norm.integrable_mul (innerGapWeight_memLp power positive)).congr
  filter_upwards with x
  change ‖raw x‖ * (if (1 / 4 : ℝ) < |x| then (|x| ^ power)⁻¹ else 0) = _
  split_ifs with outside
  · rw [div_eq_mul_inv]
  · rw [gap (le_of_not_gt outside), norm_zero, zero_mul, zero_div]

private theorem innerGap_reciprocal_integrable (raw : ℝ → ℂ) (measurable : Measurable raw)
    (memLp : MemLp raw 2 volume) (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ)⁻¹ * raw x) (Ioi 0) := by
  have normRead : (fun x : ℝ => ‖(x : ℂ)⁻¹ * raw x‖) =
      fun x => ‖raw x‖ / |x| := by
    funext x
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  have integrable := innerGap_weighted_integrable raw memLp gap 1 (by decide)
  have normIntegrable : Integrable (fun x : ℝ => ‖(x : ℂ)⁻¹ * raw x‖) := by
    simpa only [normRead, pow_one] using integrable
  exact ((integrable_norm_iff
    ((Complex.measurable_ofReal.comp measurable_id).inv.mul measurable).aestronglyMeasurable
      ).mp normIntegrable).integrableOn

private theorem forward_locallyIntegrable (raw : ℝ → ℂ) (measurable : Measurable raw)
    (atZero : raw 0 = 0) (weighted : Integrable (fun x : ℝ => ‖raw x‖ / |x| ^ 3)) :
    LocallyIntegrable (burnolInnerGapForward raw) volume := by
  have integrable := burnolInnerGapForward_test_integrable raw measurable atZero weighted clozelGaussianSchwartz
  have inverseContinuous : Continuous (fun x : ℝ => (Real.exp (Real.pi * x ^ 2) : ℂ)) := by
    fun_prop
  apply (integrable.locallyIntegrable.mul_continuous inverseContinuous).congr
  filter_upwards with x
  rw [clozelGaussianSchwartz_apply]
  change (Real.exp (-Real.pi * x ^ 2) : ℂ) * burnolInnerGapForward raw x *
    (Real.exp (Real.pi * x ^ 2) : ℂ) = _
  rw [mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf
  simp only [Real.exp_zero, Complex.ofReal_one, one_mul]

theorem burnolInnerGapForward_innerGap (raw : ℝ → ℂ)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0)
    {x : ℝ} (small : |x| ≤ (1 / 4 : ℝ)) : burnolInnerGapForward raw x = 0 := by
  unfold burnolInnerGapForward
  calc
    _ = ∑' _ : ℕ+, (0 : ℂ) := by
      apply tsum_congr
      intro n
      have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
      have atLeastOne : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
      have divided : |x / (n : ℕ)| ≤ (1 / 4 : ℝ) := by
        rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
        linarith
      rw [gap divided, mul_zero]
    _ = 0 := tsum_zero

private theorem burnolRemainderSourceRead_faithful_raw (source : BurnolL2) (raw : ℝ → ℂ)
    (measurable : Measurable raw) (represents : (source : ℝ → ℂ) =ᵐ[volume] raw)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0)
    (even : ∀ x, raw (-x) = raw x)
    (readZero : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test = 0) :
    source = 0 := by
  let normal := ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u
  have mem : MemLp raw 2 volume := (Lp.memLp source).ae_eq represents
  have atZero : raw 0 = 0 := gap (by norm_num)
  have weighted := innerGap_weighted_integrable raw mem gap 3 (by decide)
  have reciprocal := innerGap_reciprocal_integrable raw measurable mem gap
  have zeroRead : ∀ᵐ x : ℝ ∂volume, burnolInnerGapForward raw x - normal = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((forward_locallyIntegrable raw measurable atZero weighted).sub
        (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : ℝ => normal) volume))
    intro test smooth compact
    let complexTest : SchwartzMap ℝ ℂ :=
      (compact.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp smooth)
    have actual := burnolRemainderSourceRead_forward source raw measurable represents
      atZero even weighted reciprocal complexTest
    rw [readZero] at actual
    change 0 = ∫ x : ℝ, (test x : ℂ) * (burnolInnerGapForward raw x - normal) at actual
    change (∫ x : ℝ, test x • (burnolInnerGapForward raw x - normal)) = 0
    simpa only [Complex.real_smul] using actual.symm
  have normalZero : normal = 0 := by
    by_contra nonzero
    have bad : ∀ᵐ x : ℝ ∂volume.restrict (symmetricInterval (1 / 4 : ℝ)), False := by
      filter_upwards [ae_restrict_of_ae zeroRead,
        ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x hx inside
      rw [burnolInnerGapForward_innerGap raw gap (abs_le.mpr inside), zero_sub, neg_eq_zero] at hx
      exact nonzero hx
    have measureZero : (volume.restrict (symmetricInterval (1 / 4 : ℝ))) univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using bad
    norm_num [symmetricInterval] at measureZero
  have forwardZero : ∀ᵐ x : ℝ ∂volume, burnolInnerGapForward raw x = 0 := by
    simpa only [normalZero, sub_zero] using zeroRead
  have scaledZero (n : ℕ+) : ∀ᵐ x : ℝ ∂volume,
      burnolInnerGapForward raw (x / (n : ℕ)) = 0 := by
    have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := ((n : ℕ) : ℝ)⁻¹) (inv_ne_zero positive.ne')
    simpa only [smul_eq_mul, inv_mul_eq_div] using qmp.ae forwardZero
  have rawZero : ∀ᵐ x : ℝ ∂volume, raw x = 0 := by
    filter_upwards [ae_all_iff.mpr scaledZero] with x hx
    rw [← burnolCenteredMobiusInverse_forward_innerGap raw gap 0 x]
    unfold burnolCenteredMobiusInverse
    calc
      _ = ∑' _ : ℕ+, (0 : ℂ) := by
        apply tsum_congr
        intro n
        dsimp only
        rw [hx n, burnolInnerGapForward_innerGap raw gap (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]
        ring
      _ = 0 := tsum_zero
  apply Lp.ext
  filter_upwards [represents, rawZero, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)]
    with x hraw hzero htarget
  exact hraw.trans (hzero.trans htarget.symm)

private def innerGapRepresentative (source : BurnolL2) : ℝ → ℂ :=
  (symmetricInterval (1 / 4 : ℝ))ᶜ.indicator (burnolEvenStrongRepresentative source)

private theorem innerGapRepresentative_measurable (source : BurnolL2) :
    Measurable (innerGapRepresentative source) :=
  (burnolEvenStrongRepresentative_stronglyMeasurable source).measurable.indicator
    (measurableSet_symmetricInterval (1 / 4 : ℝ)).compl

private theorem innerGapRepresentative_gap (source : BurnolL2) {x : ℝ}
    (small : |x| ≤ (1 / 4 : ℝ)) : innerGapRepresentative source x = 0 := by
  exact indicator_of_notMem (not_not.mpr (abs_le.mp small)) _

private theorem innerGapRepresentative_even (source : BurnolL2) (x : ℝ) :
    innerGapRepresentative source (-x) = innerGapRepresentative source x := by
  classical
  have same : -x ∈ symmetricInterval (1 / 4 : ℝ) ↔ x ∈ symmetricInterval (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [innerGapRepresentative, indicator_apply, mem_compl_iff, same]
  split_ifs
  · rfl
  · unfold burnolEvenStrongRepresentative
    simp only [neg_neg, add_comm]

private theorem innerGapRepresentative_ae (source : BurnolL2)
    (even : reflectL2 source = source)
    (gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0) :
    (source : ℝ → ℂ) =ᵐ[volume] innerGapRepresentative source := by
  have whole := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp gap
  filter_upwards [burnolEvenStrongRepresentative_ae_eq source even, whole] with x hrep hgap
  unfold innerGapRepresentative
  by_cases inside : x ∈ symmetricInterval (1 / 4 : ℝ)
  · rw [indicator_of_notMem (show x ∉ (symmetricInterval (1 / 4 : ℝ))ᶜ from not_not.mpr inside)]
    exact hgap inside
  · rw [indicator_of_mem inside]
    exact hrep.symm

theorem burnolRemainderSourceRead_faithful (source : BurnolL2)
    (even : reflectL2 source = source)
    (gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0)
    (readZero : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test = 0) :
    source = 0 :=
  burnolRemainderSourceRead_faithful_raw source (innerGapRepresentative source)
    (innerGapRepresentative_measurable source) (innerGapRepresentative_ae source even gap)
    (innerGapRepresentative_gap source) (innerGapRepresentative_even source) readZero

/-- A realized full source yields its actual co-sum representative; the
normalization is still the reciprocal integral of that same source. -/
theorem burnolRemainderSourceRead_realization_ae (source value : BurnolL2)
    (even : reflectL2 source = source)
    (gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * value x) :
    ∃ raw : ℝ → ℂ, (source : ℝ → ℂ) =ᵐ[volume] raw ∧
      (∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0) ∧
      (value : ℝ → ℂ) =ᵐ[volume] (fun x => burnolInnerGapForward raw x -
        ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) := by
  let raw := innerGapRepresentative source
  have represents := innerGapRepresentative_ae source even gap
  have measurable := innerGapRepresentative_measurable source
  have rawGap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0 :=
    innerGapRepresentative_gap source
  have mem : MemLp raw 2 volume := (Lp.memLp source).ae_eq represents
  have atZero : raw 0 = 0 := rawGap (by norm_num)
  have weighted := innerGap_weighted_integrable raw mem rawGap 3 (by decide)
  have reciprocal := innerGap_reciprocal_integrable raw measurable mem rawGap
  refine ⟨raw, represents, rawGap, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp value).locallyIntegrable (by norm_num))
    ((forward_locallyIntegrable raw measurable atZero weighted).sub continuous_const.locallyIntegrable)
  intro test smooth compact
  let complexTest : SchwartzMap ℝ ℂ :=
    (compact.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp smooth)
  have actual := burnolRemainderSourceRead_forward source raw measurable represents atZero
    (innerGapRepresentative_even source) weighted reciprocal complexTest
  rw [realizes] at actual
  change (∫ x : ℝ, (test x : ℂ) * value x) =
    ∫ x : ℝ, (test x : ℂ) * (burnolInnerGapForward raw x -
      ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) at actual
  simpa only [Complex.real_smul, Pi.sub_apply] using actual

/-- Inner-gap source data pay the weighted integrals in the forward read. -/
theorem burnolRemainderSourceRead_innerGap_forward (source : BurnolL2) (raw : ℝ → ℂ)
    (measurable : Measurable raw) (represents : (source : ℝ → ℂ) =ᵐ[volume] raw)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0)
    (even : ∀ x, raw (-x) = raw x) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * (burnolInnerGapForward raw x -
        ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) := by
  have mem := (Lp.memLp source).ae_eq represents
  exact burnolRemainderSourceRead_forward source raw measurable represents (gap (by norm_num)) even
    (innerGap_weighted_integrable raw mem gap 3 (by decide))
    (innerGap_reciprocal_integrable raw measurable mem gap) test

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
