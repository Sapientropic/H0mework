import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped InnerProductSpace

open private compact_seed_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactFloor
open private elementary_outside from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa
open private compensated_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical

local notation "q" => (1/4 : ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "Q" => burnolQuarterRestriction
local notation "Hq" => BurnolQuarterIntervalL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "channel" => ContinuousChannels.channel
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "phase" => fun (c : BurnolCompletedMellinCoordinate) (a : ℝ) =>
  (a : ℂ)^(-star (BurnolCompletedMellinCoordinate.value c))
local notation "power" => fun c => SingularCounting.powerL2 (barC c)

private theorem star_real_power (a : ℝ) (positive : 0 < a) (w : ℂ) :
    star ((a : ℂ)^w) = (a : ℂ)^star w := by
  have arg : (a : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.star_def, Complex.conj_ofReal] using (Complex.cpow_conj (a : ℂ) w arg).symm

private theorem forward_reciprocal (a : ℝ) (positive : 0 < a) (v : BurnolL2) :
    channel (-1) a v = (a : ℂ)⁻¹ • channel 1 a⁻¹ v := by
  unfold ContinuousChannels.channel
  rw [neg_one_mul, one_mul, Real.log_inv, Real.sqrt_inv, Complex.ofReal_inv, inv_inv, smul_smul]
  have root : (Real.sqrt a : ℂ)^2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt positive.le
  have live : (Real.sqrt a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 positive).ne'
  have factor : (a : ℂ)⁻¹ * (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ)⁻¹ := by
    rw [← root]
    field_simp [live]
  rw [factor]

private theorem power_covector_raw (c : BurnolCompletedMellinCoordinate) :
    (E (power c) : ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| ≤ q then ((|x| : ℝ) : ℂ)^(c.value-1) else 0 := by
  have source := compact_seed_read (power c) (SingularCounting.powerRaw (barC c))
    (SingularCounting.power_coeFn (barC c)) (fun x _ => by simp only [SingularCounting.powerRaw, abs_abs])
  filter_upwards [source] with x raw
  rw [raw]
  simp only [compactReverseSeedRaw, SingularCounting.powerRaw, abs_abs,
    OriginalPrimitiveRankBalance.conjugateCoordinate, star_star]

private theorem forward_power_raw (c : BurnolCompletedMellinCoordinate) (a : ℝ) (positive : 0 < a) :
    (channel (-1) a (E (power c)) : ℝ → ℂ) =ᵐ[volume]
      fun x => (a : ℂ)^(-c.value) * (if |x| ≤ a*q then ((|x| : ℝ) : ℂ)^(c.value-1) else 0) := by
  have raw := DualSourceRaw.channel_coeFn (E (power c)) _ (power_covector_raw c) a⁻¹ (inv_pos.mpr positive)
  rw [forward_reciprocal a positive]
  filter_upwards [Lp.coeFn_smul (a : ℂ)⁻¹ (channel 1 a⁻¹ (E (power c))), raw] with x scaled moved
  rw [scaled, Pi.smul_apply, smul_eq_mul, moved]
  have threshold : |a⁻¹*x| ≤ q ↔ |x| ≤ a*q := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr positive), ← div_eq_inv_mul, div_le_iff₀ positive, mul_comm q a]
  by_cases inside : |x| ≤ a*q
  · rw [if_pos (threshold.mpr inside), if_pos inside, abs_mul, abs_of_pos (inv_pos.mpr positive),
      show a⁻¹*|x|=|x|/a by rw [div_eq_inv_mul], Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (abs_nonneg x) positive.le]
    have live : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
    have powerLive : (a : ℂ)^c.value ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl live)
    rw [Complex.cpow_sub _ _ live, cpow_one, cpow_neg]
    field_simp [live, powerLive]
  · rw [if_neg (fun h => inside (threshold.mp h)), if_neg inside, mul_zero, mul_zero]

private theorem input_exterior (c : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x ∂volume, q < |x| → input c x = -(1/2 : ℂ)*((|x| : ℝ) : ℂ)^(-star c.value) := by
  unfold input
  filter_upwards [Lp.coeFn_sub (E (S (nativeSmooth c) : Hq)) (elementarySource c),
    burnolQuarterZeroExtension_coe (S (nativeSmooth c) : Hq), gapState_read c] with x sub extended elem outside
  have off : x ∉ symmetricInterval q := fun inside => (not_le_of_gt outside) (abs_le.mpr inside)
  change elementarySource c x = burnolEvenRaw (burnolAmbientMellinKernelRaw c) x at elem
  rw [sub, Pi.sub_apply, extended, indicator_of_notMem off, elem, elementary_outside c x outside, zero_sub]
  ring

private def annulus (a : ℝ) : Set ℝ := symmetricInterval (a*q) \ symmetricInterval q

private theorem annulus_integral (a : ℝ) (large : 1 ≤ a) :
    (∫ x : ℝ in annulus a, (((|x| : ℝ) : ℂ)⁻¹)) = 2 * (Real.log a : ℂ) := by
  let b := a*q
  let f := fun x : ℝ => (((|x| : ℝ) : ℂ)⁻¹)
  have qPositive : 0 < q := by norm_num
  have ordered : q ≤ b := le_mul_of_one_le_left qPositive.le large
  have bPositive := qPositive.trans_le ordered
  have bands : Ico (-b) (-q) ∪ Ioc q b = annulus a := by
    ext x
    change (-b ≤ x ∧ x < -q) ∨ (q < x ∧ x ≤ b) ↔
      (-b ≤ x ∧ x ≤ b) ∧ ¬(-q ≤ x ∧ x ≤ q)
    constructor
    · rintro (⟨lower, upper⟩ | ⟨lower, upper⟩)
      · exact ⟨⟨lower, by linarith⟩, fun h => (not_le_of_gt upper) h.1⟩
      · exact ⟨⟨by linarith, upper⟩, fun h => (not_le_of_gt lower) h.2⟩
    · rintro ⟨⟨lower, upper⟩, outside⟩
      by_cases right : q < x
      · exact Or.inr ⟨right, upper⟩
      · exact Or.inl ⟨lower, lt_of_not_ge (fun bound => outside ⟨bound, le_of_not_gt right⟩)⟩
  have disjoint : Disjoint (Ico (-b) (-q)) (Ioc q b) := by
    refine Set.disjoint_left.mpr (fun x left right => ?_)
    linarith [left.2, right.1]
  have domain {l u : ℝ} (avoids : ∀ x ∈ Icc l u, x ≠ 0) : IntegrableOn f (Icc l u) :=
    ((Complex.continuous_ofReal.comp continuous_abs).continuousOn.inv₀
      (fun x hx => Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (avoids x hx)))).integrableOn_Icc
  have left : IntegrableOn f (Ico (-b) (-q)) :=
    (domain (fun x hx => (hx.2.trans_lt (neg_neg_of_pos qPositive)).ne)).mono_set Ico_subset_Icc_self
  have right : IntegrableOn f (Ioc q b) :=
    (domain (fun x hx => (qPositive.trans_le hx.1).ne')).mono_set Ioc_subset_Icc_self
  have price : (∫ x in q..b, f x) = (Real.log a : ℂ) := by
    calc
      _ = ∫ x in q..b, ((x⁻¹ : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ordered
        intro x hx
        change (((|x| : ℝ) : ℂ)⁻¹) = ((x⁻¹ : ℝ) : ℂ)
        rw [abs_of_pos (qPositive.trans hx.1), Complex.ofReal_inv]
      _ = _ := by
        rw [intervalIntegral.integral_ofReal, integral_inv_of_pos qPositive bPositive,
          show b/q=a by dsimp only [b]; field_simp]
  change (∫ x in annulus a, f x) = _
  rw [← bands, setIntegral_union disjoint measurableSet_Ioc left right, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_neg ordered), ← intervalIntegral.integral_of_le ordered,
    ← intervalIntegral.integral_comp_neg (f := f) (a := q) (b := b)]
  have even : (fun x : ℝ => f (-x)) = f := by funext x; simp only [f, abs_neg]
  rw [even, price, two_mul]

private def moment (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  innerSL ℂ (E (power c))

/-- The adjoint channel contributes the exact logarithmic price of both swept bands. -/
private theorem actual_channel_price (c : BurnolCompletedMellinCoordinate) (a : ℝ) (large : 1 ≤ a) :
    moment c (channel 1 a (input c)) = phase c a * (moment c (input c) - (Real.log a : ℂ)) := by
  have positive := zero_lt_one.trans_le large
  let p := E (power c)
  let f := channel (-1) a p
  let extra := f - ((a : ℂ)^(-c.value)) • p
  have starPhase : star ((a : ℂ)^(-c.value)) = phase c a := by
    rw [star_real_power a positive, star_neg]
  have annulusPrice : inner ℂ extra (input c) = -(phase c a / 2) *
      ∫ x : ℝ in annulus a, (((|x| : ℝ) : ℂ)⁻¹) := by
    have measurable : MeasurableSet (annulus a) :=
      (measurableSet_symmetricInterval (a*q)).diff (measurableSet_symmetricInterval q)
    rw [L2.inner_def, ← integral_indicator measurable, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f (((a : ℂ)^(-c.value)) • p), forward_power_raw c a positive,
      Lp.coeFn_smul ((a : ℂ)^(-c.value)) p, power_covector_raw c, input_exterior c] with
      x sub forward scaled original exterior
    change extra x = _ at sub
    change f x = _ at forward
    change p x = _ at original
    rw [RCLike.inner_apply, starRingEnd_apply, sub, Pi.sub_apply, forward, scaled, Pi.smul_apply,
      smul_eq_mul, original]
    by_cases inside : |x| ≤ q
    · have enlarged : |x| ≤ a*q := inside.trans (le_mul_of_one_le_left (by norm_num) large)
      have off : x ∉ annulus a := fun h => h.2 (abs_le.mp inside)
      simp only [if_pos enlarged, if_pos inside, sub_self, star_zero, mul_zero, indicator_of_notMem off]
    · have outside := lt_of_not_ge inside
      rw [if_neg inside, mul_zero, sub_zero]
      by_cases enlarged : |x| ≤ a*q
      · have on : x ∈ annulus a := ⟨abs_le.mp enlarged, fun h => inside (abs_le.mpr h)⟩
        have xPositive : 0 < |x| := (by norm_num : 0 < q).trans outside
        have xLive : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr xPositive.ne'
        rw [if_pos enlarged, indicator_of_mem on, star_mul, starPhase, star_real_power |x| xPositive,
          star_sub, star_one, exterior outside]
        have exponent : star c.value-1 + -star c.value = (-1 : ℂ) := by ring
        rw [show ((|x| : ℝ) : ℂ)⁻¹ = ((|x| : ℝ) : ℂ)^(-1 : ℂ) by rw [cpow_neg, cpow_one],
          ← exponent, Complex.cpow_add _ _ xLive]
        ring
      · have off : x ∉ annulus a := fun h => enlarged (abs_le.mpr h.1)
        simp only [if_neg enlarged, mul_zero, star_zero, indicator_of_notMem off]
  change inner ℂ p (channel 1 a (input c)) = phase c a * (inner ℂ p (input c) - _)
  rw [← ContinuousChannels.channel_pairing a p (input c)]
  change inner ℂ f (input c) = _
  rw [annulus_integral a large] at annulusPrice
  unfold extra at annulusPrice
  rw [inner_sub_left, inner_smul_left, starRingEnd_apply, starPhase] at annulusPrice
  linear_combination annulusPrice

/-- The existing exterior coefficient reads the actual integer cell and its own continuous segment. -/
theorem actual_tail_increment (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient (barC c) (difference c N) =
      coefficientStep c N * (moment c (E (S (nativeSmooth c) : Hq)) - (Real.log N : ℂ)) +
      ∫ a : ℝ in Ioc (N : ℝ) ((N+1 : ℕ) : ℝ), phase c a * ((Real.log a : ℂ) - (Real.log N : ℂ)) := by
  have even : reflectL2 (difference c N) = difference c N := by
    rw [difference, map_sub, compensated_even, compensated_even]
  rw [actual_compact_tail_coefficient (barC c) _ even]
  have pairing := (ContinuousLinearMap.adjoint_inner_left Q (difference c N) (power c)).symm
  change inner ℂ (power c) (Q (difference c N)) = moment c (difference c N) at pairing
  rw [pairing, actual_increment c N positive, map_add, map_sub, map_smul, smul_eq_mul]
  have bound : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have ordered : (N : ℝ) ≤ ((N+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have channelDomain := (ContinuousChannels.channel_integrable 1 ((N+1 : ℕ) : ℝ) (input c)).mono_set
    (Ioc_subset_Ioc (Nat.cast_nonneg N) le_rfl)
  have phaseContinuous : ContinuousOn (phase c) (Icc (N : ℝ) ((N+1 : ℕ) : ℝ)) :=
    fun a ha => (Complex.continuousAt_ofReal_cpow_const a _ (Or.inr (zero_lt_one.trans_le (bound.trans ha.1)).ne')).continuousWithinAt
  have logContinuous : ContinuousOn Real.log (Icc (N : ℝ) ((N+1 : ℕ) : ℝ)) :=
    fun a ha => (Real.continuousAt_log (zero_lt_one.trans_le (bound.trans ha.1)).ne').continuousWithinAt
  have phaseDomain := (phaseContinuous.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  have errorContinuous : ContinuousOn
      (fun a : ℝ => phase c a * ((Real.log a : ℂ) - (Real.log N : ℂ)))
      (Icc (N : ℝ) ((N+1 : ℕ) : ℝ)) :=
    phaseContinuous.mul ((Complex.continuous_ofReal.comp_continuousOn logContinuous).sub continuousOn_const)
  have errorDomain := (errorContinuous.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  rw [← (moment c).integral_comp_comm channelDomain, actual_channel_price c N bound,
    setIntegral_congr_fun measurableSet_Ioc (fun a ha => actual_channel_price c a (bound.trans ha.1.le))]
  have split (a : ℝ) : phase c a * (moment c (input c) - (Real.log a : ℂ)) =
      phase c a * (moment c (input c) - (Real.log N : ℂ)) -
        phase c a * ((Real.log a : ℂ) - (Real.log N : ℂ)) := by ring
  have segment :
      (∫ a : ℝ in Ioc (N : ℝ) ((N+1 : ℕ) : ℝ), phase c a * (moment c (input c) - (Real.log a : ℂ))) =
      ∫ a : ℝ in Ioc (N : ℝ) ((N+1 : ℕ) : ℝ), phase c a * (moment c (input c) - (Real.log N : ℂ)) -
        phase c a * ((Real.log a : ℂ) - (Real.log N : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioc (fun a _ => split a)
  rw [segment]
  rw [integral_sub (phaseDomain.mul_const _) errorDomain, integral_mul_const]
  have coefficient := actual_coefficient_step c N positive
  rw [intervalIntegral.integral_of_le ordered] at coefficient
  change coefficientStep c N = phase c N - ∫ a : ℝ in Ioc (N : ℝ) ((N+1 : ℕ) : ℝ), phase c a at coefficient
  have whole : moment c (E (S (nativeSmooth c) : Hq)) =
      moment c (input c) + moment c (elementarySource c) := by rw [input, map_sub, sub_add_cancel]
  rw [whole]
  linear_combination -coefficient * (moment c (input c) - (Real.log N : ℂ))

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
