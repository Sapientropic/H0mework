import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.Rate

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology ENNReal

local notation "q₀" => (1/4 : ℝ)
local notation "μq" => volume.restrict (Ioc (0 : ℝ) q₀)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "A" => fun c (n : Nat) => Prod.fst (clockCoefficients c (actualClockPair c n))
local notation "B" => fun c (n : Nat) => Prod.snd (clockCoefficients c (actualClockPair c n))
local notation "N" => fun n : Nat => ((n+2 : Nat) : ℝ)
local notation "clock" => fun n : Nat => Real.log (N n)
local notation "phase" => fun c (n : Nat) => ((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "scale" => fun c (n : Nat) => (clock n : ℂ)*phase c n
local notation "Y" => countedNormalizedField
local notation "H" => fun c (x : ℝ) => (x : ℂ)^(-s₀ c)*(1/2 : ℂ)

private def collarBudget (c : BurnolCompletedMellinCoordinate) : ℝ :=
  2*‖GapEuler.gapMean q₀ c‖*(2*q₀^c.value.re/‖s₀ c‖)

private theorem collarBudget_nonnegative (c : BurnolCompletedMellinCoordinate) : 0 ≤ collarBudget c := by
  unfold collarBudget
  positivity

private theorem collar_primitive_bound (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (positive : 0 < x) (bounded : x ≤ q₀) :
    ‖collarPrimitive c x‖ ≤ Real.log (q₀/x)+collarBudget c := by
  have ratio : 1 ≤ q₀/x := (le_div_iff₀ positive).mpr (by simpa only [one_mul] using bounded)
  have logPositive := Real.log_nonneg ratio
  have right : 0 ≤ (s₀ c).re := by
    change 0 ≤ (star c.value).re
    simp only [star_def, conj_re]
    linarith [c.rightHalf]
  have power : ‖(q₀ : ℂ)^(s₀ c)-(x : ℂ)^(s₀ c)‖ ≤ 2*q₀^c.value.re := by
    apply (norm_sub_le _ _).trans
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0 < q₀),
      Complex.norm_cpow_eq_rpow_re_of_pos positive]
    have compare := Real.rpow_le_rpow positive.le bounded right
    change x^(star c.value).re ≤ q₀^(star c.value).re at compare
    simp only [star_def, conj_re] at compare ⊢
    linarith
  unfold collarPrimitive collarBudget
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg logPositive, norm_mul, norm_mul,
    Complex.norm_ofNat, norm_div]
  have contribution := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right power (norm_nonneg (s₀ c)))
    (show 0 ≤ 2*‖GapEuler.gapMean q₀ c‖ by positivity)
  linarith only [contribution]

private theorem late_endpoint_budget (c : BurnolCompletedMellinCoordinate) :
    ∀ᶠ n : Nat in atTop, ‖(scale c n)⁻¹*A c n‖ ≤ 1 ∧
      ‖(phase c n)⁻¹*B c n‖ ≤ 1 ∧ 1 ≤ clock n := by
  have outer := (actual_scaled_outer_limit c).norm.eventually
    (gt_mem_nhds (by simp : ‖(1 : ℂ)‖ < 2))
  have halfNorm : ‖(-(1/2 : ℂ))‖ = 1/2 := by rw [norm_neg, norm_div, norm_one]; norm_num
  have count := (actual_phase_count_limit c).norm.eventually
    (gt_mem_nhds (by rw [halfNorm]; norm_num : ‖(-(1/2 : ℂ))‖ < 1))
  have indices : Tendsto N atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  filter_upwards [outer, count, (Real.tendsto_log_atTop.comp indices).eventually (eventually_ge_atTop 1)]
    with n outerBound countBound clockBound
  change ‖(scale c n)⁻¹*(-(2*A c n))‖ < 2 at outerBound
  rw [show (scale c n)⁻¹*(-(2*A c n)) = -(2*((scale c n)⁻¹*A c n)) by ring,
    norm_neg, norm_mul, Complex.norm_ofNat] at outerBound
  exact ⟨by linarith, countBound.le, clockBound⟩

private theorem actual_covered_bound (c : BurnolCompletedMellinCoordinate) :
    ∀ᶠ n : Nat in atTop, ∀ᵐ x : ℝ ∂μq, q₀/x < N n →
      ‖Y c n x‖ ≤ (2+collarBudget c)*x^(-c.value.re) := by
  filter_upwards [late_endpoint_budget c] with n budget
  obtain ⟨outer, count, clockBound⟩ := budget
  have clockPositive := zero_lt_one.trans_le clockBound
  have inverseNonnegative : 0 ≤ (clock n)⁻¹ := inv_nonneg.mpr clockPositive.le
  have countScale : ‖(scale c n)⁻¹*B c n‖ ≤ (clock n)⁻¹ := by
    have split : (scale c n)⁻¹*B c n = (clock n : ℂ)⁻¹*((phase c n)⁻¹*B c n) := by
      rw [mul_inv_rev]
      ring
    rw [split, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos clockPositive]
    exact mul_le_of_le_one_right inverseNonnegative count
  let delta := floorFromResponses c+riemannZeta (s₀ c) • elementarySource c-compensated c (n+2)
  let action := burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c) delta
  filter_upwards [ae_restrict_of_ae (actual_settled_R_profile c n),
    ae_restrict_of_ae (Lp.coeFn_smul (scale c n)⁻¹ action), ae_restrict_mem measurableSet_Ioc]
    with x acted scaled member covered
  have primitive := collar_primitive_bound c member.1 member.2
  have logBound : Real.log (q₀/x) ≤ clock n :=
    Real.log_le_log (div_pos (by norm_num) member.1) covered.le
  have part : ‖(scale c n)⁻¹*B c n‖*‖collarPrimitive c x‖ ≤ 1+collarBudget c := by
    calc
      _ ≤ (clock n)⁻¹*(clock n+collarBudget c) :=
        mul_le_mul countScale (primitive.trans (add_le_add_left logBound _)) (norm_nonneg _) inverseNonnegative
      _ = 1+(clock n)⁻¹*collarBudget c := by rw [mul_add, inv_mul_cancel₀ clockPositive.ne']
      _ ≤ _ := by
        have paid := mul_le_of_le_one_left (collarBudget_nonnegative c)
          (inv_le_one_of_one_le₀ clockBound)
        linarith only [paid]
  change (((scale c n)⁻¹) • action : BurnolL2) x = _ at scaled
  change ‖(((scale c n)⁻¹) • action : BurnolL2) x‖ ≤ _
  have formula : (scale c n)⁻¹*((x : ℂ)^(-s₀ c)*(-A c n+B c n*collarPrimitive c x)) =
      (x : ℂ)^(-s₀ c)*(-((scale c n)⁻¹*A c n)+((scale c n)⁻¹*B c n)*collarPrimitive c x) := by ring
  have raw := acted member.1 member.2 covered
  change action x = _ at raw
  rw [scaled, Pi.smul_apply, smul_eq_mul, raw, formula, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos member.1, neg_re]
  change x^(-(star c.value).re)*_ ≤ _
  simp only [star_def, conj_re]
  rw [mul_comm (2+collarBudget c)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg member.1.le _)
  have combine := norm_add_le (-((scale c n)⁻¹*A c n))
    (((scale c n)⁻¹*B c n)*collarPrimitive c x)
  rw [norm_neg, norm_mul ((scale c n)⁻¹*B c n) (collarPrimitive c x)] at combine
  exact combine.trans ((add_le_add outer part).trans_eq (by ring))

private theorem half_power_norm (c : BurnolCompletedMellinCoordinate) {x : ℝ} (positive : 0 < x) :
    ‖H c x‖ = (1/2 : ℝ)*x^(-c.value.re) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive, neg_re, norm_div, norm_one]
  change x^(-(star c.value).re)*(1/‖(2 : ℂ)‖) = _
  simp only [star_def, conj_re, Complex.norm_ofNat, mul_comm]

private theorem positive_power_integrable (c : BurnolCompletedMellinCoordinate) :
    Integrable (fun x : ℝ => x^(-c.value.re)) μq := by
  have domain : IntegrableOn (fun x : ℝ => x^(-c.value.re)) (Ioo 0 q₀) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : 0 < q₀)).mpr
      (show -1 < -c.value.re by linarith [c.belowOne])
  exact domain.congr_set_ae Ioo_ae_eq_Ioc.symm

private theorem half_power_integrable (c : BurnolCompletedMellinCoordinate) :
    Integrable (H c) μq := by
  have measurable : Measurable (H c) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    have live : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
    exact ((Complex.continuousAt_ofReal_cpow_const x (-s₀ c) (Or.inr live)).mul
      continuousAt_const).continuousWithinAt
  apply (integrable_norm_iff measurable.aestronglyMeasurable).mp
  apply ((positive_power_integrable c).const_mul (1/2 : ℝ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (half_power_norm c hx.1).symm

local instance positiveQuarterFinite : IsFiniteMeasure μq :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩

private theorem actual_positive_integrable (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    Integrable (Y c n : ℝ → ℂ) μq := by
  exact ((Lp.memLp (Y c n)).mono_measure Measure.restrict_le_self).integrable (by norm_num)

private def coveredSet (n : Nat) : Set ℝ := {x | q₀/x < N n}

private theorem covered_measurable (n : Nat) : MeasurableSet (coveredSet n) :=
  measurableSet_lt (measurable_const.div measurable_id) measurable_const

/-- The original normalized field converges in L¹ on its positive quarter.
The unresolved window is paid by the same count, and the covered points by
the two literal endpoint coefficients. -/
theorem actual_normalized_counted_positive_L1 (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ∫ x in Ioc (0 : ℝ) q₀, ‖Y c n x-H c x‖) atTop (𝓝 0) := by
  let V := fun n : Nat => (coveredSet n).indicator (Y c n : ℝ → ℂ)
  have Vint (n : Nat) : Integrable (V n) μq :=
    (actual_positive_integrable c n).indicator (covered_measurable n)
  have HInt := half_power_integrable c
  have indices : Tendsto N atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have pointwise : ∀ᵐ x : ℝ ∂μq, Tendsto (fun n => ‖V n x-H c x‖) atTop (𝓝 0) := by
    filter_upwards [actual_normalized_counted_interior_limit c] with x original
    have paid : Tendsto (fun n => V n x) atTop (𝓝 (H c x)) := by
      apply original.congr'
      filter_upwards [indices.eventually (eventually_gt_atTop (q₀/x))] with n after
      exact (indicator_of_mem (show x ∈ coveredSet n from after) _).symm
    simpa only [sub_self, norm_zero] using (paid.sub_const (H c x)).norm
  have dominate : ∀ᶠ n : Nat in atTop, ∀ᵐ x : ℝ ∂μq,
      ‖‖V n x-H c x‖‖ ≤ (5/2+collarBudget c)*x^(-c.value.re) := by
    filter_upwards [actual_covered_bound c] with n budget
    filter_upwards [budget, ae_restrict_mem measurableSet_Ioc] with x source hx
    have read : ‖V n x‖ ≤ (2+collarBudget c)*x^(-c.value.re) := by
      by_cases after : x ∈ coveredSet n
      · change ‖(coveredSet n).indicator (Y c n : ℝ → ℂ) x‖ ≤ _
        rw [indicator_of_mem after]
        exact source after
      · change ‖(coveredSet n).indicator (Y c n : ℝ → ℂ) x‖ ≤ _
        rw [indicator_of_notMem after, norm_zero]
        exact mul_nonneg (by linarith [collarBudget_nonnegative c]) (Real.rpow_nonneg hx.1.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (norm_sub_le _ _).trans ((add_le_add read (half_power_norm c hx.1).le).trans_eq ?_)
    ring
  have covered : Tendsto (fun n : Nat => ∫ x, ‖V n x-H c x‖ ∂μq) atTop (𝓝 0) := by
    simpa only [integral_zero, Pi.sub_apply] using tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => (5/2+collarBudget c)*x^(-c.value.re))
      (Eventually.of_forall fun n => ((Vint n).sub HInt).norm.aestronglyMeasurable)
      dominate ((positive_power_integrable c).const_mul _) pointwise
  have missed (n : Nat) :
      (∫ x, ‖Y c n x-V n x‖ ∂μq) = ∫ x in Ioc (0 : ℝ) (q₀/N n), ‖Y c n x‖ := by
    have large : 1 ≤ N n := by dsimp only; exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n+1))
    have positive : 0 < N n := zero_lt_one.trans_le large
    have shorter : q₀/N n ≤ q₀ := div_le_self (by norm_num) large
    have restriction : ((volume : Measure ℝ).restrict (Ioc 0 q₀)).restrict (Ioc 0 (q₀/N n)) =
        volume.restrict (Ioc 0 (q₀/N n)) := by
      rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioc_right shorter)]
    have equal : (∫ x, ‖Y c n x-V n x‖ ∂μq) =
        ∫ x, (Ioc (0 : ℝ) (q₀/N n)).indicator (fun y => ‖Y c n y‖) x ∂μq := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have whereCovered : x ∈ coveredSet n ↔ q₀/N n < x := by
        change q₀/x < N n ↔ q₀/N n < x
        rw [div_lt_iff₀ hx.1, div_lt_iff₀ positive, mul_comm (N n) x]
      by_cases after : x ∈ coveredSet n
      · have missing : x ∉ Ioc (0 : ℝ) (q₀/N n) := fun hm => (not_le_of_gt (whereCovered.mp after)) hm.2
        change ‖Y c n x-(coveredSet n).indicator (Y c n : ℝ → ℂ) x‖ = _
        rw [indicator_of_mem after, sub_self, norm_zero, indicator_of_notMem missing]
      · have within : x ∈ Ioc (0 : ℝ) (q₀/N n) := ⟨hx.1, le_of_not_gt (fun h => after (whereCovered.mpr h))⟩
        change ‖Y c n x-(coveredSet n).indicator (Y c n : ℝ → ℂ) x‖ = _
        rw [indicator_of_notMem after, sub_zero, indicator_of_mem within]
    rw [equal, integral_indicator measurableSet_Ioc, restriction]
  have origin : Tendsto (fun n : Nat => ∫ x, ‖Y c n x-V n x‖ ∂μq) atTop (𝓝 0) :=
    (actual_normalized_counted_uncovered_L1 c).congr' (Eventually.of_forall fun n => (missed n).symm)
  have small := origin.add covered
  simp only [zero_add] at small
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ small
  filter_upwards with n
  have YInt := actual_positive_integrable c n
  have sum : (∫ x, ‖Y c n x-V n x‖+‖V n x-H c x‖ ∂μq) =
      (∫ x, ‖Y c n x-V n x‖ ∂μq)+(∫ x, ‖V n x-H c x‖ ∂μq) := by
    simpa only [Pi.sub_apply, Pi.add_apply] using
      integral_add ((YInt.sub (Vint n)).norm) (((Vint n).sub HInt).norm)
  rw [← sum]
  apply integral_mono ((YInt.sub HInt).norm) (((YInt.sub (Vint n)).norm).add (((Vint n).sub HInt).norm))
  intro x
  have triangle := norm_add_le (Y c n x-V n x) (V n x-H c x)
  rwa [sub_add_sub_cancel] at triangle

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
