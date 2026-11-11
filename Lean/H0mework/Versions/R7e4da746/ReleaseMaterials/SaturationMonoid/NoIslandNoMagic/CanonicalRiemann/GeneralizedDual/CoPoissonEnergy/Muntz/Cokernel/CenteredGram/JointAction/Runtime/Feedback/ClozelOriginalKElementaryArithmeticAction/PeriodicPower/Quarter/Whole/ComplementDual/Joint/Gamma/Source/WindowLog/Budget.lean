import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WindowLog

open Complex Filter MeasureTheory Set
open scoped Topology
open private powerProfile powerEnvelopeRaw powerEnvelopeL2 envelope_norm envelope_raw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

private theorem profile_nonnegative {t : ℝ} (nonnegative : 0 ≤ t) : 0 ≤ powerProfile t := by
  unfold powerProfile
  split_ifs <;> exact Real.rpow_nonneg nonnegative _

private theorem profile_measurable : Measurable powerProfile := by
  unfold powerProfile
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (by fun_prop) (by fun_prop)

private theorem log_ratio_bound (t : ℝ) (positive : 0 < t) :
    |Real.log t| ≤ 8 * powerProfile t * |1-t| := by
  unfold powerProfile
  by_cases lower : t ≤ 1
  · rw [if_pos lower, abs_of_nonneg (sub_nonneg.mpr lower),
      abs_of_nonpos (Real.log_nonpos positive.le lower)]
    let p := t ^ (-1/4 : ℝ)
    change -Real.log t ≤ 8*p*(1-t)
    have hp : 1 ≤ p :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos positive lower (by norm_num)
    by_cases small : t ≤ 1/2
    · have logarithm := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (-1/4 : ℝ))
      rw [Real.log_rpow positive] at logarithm
      change (-1/4 : ℝ) * Real.log t ≤ p-1 at logarithm
      nlinarith [mul_nonneg (show 0 ≤ p by linarith) (show 0 ≤ 1/2-t by linarith)]
    · have logarithm := Real.log_le_sub_one_of_pos (inv_pos.mpr positive)
      rw [Real.log_inv] at logarithm
      have inverse : t⁻¹ ≤ 2 := by
        rw [inv_eq_one_div, div_le_iff₀ positive]
        linarith [le_of_not_ge small]
      have amount : t⁻¹ - 1 = (1-t)*t⁻¹ := by
        rw [sub_mul, one_mul, mul_inv_cancel₀ positive.ne']
      rw [amount] at logarithm
      have first := mul_le_mul_of_nonneg_left inverse (sub_nonneg.mpr lower)
      nlinarith [mul_nonneg (show 0 ≤ p-1 by linarith) (sub_nonneg.mpr lower)]
  · have upper : 1 ≤ t := le_of_not_ge lower
    rw [if_neg lower, abs_of_nonpos (sub_nonpos.mpr upper), neg_sub,
      abs_of_nonneg (Real.log_nonneg upper)]
    let p := t ^ (-3/4 : ℝ)
    change Real.log t ≤ 8*p*(t-1)
    by_cases large : 2 ≤ t
    · have logarithm := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (1/4 : ℝ))
      rw [Real.log_rpow positive] at logarithm
      have product : t ^ (1/4 : ℝ) = p*t := by
        calc
          _ = t ^ ((-3/4 : ℝ) + 1) := by norm_num
          _ = t ^ (-3/4 : ℝ) * t ^ (1 : ℝ) := Real.rpow_add positive _ _
          _ = _ := by rw [Real.rpow_one]
      rw [product] at logarithm
      nlinarith [mul_nonneg (show 0 ≤ p by positivity) (show 0 ≤ t-2 by linarith)]
    · have pLower : 1/2 ≤ p := by
        have upperPower : t ^ (3/4 : ℝ) ≤ 2 :=
          (Real.rpow_le_rpow_of_exponent_le upper (by norm_num : (3/4 : ℝ) ≤ 1)).trans
            (by rw [Real.rpow_one]; exact le_of_not_ge large)
        dsimp [p]
        rw [show (-3/4 : ℝ) = -(3/4) by ring, Real.rpow_neg positive.le, inv_eq_one_div,
          le_div_iff₀ (Real.rpow_pos_of_pos positive _)]
        linarith
      nlinarith [Real.log_le_sub_one_of_pos positive,
        mul_nonneg (show 0 ≤ p-1/2 by linarith) (sub_nonneg.mpr upper)]

theorem log_difference_budget (x y : ℝ) (nonzeroX : x ≠ 0) (nonzeroY : y ≠ 0) :
    |Real.log (|x|) - Real.log (|y|)| ≤
      (8 * powerProfile (|y|/|x|) / |x|) * |x-y| := by
  have xpos := abs_pos.mpr nonzeroX
  have ypos := abs_pos.mpr nonzeroY
  rw [abs_sub_comm, ← Real.log_div ypos.ne' xpos.ne']
  have ratio : 1 - |y| / |x| = (|x| - |y|) / |x| := by
    rw [sub_div, div_self xpos.ne']
  calc
    _ ≤ 8 * powerProfile (|y|/|x|) * |1 - (|y|/|x|)| :=
      log_ratio_bound _ (div_pos ypos xpos)
    _ = (8 * powerProfile (|y|/|x|) / |x|) * |(|x| - |y|)| := by
      rw [ratio, abs_div, abs_abs]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y)
      (div_nonneg (mul_nonneg (by norm_num) (profile_nonnegative (div_nonneg ypos.le xpos.le))) xpos.le)

private theorem profile_memLp : MemLp (fun x : ℝ => powerProfile |x|) 2 volume := by
  have envelope : MemLp powerEnvelopeRaw 2 volume := (Lp.memLp powerEnvelopeL2).ae_eq envelope_raw
  apply envelope.of_le (profile_measurable.comp (continuous_abs.measurable)).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  change ‖powerProfile |x|‖ ≤ ‖powerEnvelopeRaw x‖
  rw [Real.norm_of_nonneg (profile_nonnegative (abs_nonneg x))]
  exact envelope_norm x nonzero

private theorem memLp_scale (f : ℝ → ℝ) (domain : MemLp f 2 volume) (a : ℝ) (nonzero : a ≠ 0) :
    MemLp (fun t : ℝ => f (a*t)) 2 volume := by
  have mapped : MemLp f 2 (volume.map (fun t : ℝ => a*t)) := by
    rw [Real.map_volume_mul_left nonzero]
    exact domain.smul_measure ENNReal.ofReal_ne_top
  exact mapped.comp_of_map (by fun_prop)

theorem ratio_budget_integrable (v : BurnolL2) (x : ℝ) (nonzero : x ≠ 0) :
    Integrable (fun y : ℝ => powerProfile (|y|/|x|) * ‖v y‖) := by
  have positive := abs_pos.mpr nonzero
  have scaled : MemLp (fun y : ℝ => powerProfile (|y|/|x|)) 2 volume := by
    simpa only [abs_mul, abs_of_pos (inv_pos.mpr positive), div_eq_mul_inv, mul_comm] using
      memLp_scale _ profile_memLp |x|⁻¹ (inv_ne_zero positive.ne')
  exact scaled.integrable_mul (Lp.memLp v).norm

private def bothNorm (v : BurnolL2) (x : ℝ) : ℝ := ‖v x‖ + ‖v (-x)‖

private theorem both_norm_memLp (v : BurnolL2) : MemLp (bothNorm v) 2 volume :=
  (Lp.memLp v).norm.add ((Lp.memLp v).norm.comp_measurePreserving negMeasurePreserving)

private theorem norm_carrier_domain (v : BurnolL2) :
    MemLp (fun x => (bothNorm v x : ℂ)) 2 volume := by
  have measured : Measurable (bothNorm v) :=
    (Lp.stronglyMeasurable v).measurable.norm.add
      ((Lp.stronglyMeasurable v).measurable.norm.comp measurable_neg)
  apply (both_norm_memLp v).of_le
    (Complex.continuous_ofReal.measurable.comp measured).aestronglyMeasurable
  filter_upwards with x
  change ‖(bothNorm v x : ℂ)‖ ≤ ‖bothNorm v x‖
  rw [Complex.norm_real]

private def normCarrier (v : BurnolL2) : BurnolL2 :=
  (norm_carrier_domain v).toLp _

private theorem norm_carrier_raw (v : BurnolL2) :
    (normCarrier v : ℝ → ℂ) =ᵐ[volume] fun x => (bothNorm v x : ℂ) :=
  (norm_carrier_domain v).coeFn_toLp

private def clockWeight (t : ℝ) : ℝ := Real.exp (-Real.log t / 2) * powerProfile t

private theorem clock_weight_measurable : Measurable clockWeight :=
  (by fun_prop : Measurable (fun t : ℝ => Real.exp (-Real.log t / 2))).mul profile_measurable

private theorem clock_weight_form (t : ℝ) (positive : 0 < t) :
    clockWeight t = if t ≤ 1 then t ^ (-3/4 : ℝ) else t ^ (-5/4 : ℝ) := by
  have scale : Real.exp (-Real.log t / 2) = t ^ (-1/2 : ℝ) := by
    rw [Real.rpow_def_of_pos positive]
    congr 1
    ring
  rw [clockWeight, scale, powerProfile]
  split_ifs <;> rw [← Real.rpow_add positive] <;> norm_num

private theorem clock_weight_integrable : IntegrableOn clockWeight (Ioi 0) := by
  have first : IntegrableOn clockWeight (Ioc 0 1) := by
    apply (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : -1 < (-3/4 : ℝ))).1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
    exact (clock_weight_form t inside.1).trans (if_pos inside.2) |>.symm
  have last : IntegrableOn clockWeight (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5/4 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t above
    exact (clock_weight_form t ((by norm_num : (0 : ℝ) < 1).trans above)).trans
      (if_neg (not_le.mpr above)) |>.symm
  have cover : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← cover]
  exact first.union last

private def budgetOrbit (v : BurnolL2) (t : ℝ) : BurnolL2 :=
  (clockWeight t : ℂ) • burnolMultiplicativeDilation (Real.log t) (normCarrier v)

private theorem budget_orbit_integrable (v : BurnolL2) :
    IntegrableOn (budgetOrbit v) (Ioi 0) := by
  have orbitMeasured : StronglyMeasurable (fun t : ℝ =>
      burnolMultiplicativeDilation (Real.log t) (normCarrier v)) :=
    (burnolMultiplicativeDilation_stronglyContinuous (normCarrier v)).stronglyMeasurable.comp_measurable
      (by fun_prop)
  have measured : AEStronglyMeasurable (budgetOrbit v) (volume.restrict (Ioi 0)) :=
    ((Complex.continuous_ofReal.measurable.comp
      clock_weight_measurable).stronglyMeasurable.smul orbitMeasured).aestronglyMeasurable
  apply (integrable_norm_iff measured).mp
  apply (clock_weight_integrable.mul_const ‖normCarrier v‖).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
  have nonnegative : 0 ≤ clockWeight t :=
    mul_nonneg (Real.exp_pos _).le (profile_nonnegative (show 0 < t from positive).le)
  change clockWeight t * ‖normCarrier v‖ = ‖budgetOrbit v t‖
  rw [budgetOrbit, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonnegative,
    LinearIsometryEquiv.norm_map]

/-- A positive original dilation clock pays the absolute logarithmic difference kernel. -/
def quarterLogClockBudget (v : BurnolL2) : BurnolL2 :=
  ∫ t : ℝ in Ioi 0, budgetOrbit v t

private theorem budget_clock_raw (v : BurnolL2) :
    (quarterLogClockBudget v : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t : ℝ in Ioi 0, ((powerProfile t * bothNorm v (t*x) : ℝ) : ℂ) := by
  let raw : ℝ × ℝ → ℂ := fun p => ((powerProfile p.1 * bothNorm v (p.1*p.2) : ℝ) : ℂ)
  have measuredNorm : Measurable (bothNorm v) :=
    (Lp.stronglyMeasurable v).measurable.norm.add
      ((Lp.stronglyMeasurable v).measurable.norm.comp measurable_neg)
  have measured : Measurable raw := Complex.continuous_ofReal.measurable.comp
    ((profile_measurable.comp measurable_fst).mul (measuredNorm.comp (by fun_prop)))
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioi 0))
    (budgetOrbit v) (budget_orbit_integrable v) raw measured
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
  have positive : 0 < t := positive
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := Real.exp (Real.log t)) (Real.exp_ne_zero _)).ae_eq (norm_carrier_raw v)
  filter_upwards [Lp.coeFn_smul (clockWeight t : ℂ)
      (burnolMultiplicativeDilation (Real.log t) (normCarrier v)),
    burnolMultiplicativeDilation_coeFn (Real.log t) (normCarrier v), moved]
    with x scalar dilation read
  change (normCarrier v) (Real.exp (Real.log t)*x) =
    (bothNorm v (Real.exp (Real.log t)*x) : ℂ) at read
  rw [budgetOrbit, scalar, Pi.smul_apply, smul_eq_mul, dilation,
    burnolL2RawNormalizedDilation, read, Real.exp_log positive]
  change (clockWeight t : ℂ) * ((Real.exp (Real.log t / 2) : ℂ) *
    (bothNorm v (t*x) : ℂ)) = (powerProfile t * bothNorm v (t*x) : ℝ)
  rw [← mul_assoc]
  have scaled : clockWeight t * Real.exp (Real.log t / 2) = powerProfile t := by
    rw [clockWeight, mul_right_comm, ← Real.exp_add,
      show -Real.log t / 2 + Real.log t / 2 = 0 by ring, Real.exp_zero, one_mul]
  rw [← Complex.ofReal_mul, scaled, Complex.ofReal_mul]

private theorem section_integrable (v : BurnolL2) (x : ℝ) (nonzero : x ≠ 0) :
    IntegrableOn (fun t : ℝ => powerProfile t * bothNorm v (t*x)) (Ioi 0) := by
  have first := profile_memLp.mono_measure (Measure.restrict_le_self (s := Ioi (0 : ℝ)))
  have last := (memLp_scale _ (both_norm_memLp v) x nonzero).mono_measure
    (Measure.restrict_le_self (s := Ioi (0 : ℝ)))
  apply (first.integrable_mul last).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
  change powerProfile |t| * bothNorm v (x*t) = powerProfile t * bothNorm v (t*x)
  rw [abs_of_pos positive, mul_comm x t]

private theorem ratio_integral_change (v : BurnolL2) (x : ℝ) (nonzero : x ≠ 0) :
    (∫ y : ℝ, powerProfile (|y|/|x|) * ‖v y‖) / |x| =
      ∫ t : ℝ in Ioi 0, powerProfile t * bothNorm v (t*x) := by
  let f : ℝ → ℝ := fun y => powerProfile (|y|/|x|) * ‖v y‖
  have domain : Integrable f := ratio_budget_integrable v x nonzero
  have reflected : Integrable (fun y : ℝ => f (-y)) :=
    negMeasurePreserving.integrable_comp_of_integrable domain
  have split := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi domain
  rw [compl_Ioi] at split
  have whole : (∫ y : ℝ in Ioi 0, f y + f (-y)) = ∫ y : ℝ, f y := by
    rw [integral_add domain.integrableOn reflected.integrableOn, integral_comp_neg_Ioi,
      neg_zero, split]
  have positive := abs_pos.mpr nonzero
  have scale := integral_comp_mul_left_Ioi (fun y : ℝ => f y + f (-y)) 0 positive
  rw [mul_zero, whole] at scale
  have read :
      (∫ t : ℝ in Ioi 0, f (|x| * t) + f (-(|x| * t))) =
        ∫ t : ℝ in Ioi 0, powerProfile t * bothNorm v (t*x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t inside
    have tpos : 0 < t := inside
    have ratio : |(|x| * t)|/|x| = t := by
      rw [abs_of_pos (mul_pos positive tpos), mul_comm, mul_div_cancel_right₀ _ positive.ne']
    have evenRead : bothNorm v (|x| * t) = bothNorm v (t*x) := by
      rw [mul_comm |x| t]
      by_cases sign : 0 ≤ x
      · rw [abs_of_nonneg sign]
      · rw [abs_of_neg (lt_of_not_ge sign), mul_neg]
        simp only [bothNorm, neg_neg, add_comm]
    simp only [f, abs_neg, ratio, ← mul_add]
    exact congrArg (powerProfile t * ·) evenRead
  change (∫ y : ℝ, f y) / |x| = _
  rw [← read, scale, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem quarter_log_clock_read (v : BurnolL2) :
    (quarterLogClockBudget v : ℝ → ℂ) =ᵐ[volume]
      fun x => (((∫ y : ℝ, powerProfile (|y|/|x|) * ‖v y‖) / |x| : ℝ) : ℂ) := by
  filter_upwards [budget_clock_raw v, volume.ae_ne (0 : ℝ)] with x read nonzero
  rw [read, ratio_integral_change v x nonzero]
  exact Complex.ofRealCLM.integral_comp_comm (section_integrable v x nonzero)

end OriginalGamma.Source.WindowLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
