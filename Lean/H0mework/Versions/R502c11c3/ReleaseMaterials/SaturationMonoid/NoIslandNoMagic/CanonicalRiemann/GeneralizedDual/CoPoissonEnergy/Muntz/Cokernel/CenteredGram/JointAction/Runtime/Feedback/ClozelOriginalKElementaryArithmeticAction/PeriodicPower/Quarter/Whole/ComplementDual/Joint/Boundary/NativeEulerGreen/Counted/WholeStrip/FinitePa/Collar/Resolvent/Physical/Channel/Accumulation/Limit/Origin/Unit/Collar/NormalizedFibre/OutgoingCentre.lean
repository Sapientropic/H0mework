import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.PhysicalProjection

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter Function MeasureTheory Set BurnolPhysicalState
open scoped ENNReal

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "r₀" => ((1/4 : ℝ)/2)
local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioc 0 r₀)
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "weight" => fun c (t : ℝ) => (t : ℂ)^(s₀ c-1)
local notation "power" => fun c (x : ℝ) => ((|x| : ℝ) : ℂ)^(-s₀ c)

private theorem ofReal_cpow_measurable (z : ℂ) : Measurable (fun t : ℝ => (t : ℂ)^z) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro t ht
  have live : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
  exact (Complex.continuousAt_ofReal_cpow_const t z (Or.inr live)).continuousWithinAt

private theorem symmetric_power_integral (β t : ℝ) (below : β < 1) (positive : 0 < t) :
    let g := Set.indicator (symmetricInterval t) (fun x : ℝ => |x|^(-β))
    Integrable g volume ∧ (∫ x, g x) = 2*t^(1-β)/(1-β) := by
  dsimp only
  let f := fun x : ℝ => |x|^(-β)
  have exponent : -1 < -β := by linarith
  have right : IntervalIntegrable f volume 0 t := by
    refine (intervalIntegral.intervalIntegrable_rpow' exponent (a := 0) (b := t)).congr ?_
    intro x hx
    rw [uIoc_of_le positive.le] at hx
    exact congrArg (fun a : ℝ => a^(-β)) (abs_of_pos hx.1).symm
  have left : IntervalIntegrable f volume (-t) 0 := by
    have reflected := (IntervalIntegrable.iff_comp_neg (f := f) (a := 0) (b := t)).mp right
    simpa only [f, abs_neg, neg_zero] using reflected.symm
  have localInt : IntegrableOn f (symmetricInterval t) := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -t ≤ t)).mp (left.trans right)
  refine ⟨(integrable_indicator_iff (measurableSet_symmetricInterval t)).mpr localInt, ?_⟩
  rw [integral_indicator (measurableSet_symmetricInterval t)]
  change ∫ x in Icc (-t) t, f x = _
  rw [← restrict_Ioc_eq_restrict_Icc, ← intervalIntegral.integral_of_le (by linarith : -t ≤ t),
    ← intervalIntegral.integral_add_adjacent_intervals left right]
  have reflected : (∫ x in -t..0, f x) = ∫ x in 0..t, f x := by
    simpa only [f, abs_neg, neg_zero] using
      (intervalIntegral.integral_comp_neg (a := 0) (b := t) (f := f)).symm
  have positivePart : (∫ x in 0..t, f x) = t^(1-β)/(1-β) := by
    calc
      _ = ∫ x in 0..t, x^(-β) := by
        apply intervalIntegral.integral_congr_Ioo_of_le positive.le
        intro x hx
        dsimp only [f]
        rw [abs_of_pos hx.1]
      _ = _ := by
        rw [integral_rpow (Or.inl exponent), show -β+1=1-β by ring,
          Real.zero_rpow (sub_pos.mpr below).ne', sub_zero]
  rw [reflected, positivePart]
  ring

private def outgoingKernel (c : BurnolCompletedMellinCoordinate) (x t : ℝ) : ℂ :=
  if |x| < t then 2*power c x*weight c t else 0

private def outgoingRaw (c : BurnolCompletedMellinCoordinate) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioc 0 r₀, outgoingKernel c x t*f t

private theorem outgoing_kernel_measurable (c : BurnolCompletedMellinCoordinate) :
    Measurable (fun p : ℝ × ℝ => outgoingKernel c p.1 p.2) := by
  apply Measurable.ite (measurableSet_lt (continuous_abs.measurable.comp measurable_fst) measurable_snd)
  · exact (measurable_const.mul ((ofReal_cpow_measurable (-s₀ c)).comp
        (continuous_abs.measurable.comp measurable_fst))).mul
      ((ofReal_cpow_measurable (s₀ c-1)).comp measurable_snd)
  · exact measurable_const

private theorem outgoing_slice_bound (c : BurnolCompletedMellinCoordinate) (a : ℂ) (t : ℝ) (positive : 0 < t) :
    Integrable (fun x => outgoingKernel c x t*a) volume ∧
      (∫ x, ‖outgoingKernel c x t*a‖) ≤ (4/(1-c.value.re))*‖a‖ := by
  let β := c.value.re
  let g := Set.indicator (symmetricInterval t) (fun x : ℝ => |x|^(-β))
  let A := 2*t^(β-1)*‖a‖
  obtain ⟨bound, mass⟩ := symmetric_power_integral β t c.belowOne positive
  have majorant : Integrable (fun x => A*g x) volume := bound.const_mul A
  have comparison : ∀ᵐ x : ℝ ∂volume, ‖outgoingKernel c x t*a‖ ≤ A*g x := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
    by_cases inside : |x| < t
    · dsimp only [outgoingKernel, g, A]
      rw [if_pos inside, indicator_of_mem (show x ∈ symmetricInterval t from abs_le.mp inside.le), norm_mul, norm_mul, norm_mul,
        Complex.norm_ofNat, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr nonzero),
        Complex.norm_cpow_eq_rpow_re_of_pos positive]
      simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
      dsimp only [β]
      exact le_of_eq (by ring)
    · rw [outgoingKernel, if_neg inside, zero_mul, norm_zero]
      refine mul_nonneg (by dsimp only [A]; positivity) ?_
      exact Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) _
  have slice : Integrable (fun x => outgoingKernel c x t*a) volume :=
    majorant.mono (((outgoing_kernel_measurable c).comp (measurable_id.prodMk measurable_const)).mul
      measurable_const).aestronglyMeasurable (comparison.mono fun x hx => hx.trans (le_abs_self (A*g x)))
  refine ⟨slice, (integral_mono_ae slice.norm majorant comparison).trans_eq ?_⟩
  rw [integral_const_mul, mass]
  calc
    _ = ((4/(1-β))*‖a‖)*(t^(β-1)*t^(1-β)) := by dsimp only [A]; ring
    _ = _ := by rw [← Real.rpow_add positive, show β-1+(1-β)=0 by ring, Real.rpow_zero, mul_one]

private theorem outgoing_kernel_integrable (c : BurnolCompletedMellinCoordinate) (f : L¹) :
    Integrable (fun p : ℝ × ℝ => outgoingKernel c p.1 p.2*f p.2) ((volume : Measure ℝ).prod μ₊) := by
  let g := fun p : ℝ × ℝ => outgoingKernel c p.1 p.2*f p.2
  have measured : StronglyMeasurable g := ((outgoing_kernel_measurable c).mul
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).stronglyMeasurable
  have cap : Integrable (fun t => (4/(1-c.value.re))*‖f t‖) μ₊ :=
    ((L1.integrable_coeFn f).norm.mono_measure Measure.restrict_le_self).const_mul _
  refine (integrable_prod_iff' measured.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t member
    exact (outgoing_slice_bound c (f t) t member.1).1
  · apply cap.mono measured.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t member
    have paid := (outgoing_slice_bound c (f t) t member.1).2
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact paid.trans (le_abs_self _)

private theorem outgoing_raw_integrable (c : BurnolCompletedMellinCoordinate) (f : L¹) :
    Integrable (outgoingRaw c f) volume := (outgoing_kernel_integrable c f).integral_prod_left

private def outgoingCentreValue (c : BurnolCompletedMellinCoordinate) (f : L¹) : L¹ :=
  (outgoing_raw_integrable c f).toL1 (outgoingRaw c f)

private theorem outgoingCentreValue_read (c : BurnolCompletedMellinCoordinate) (f : L¹) :
    (outgoingCentreValue c f : ℝ → ℂ) =ᵐ[volume] outgoingRaw c f :=
  (outgoing_raw_integrable c f).coeFn_toL1

private theorem outgoing_centre_add (c : BurnolCompletedMellinCoordinate) (f g : L¹) :
    outgoingCentreValue c (f+g) = outgoingCentreValue c f+outgoingCentreValue c g := by
  apply Lp.ext
  filter_upwards [outgoingCentreValue_read c (f+g), outgoingCentreValue_read c f, outgoingCentreValue_read c g,
    Lp.coeFn_add (outgoingCentreValue c f) (outgoingCentreValue c g),
    (outgoing_kernel_integrable c f).prod_right_ae, (outgoing_kernel_integrable c g).prod_right_ae]
    with x whole left right sum leftInt rightInt
  rw [whole, sum, Pi.add_apply, left, right]
  unfold outgoingRaw
  rw [← integral_add leftInt rightInt]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_add f g)] with t add
  rw [add, Pi.add_apply, mul_add]

private theorem outgoing_centre_smul (c : BurnolCompletedMellinCoordinate) (a : ℂ) (f : L¹) :
    outgoingCentreValue c (a • f) = a • outgoingCentreValue c f := by
  apply Lp.ext
  filter_upwards [outgoingCentreValue_read c (a • f), outgoingCentreValue_read c f,
    Lp.coeFn_smul a (outgoingCentreValue c f)] with x whole read scalar
  rw [whole, scalar, Pi.smul_apply, smul_eq_mul, read]
  unfold outgoingRaw
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul a f)] with t scale
  rw [scale, Pi.smul_apply, smul_eq_mul]
  ring

private theorem outgoing_centre_bound (c : BurnolCompletedMellinCoordinate) (f : L¹) :
    ‖outgoingCentreValue c f‖ ≤ (4/(1-c.value.re))*‖f‖ := by
  let C := 4/(1-c.value.re)
  let k := fun x t => ‖outgoingKernel c x t*f t‖
  have domain := outgoing_kernel_integrable c f
  have cap : Integrable (fun t => C*‖f t‖) volume := (L1.integrable_coeFn f).norm.const_mul C
  rw [outgoingCentreValue, L1.norm_of_fun_eq_integral_norm]
  calc
    _ ≤ ∫ x, ∫ t, k x t ∂μ₊ := integral_mono_ae (outgoing_raw_integrable c f).norm
      domain.integral_norm_prod_left (Eventually.of_forall fun x => norm_integral_le_integral_norm _)
    _ = ∫ t, ∫ x, k x t ∂volume ∂μ₊ := integral_integral_swap domain.norm
    _ ≤ ∫ t, C*‖f t‖ ∂μ₊ := by
      apply integral_mono_ae domain.swap.integral_norm_prod_left (cap.mono_measure Measure.restrict_le_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t member
      exact (outgoing_slice_bound c (f t) t member.1).2
    _ ≤ ∫ t, C*‖f t‖ := setIntegral_le_integral cap (Eventually.of_forall fun t =>
      mul_nonneg (div_nonneg (by norm_num) (sub_pos.mpr c.belowOne).le) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

/-- The outward compact primitive is bounded on the actual L¹ centre. -/
def outgoingCentre (c : BurnolCompletedMellinCoordinate) : L¹ →L[ℂ] L¹ :=
  ({ toFun := outgoingCentreValue c
     map_add' := outgoing_centre_add c
     map_smul' := outgoing_centre_smul c } : L¹ →ₗ[ℂ] L¹).mkContinuous _ (outgoing_centre_bound c)

private theorem outgoing_raw_interval (c : BurnolCompletedMellinCoordinate) (f : ℝ → ℂ) (x : ℝ) :
    outgoingRaw c f x = 2*power c x*(∫ t in Ioc |x| r₀, weight c t*f t) := by
  unfold outgoingRaw
  have form : (fun t => outgoingKernel c x t*f t) =
      (Ioi |x|).indicator (fun t => 2*power c x*(weight c t*f t)) := by
    funext t
    by_cases h : |x| < t
    · rw [indicator_of_mem (show t ∈ Ioi |x| from h), outgoingKernel, if_pos h, mul_assoc]
    · rw [indicator_of_notMem (show t ∉ Ioi |x| from h), outgoingKernel, if_neg h, zero_mul]
  rw [form, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have window : Ioi |x| ∩ Ioc 0 r₀ = Ioc |x| r₀ := by
    ext t
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (abs_nonneg x).trans_lt h.1, h.2⟩⟩
  rw [window, integral_const_mul]

/-- The bounded primitive retains the exact outgoing integral of the same compact source. -/
theorem outgoing_centre_read (c : BurnolCompletedMellinCoordinate) (f : L¹) :
    ∀ᵐ x : ℝ ∂volume, outgoingCentre c f x =
      2*power c x*(∫ t in Ioc |x| r₀, weight c t*f t) := by
  filter_upwards [outgoingCentreValue_read c f] with x actual
  exact actual.trans (outgoing_raw_interval c f x)

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
