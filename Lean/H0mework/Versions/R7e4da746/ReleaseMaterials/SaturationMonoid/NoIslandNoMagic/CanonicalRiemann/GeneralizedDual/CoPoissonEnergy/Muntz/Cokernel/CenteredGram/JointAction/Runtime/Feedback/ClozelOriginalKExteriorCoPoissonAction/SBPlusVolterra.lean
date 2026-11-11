import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.RVolterra
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Window
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.ReverseRank

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorSBPlusVolterra
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalKExteriorCoPoissonAction OriginalKExteriorRVolterra
open OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def sourceRate (c : BurnolCompletedMellinCoordinate) : ℂ := c.value + star c.value - 1

theorem sourceRate_ne_zero (c : BurnolCompletedMellinCoordinate) : sourceRate c ≠ 0 := by
  intro zero
  have real := congrArg Complex.re zero
  norm_num [sourceRate, Complex.star_def] at real
  linarith [c.rightHalf]

def tailProfile (c : BurnolCompletedMellinCoordinate) (h t : ℝ) : ℂ :=
  (t : ℂ) ^ (-c.value) * burnolRieszReturnRaw c (Real.exp (-h) * t)

def tailForcing (c : BurnolCompletedMellinCoordinate) (h t : ℝ) : ℂ :=
  (t : ℂ) ^ (-c.value) * returnForce c (Real.exp (-h) * t)

def sourceEndpoint (c : BurnolCompletedMellinCoordinate) (h t : ℝ) : ℂ :=
  (t : ℂ) ^ (1 - c.value) * burnolRieszReturnRaw c (Real.exp (-h) * t)

def tailMoment (c : BurnolCompletedMellinCoordinate) (h a b : ℝ) : ℂ :=
  (sourceRate c)⁻¹ *
    ((∫ t : ℝ in a..b, tailForcing c h t) - sourceEndpoint c h b + sourceEndpoint c h a)

private theorem sourceEndpoint_derivative (c : BurnolCompletedMellinCoordinate) (h t : ℝ)
    (positive : 0 < t) :
    HasDerivAt (sourceEndpoint c h)
      (tailForcing c h t - sourceRate c * tailProfile c h t) t := by
  have powerDerivative := burnolMellinTailPower_hasDerivAt (c.value - 1) positive
  have exponent : -(c.value - 1) = 1 - c.value := by ring
  have nextExponent : -((c.value - 1) + 1) = -c.value := by ring
  simp only [exponent, nextExponent] at powerDerivative
  have argument : HasDerivAt (fun u : ℝ => Real.exp (-h) * u) (Real.exp (-h)) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (Real.exp (-h))
  have generated := powerDerivative.mul ((burnolRieszReturnRaw_hasDerivAt c _).scomp t argument)
  simp only [Function.comp_apply, Complex.real_smul] at generated
  convert! generated using 1
  have power : (t : ℂ) ^ (1 - c.value) = (t : ℂ) * (t : ℂ) ^ (-c.value) := by
    rw [show 1 - c.value = 1 + -c.value by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), Complex.cpow_one]
  have source := actual_return_source_ODE c (Real.exp (-h) * t)
  simp only [Complex.ofReal_mul] at source
  unfold sourceRate tailForcing tailProfile
  rw [power, ← source]
  ring

theorem finite_tail_forcing (c : BurnolCompletedMellinCoordinate) (h a b : ℝ)
    (positive : 0 < a) (ordered : a ≤ b) :
    (∫ t : ℝ in a..b, tailProfile c h t) = tailMoment c h a b := by
  have profileRegular : ContinuousOn (tailProfile c h) (Icc a b) := by
    intro t inside
    have nonzero : t ≠ 0 := ne_of_gt (positive.trans_le inside.1)
    exact ((Complex.continuousAt_ofReal_cpow_const t (-c.value) (Or.inr nonzero)).mul
      ((burnolRieszReturnRaw_continuous c).continuousAt.comp
        (continuousAt_const.mul continuousAt_id))).continuousWithinAt
  have forcingRegular : ContinuousOn (tailForcing c h) (Icc a b) := by
    intro t inside
    have nonzero : t ≠ 0 := ne_of_gt (positive.trans_le inside.1)
    have regularForce : Continuous (returnForce c) := by
      unfold returnForce
      exact ((((Edge.raw_continuous q).const_mul _).sub
        ((burnolRadiusTruncatedFourierRaw_continuous (Response.u : BurnolQuarterIntervalL2)).const_mul _)).add
        ((burnolRadiusTruncatedFourierRaw_continuous (Response.v : BurnolQuarterIntervalL2)).const_mul _)).sub continuous_const
    exact ((Complex.continuousAt_ofReal_cpow_const t (-c.value) (Or.inr nonzero)).mul
      (regularForce.continuousAt.comp (continuousAt_const.mul continuousAt_id))).continuousWithinAt
  have first : IntervalIntegrable (tailForcing c h) volume a b :=
    forcingRegular.intervalIntegrable_of_Icc ordered
  have second : IntervalIntegrable (fun t => sourceRate c * tailProfile c h t) volume a b :=
    (profileRegular.const_mul _).intervalIntegrable_of_Icc ordered
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t inside => by
      apply sourceEndpoint_derivative c h t
      have bound : t ∈ Icc a b := by simpa only [uIcc_of_le ordered] using inside
      exact positive.trans_le bound.1)
    (first.sub second)
  rw [intervalIntegral.integral_sub first second, intervalIntegral.integral_const_mul] at actual
  have weighted : sourceRate c * (∫ t : ℝ in a..b, tailProfile c h t) =
      (∫ t : ℝ in a..b, tailForcing c h t) - sourceEndpoint c h b + sourceEndpoint c h a := by
    linear_combination -actual
  unfold tailMoment
  rw [← weighted, ← mul_assoc, inv_mul_cancel₀ (sourceRate_ne_zero c), one_mul]

theorem actual_source_tail (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (x : ℝ) (positive : 0 < x) :
    burnolRadiusMellinTailEvaluator x positive c.value c.rightHalf (exteriorSource c h 1) =
      (Real.exp (-h / 2) : ℂ) *
        ∫ t : ℝ in Ioc (max x q) (q * Real.exp h), tailProfile c h t := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  have source :
      (∫ t : ℝ in Ioi x, (t : ℂ) ^ (-c.value) * exteriorSource c h 1 t) =
        ∫ t : ℝ in Ioi x, (Real.exp (-h / 2) : ℂ) *
          (Ioc q (q * Real.exp h)).indicator (tailProfile c h) t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (actual_source_raw c h nonnegative 1),
      ae_restrict_mem measurableSet_Ioi] with t actual inside
    have tPositive : 0 < t := positive.trans inside
    rw [actual]
    unfold shellRaw
    rw [abs_of_pos tPositive]
    by_cases active : t ∈ Ioc q (q * Real.exp h)
    · rw [if_pos (show q < t ∧ t ≤ q * Real.exp h from active), indicator_of_mem active]
      change _ = (Real.exp (-h / 2) : ℂ) * ((t : ℂ) ^ (-c.value) * burnolRieszReturnRaw c (Real.exp (-h) * t))
      simp only [sourceProfile, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    · rw [if_neg (show ¬(q < t ∧ t ≤ q * Real.exp h) from active),
        indicator_of_notMem active, mul_zero, mul_zero]
  rw [source, integral_const_mul, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have intersection : Ioc q (q * Real.exp h) ∩ Ioi x = Ioc (max x q) (q * Real.exp h) := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
    tauto
  rw [intersection]

def plusRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  if |x| < q * Real.exp h then
    -(2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (c.value - 1) * (Real.exp (-h / 2) : ℂ) *
      tailMoment c h (max |x| q) (q * Real.exp h)
  else 0

private theorem source_even (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    reflectL2 (exteriorSource c h 1) = exteriorSource c h 1 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (exteriorSource c h 1) negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae (actual_source_raw c h nonnegative 1),
    actual_source_raw c h nonnegative 1] with x reflected negative direct
  change reflectL2 (exteriorSource c h 1) x = exteriorSource c h 1 (-x) at reflected
  rw [reflected, negative, direct]
  simp only [shellRaw, abs_neg]

theorem actual_SB_Rplus_source (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    (FiniteMobiusResolventFlux.Rplus (c.value / 2) (exteriorSource c h 1) : ℝ → ℂ) =ᵐ[volume]
      plusRaw c h := by
  let value := FiniteMobiusResolventFlux.Rplus (c.value / 2) (exteriorSource c h 1)
  have right : 1 / 4 < (c.value / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have same : sourceVolterraResolvent c (exteriorSource c h 1) = value := by
    exact (FiniteMobiusResolventFlux.Rplus_tate (c.value / 2) right (exteriorSource c h 1)).symm
  have positiveProfile : ∀ᵐ x ∂volume, ∀ positive : 0 < x, value x = plusRaw c h x := by
    have original := sourceVolterraResolvent_positive_profile c (exteriorSource c h 1)
    rw [same] at original
    filter_upwards [original] with x profile positive
    rw [profile positive, actual_source_tail c h nonnegative x positive]
    by_cases inside : x < q * Real.exp h
    · have lowerPositive : 0 < max x q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      have ordered : max x q ≤ q * Real.exp h := max_le inside.le (by
        have scale := Real.one_le_exp_iff.mpr nonnegative
        nlinarith)
      rw [← intervalIntegral.integral_of_le ordered, finite_tail_forcing c h _ _ lowerPositive ordered]
      simp only [plusRaw, abs_of_pos positive, if_pos inside]
      ring
    · have empty : Ioc (max x q) (q * Real.exp h) = ∅ := by
        ext t
        simp only [mem_Ioc, mem_empty_iff_false, iff_false]
        rintro ⟨lower, upper⟩
        have bound := le_max_left x q
        linarith
      rw [empty, setIntegral_empty, mul_zero, plusRaw, abs_of_pos positive, if_neg inside]
      simp only [mul_zero]
  have even : reflectL2 value = value :=
    FiniteMobiusResolventFlux.Rplus_even c (exteriorSource c h 1) (source_even c h nonnegative)
  have reflected := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
  change (reflectL2 value : ℝ → ℂ) =ᵐ[volume] fun x => value (-x) at reflected
  rw [even] at reflected
  filter_upwards [positiveProfile, negMeasurePreserving.quasiMeasurePreserving.ae positiveProfile,
    reflected, volume.ae_ne (0 : ℝ)] with x direct negative reflection nonzero
  change value x = plusRaw c h x
  rcases lt_or_gt_of_ne nonzero with negativeX | positiveX
  · rw [reflection, negative (by linarith)]
    simp only [plusRaw, abs_neg]
  · exact direct positiveX

end
end OriginalKExteriorSBPlusVolterra
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
