import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

 theorem measurable_innerBand (h : ℝ) : MeasurableSet (innerBand h) :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)
 theorem measurable_outerBand (h : ℝ) : MeasurableSet (outerBand h) :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

 theorem normalized_source_band_membership (h x : ℝ) :
    Real.exp (-h)*x∈innerBand h ↔ x∈outerBand h := by
  change (1/4:ℝ)*Real.exp (-h) < |Real.exp (-h)*x| ∧ |Real.exp (-h)*x|≤(1/4:ℝ) ↔
    (1/4:ℝ) < |x| ∧ |x|≤(1/4:ℝ)*Real.exp h
  rw [abs_mul,abs_of_pos (Real.exp_pos _),mul_comm (1/4:ℝ) (Real.exp (-h))]
  have first : Real.exp (-h)*(1/4:ℝ)<Real.exp (-h)*|x| ↔ (1/4:ℝ) < |x| := mul_lt_mul_iff_right₀ (Real.exp_pos _)
  rw [first,Real.exp_neg]
  rw [mul_comm ((Real.exp h)⁻¹) |x|,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos h)]

-- The original two-sided band, not its total mean, is transported with the actual Lebesgue Jacobian.
theorem source_band_change (h : ℝ) (f : ℝ→ℂ) :
    (∫ x : ℝ in outerBand h,f (Real.exp (-h)*x))=
      (Real.exp h:ℂ)*(∫ y : ℝ in innerBand h,f y) := by
  rw [← integral_indicator (measurable_outerBand h),← integral_indicator (measurable_innerBand h)]
  have source : (fun x =>(outerBand h).indicator (fun x=>f (Real.exp (-h)*x)) x)=
      fun x =>((innerBand h).indicator f) (Real.exp (-h)*x) := by
    funext x
    by_cases inside : x∈outerBand h
    · rw [indicator_of_mem inside,indicator_of_mem ((normalized_source_band_membership h x).mpr inside)]
    · rw [indicator_of_notMem inside,indicator_of_notMem (fun after=>inside ((normalized_source_band_membership h x).mp after))]
  rw [source,Measure.integral_comp_mul_left]
  rw [Real.exp_neg,inv_inv,abs_of_pos (Real.exp_pos h)]
  rfl

 theorem actual_source_weight_scale (h x : ℝ) (s : ℂ) :
    ((|x|:ℝ):ℂ)^s=(Real.exp h:ℂ)^s*((|Real.exp (-h)*x|:ℝ):ℂ)^s := by
  have source : |x|=Real.exp h*|Real.exp (-h)*x| := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _),← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  rw [source,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le (abs_nonneg _)]

 theorem weighted_source_band_change (h : ℝ) (f : ℝ→ℂ) (s : ℂ) :
    (∫ x : ℝ in outerBand h,f (Real.exp (-h)*x)*((|x|:ℝ):ℂ)^s)=
      ((Real.exp h:ℂ)*(Real.exp h:ℂ)^s)*(∫ y : ℝ in innerBand h,f y*((|y|:ℝ):ℂ)^s) := by
  have source : (∫ x : ℝ in outerBand h,f (Real.exp (-h)*x)*((|x|:ℝ):ℂ)^s)=
      (∫ x : ℝ in outerBand h,(Real.exp h:ℂ)^s*(f (Real.exp (-h)*x)*((|Real.exp (-h)*x|:ℝ):ℂ)^s)) := by
    apply setIntegral_congr_fun (measurable_outerBand h)
    intro x _
    dsimp only
    rw [actual_source_weight_scale h x s]
    ring
  rw [source,integral_const_mul,source_band_change h (fun y=>f y*((|y|:ℝ):ℂ)^s)]
  ring

 theorem half_density_weight_character (coordinate : ℂ) (h : ℝ) :
    (Real.exp (-h/2):ℂ)*((Real.exp h:ℂ)*(Real.exp h:ℂ)^(coordinate-1))=
      fullMellinTranslationCharacter coordinate (-h) := by
  have power : (Real.exp h:ℂ)^(coordinate-1)=Complex.exp ((h:ℂ)*(coordinate-1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),← Complex.ofReal_log (Real.exp_pos h).le,Real.log_exp]
  rw [power,Complex.ofReal_exp,Complex.ofReal_exp]
  unfold fullMellinTranslationCharacter
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
