import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.SawtoothSource
import H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.GeneratorResolventOperator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalUnitMellinSource.Resolvent
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
private theorem mellin_source_ae (f g : ℝ → ℂ) (z m : ℂ)
    (same : f =ᵐ[volume.restrict (Ioi 0)] g) (source : HasMellin g z m) : HasMellin f z m := by
  have weighted : (fun x : ℝ => (x : ℂ) ^ (z - 1) * f x) =ᵐ[volume.restrict (Ioi 0)]
      fun x : ℝ => (x : ℂ) ^ (z - 1) * g x := by
    filter_upwards [same] with x actual
    rw [actual]
  refine ⟨source.1.congr weighted.symm, ?_⟩
  exact (integral_congr_ae weighted).trans source.2

private theorem power_measurable (z : ℂ) : Measurable (fun x : ℝ => (x : ℂ) ^ z) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  exact (Complex.continuousAt_ofReal_cpow_const x z (Or.inr (by simpa using outside))).continuousWithinAt

private theorem scaled_mellin (f : ℝ → ℂ) (z m w : ℂ) (a : ℝ) (positive : 0 < a)
    (source : HasMellin f z m) :
    HasMellin (fun x : ℝ => w * f (a * x)) z (w * (a : ℂ) ^ (-z) * m) := by
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using
      ((MellinConvergent.comp_mul_left positive).mpr source.1).const_smul w
  · rw [show (fun x : ℝ => w * f (a * x)) = (fun x : ℝ => w • f (a * x)) from rfl,
      mellin_const_smul, mellin_comp_mul_left f z positive, source.2]
    simp only [smul_eq_mul]
    ring

private theorem scaled_norm_integral (f : ℝ → ℂ) (z w : ℂ) (a : ℝ) (positive : 0 < a) :
    (∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (z - 1) * (w * f (a * x))‖) =
      ‖w * (a : ℂ) ^ (-z)‖ * (∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (z - 1) * f x‖) := by
  have nonzero : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have relation (x : ℝ) (xpositive : 0 < x) :
      (x : ℂ) ^ (z - 1) * (w * f (a * x)) =
        (w * (a : ℂ) ^ (1 - z)) * ((↑(a * x) : ℂ) ^ (z - 1) * f (a * x)) := by
    rw [ofReal_mul, Complex.mul_cpow_ofReal_nonneg positive.le xpositive.le]
    have inverse : (a : ℂ) ^ (1 - z) * (a : ℂ) ^ (z - 1) = 1 := by
      rw [← cpow_add _ _ nonzero, sub_add_sub_cancel, sub_self, cpow_zero]
    calc
      _ = (w * ((a : ℂ) ^ (1 - z) * (a : ℂ) ^ (z - 1))) *
          ((x : ℂ) ^ (z - 1) * f (a * x)) := by rw [inverse]; ring
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x inside => congrArg norm (relation x inside))]
  simp_rw [norm_mul]
  rw [integral_const_mul, integral_comp_mul_left_Ioi
    (fun x : ℝ => ‖(x : ℂ) ^ (z - 1)‖ * ‖f x‖) 0 positive, mul_zero]
  have factor : (a : ℂ) ^ (1 - z) = (a : ℂ) ^ (-z) * (a : ℂ) := by
    rw [show (1 - z : ℂ) = -z + 1 by ring, cpow_add _ _ nonzero, cpow_one]
  rw [factor]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  simp only [smul_eq_mul]
  field_simp [positive.ne']

private theorem scaled_joint_integrable (value : BurnolL2) (z m : ℂ)
    (weight : ℝ → ℂ) (scale : ℝ → ℝ) (weightMeasured : Measurable weight)
    (scaleMeasured : Measurable scale) (scalePositive : ∀ a : ℝ, 0 < a → 0 < scale a)
    (source : HasMellin (value : ℝ → ℂ) z m)
    (budget : IntegrableOn (fun a : ℝ => ‖weight a * (scale a : ℂ) ^ (-z)‖) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (z - 1) *
        (weight p.1 * value (scale p.1 * p.2)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have measured : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (z - 1) *
      (weight p.1 * value (scale p.1 * p.2))) :=
    ((power_measurable (z - 1)).comp measurable_snd).mul
      ((weightMeasured.comp measurable_fst).mul
        ((Lp.stronglyMeasurable value).measurable.comp
          ((scaleMeasured.comp measurable_fst).mul measurable_snd)))
  apply (integrable_prod_iff measured.aestronglyMeasurable).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a inside
    exact (scaled_mellin _ z m (weight a) (scale a) (scalePositive a inside) source).1
  · apply (budget.mul_const (∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (z - 1) * value x‖)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a inside
    exact (scaled_norm_integral _ z (weight a) (scale a) (scalePositive a inside)).symm

private theorem bochner_scaled_mellin (value : BurnolL2) (z m : ℂ)
    (family : ℝ → BurnolL2) (familyIntegrable : IntegrableOn family (Ioi 0))
    (weight : ℝ → ℂ) (scale : ℝ → ℝ) (weightMeasured : Measurable weight)
    (scaleMeasured : Measurable scale) (scalePositive : ∀ a : ℝ, 0 < a → 0 < scale a)
    (reads : ∀ᵐ a : ℝ ∂volume.restrict (Ioi 0),
      (family a : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => weight a * value (scale a * x))
    (source : HasMellin (value : ℝ → ℂ) z m)
    (budget : IntegrableOn (fun a : ℝ => ‖weight a * (scale a : ℂ) ^ (-z)‖) (Ioi 0)) :
    HasMellin ((∫ a : ℝ in Ioi 0, family a) : BurnolL2) z
      ((∫ a : ℝ in Ioi 0, weight a * (scale a : ℂ) ^ (-z)) * m) := by
  have rawMeasured : Measurable (fun p : ℝ × ℝ => weight p.1 * value (scale p.1 * p.2)) :=
    (weightMeasured.comp measurable_fst).mul
      ((Lp.stronglyMeasurable value).measurable.comp
        ((scaleMeasured.comp measurable_fst).mul measurable_snd))
  have raw := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioi 0)) family familyIntegrable
    (fun p : ℝ × ℝ => weight p.1 * value (scale p.1 * p.2)) rawMeasured reads
  have joint := scaled_joint_integrable value z m weight scale weightMeasured scaleMeasured
    scalePositive source budget
  have weighted : (fun x : ℝ => (x : ℂ) ^ (z - 1) *
      ((∫ a : ℝ in Ioi 0, family a) : BurnolL2) x) =ᵐ[volume.restrict (Ioi 0)]
      fun x : ℝ => ∫ a : ℝ in Ioi 0,
        (x : ℂ) ^ (z - 1) * (weight a * value (scale a * x)) := by
    filter_upwards [ae_restrict_of_ae raw] with x actual
    rw [actual, integral_const_mul]
  refine ⟨joint.integral_prod_right.congr weighted.symm, ?_⟩
  change (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (z - 1) *
    ((∫ a : ℝ in Ioi 0, family a) : BurnolL2) x) = _
  rw [integral_congr_ae weighted, ← integral_integral_swap joint]
  have rows : (fun a : ℝ => ∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (z - 1) * (weight a * value (scale a * x))) =ᵐ[
      volume.restrict (Ioi 0)] fun a : ℝ => weight a * (scale a : ℂ) ^ (-z) * m := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a inside
    exact (scaled_mellin _ z m (weight a) (scale a) (scalePositive a inside) source).2
  rw [integral_congr_ae rows, integral_mul_const]


private def weight (c:BurnolCompletedMellinCoordinate) (t:ℝ):ℂ :=
  -Complex.exp (-(c.value/2)*(t:ℂ))
private def scale (t:ℝ):ℝ := Real.exp (-t/2)

private theorem actual_coefficient (c:BurnolCompletedMellinCoordinate) (z:ℂ) (t:ℝ):
    weight c t*(scale t:ℂ)^(-z) = -Complex.exp (((z-c.value)/2)*(t:ℂ)) := by
  unfold weight scale
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ←Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
  rw [neg_mul,←Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem actual_raw (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) (t:ℝ):
    (-burnolDirectRightResolventIntegrand (c.value/2) v t:BurnolL2)=ᵐ[volume]
      fun x:ℝ=>weight c t*v (scale t*x) := by
  filter_upwards [Lp.coeFn_neg (burnolDirectRightResolventIntegrand (c.value/2) v t),
    Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight (c.value/2) t)
      (burnolMultiplicativeDilation (-t/2) v),
    burnolMultiplicativeDilation_coeFn (-t/2) v] with x negative scalar dilation
  rw [negative]
  change -((positiveMellinQuarterRightResolventWeight (c.value/2) t •
    burnolMultiplicativeDilation (-t/2) v:BurnolL2) x)=_
  rw [scalar,Pi.smul_apply,smul_eq_mul,dilation,burnolL2RawNormalizedDilation]
  unfold positiveMellinQuarterRightResolventWeight weight scale
  rw [←mul_assoc,Complex.ofReal_exp,←Complex.exp_add]
  have expo:(1/4-c.value/2)*(t:ℂ)+((-t/2)/2:ℝ)=-(c.value/2)*(t:ℂ):=by push_cast;ring
  rw [expo]
  ring

/-- Complete original right-resolvent Mellin scalar, with its Fubini budget in the actual half-strip. -/
theorem actual_R_mellin (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) (z m:ℂ)
    (source:HasMellin (v:ℝ→ℂ) z m) (between:z.re<c.value.re):
    HasMellin (burnolDirectRightResolvent (c.value/2) v:ℝ→ℂ) z (2/(z-c.value)*m) := by
  have right:1/4<(c.value/2).re:=by rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have decay:((z-c.value)/2).re<0:=by rw [Complex.div_re];norm_num;linarith
  have budget:IntegrableOn (fun t:ℝ=>‖weight c t*(scale t:ℂ)^(-z)‖) (Ioi 0):=by
    simp_rw [actual_coefficient,norm_neg]
    exact (integrableOn_exp_mul_complex_Ioi decay 0).norm
  have wm:Measurable (weight c):=by unfold weight;fun_prop
  have sm:Measurable scale:=by unfold scale;fun_prop
  have generated:=bochner_scaled_mellin v z m
    (fun t:ℝ=> -burnolDirectRightResolventIntegrand (c.value/2) v t)
    (burnolDirectRightResolventIntegrand_integrableOn _ right v).neg
    (weight c) scale wm sm (fun t _=>Real.exp_pos _) (Eventually.of_forall (actual_raw c v))
    source budget
  have integralEq:(∫ t:ℝ in Ioi 0,-burnolDirectRightResolventIntegrand (c.value/2) v t)=
      burnolDirectRightResolvent (c.value/2) v:=by
    rw [integral_neg];rfl
  rw [integralEq] at generated
  have value:(∫ t:ℝ in Ioi 0,weight c t*(scale t:ℂ)^(-z))=2/(z-c.value):=by
    simp_rw [actual_coefficient]
    rw [integral_neg,integral_exp_mul_complex_Ioi decay 0]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
    have nonzero:z-c.value≠0:=by
      intro zero
      have realPart:=congrArg Complex.re zero
      simp only [sub_re,zero_re] at realPart
      linarith
    field_simp [nonzero]
  rw [value] at generated
  exact generated

end OriginalUnitMellinSource.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
