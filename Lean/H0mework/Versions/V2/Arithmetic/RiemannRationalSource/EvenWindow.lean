import H0mework.Versions.V2.Arithmetic.RiemannRationalSource.CofinalKernel

/-! The original even source and annular samples retain their full support and pairing. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem representative_abs (value : BurnolL2) (x : ℝ) :
    burnolEvenStrongRepresentative value |x| = burnolEvenStrongRepresentative value x := by
  rcases le_total 0 x with nonnegative | nonpositive
  · rw [abs_of_nonneg nonnegative]
  · rw [abs_of_nonpos nonpositive]
    unfold burnolEvenStrongRepresentative
    simp only [neg_neg, add_comm]

private theorem annulus_integral (r : ℝ → ℂ) :
    (∫ x : ℝ, if (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4 then r |x| else 0) =
      2 * ∫ x : ℝ in (1 / 4 : ℝ)..4, r x := by
  have absIntegral (f : ℝ → ℂ) :
      (∫ x : ℝ, f |x|) = 2 * ∫ x : ℝ in Ioi 0, f x := by
    have positive : (∫ x : ℝ in Ioi 0, f |x|) = ∫ x : ℝ in Ioi 0, f x := by
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun x hx => by rw [abs_of_pos hx])
    by_cases integrable : IntegrableOn (fun x => f |x|) (Ioi 0)
    · have negative : IntegrableOn (fun x => f |x|) (Iic 0) := by
        rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
        let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
        rw [m.integrableOn_map_iff]
        simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero] using
          (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi integrable)
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi negative integrable, positive,
        two_mul]
      congr 1
      rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
      exact setIntegral_congr_fun measurableSet_Iic
        (fun x hx => by rw [abs_of_nonpos hx])
    · have whole : ¬ Integrable (fun x : ℝ => f |x|) := fun h => integrable h.integrableOn
      rw [← positive, integral_undef integrable, integral_undef whole, mul_zero]
  rw [absIntegral (fun t => if (1 / 4 : ℝ) < t ∧ t ≤ 4 then r t else 0)]
  have indicator : (fun x : ℝ => if (1 / 4 : ℝ) < x ∧ x ≤ 4 then r x else 0) =
      (Ioc (1 / 4 : ℝ) 4).indicator r := by
    funext x
    simp only [Set.indicator_apply, mem_Ioc]
  rw [indicator, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (1 / 4 : ℝ) 4 ⊆ Ioi 0 from
      fun _ hx => lt_trans (by norm_num) hx.1),
    intervalIntegral.integral_of_le (by norm_num)]

theorem even_contact_inner (u v : BurnolL2)
    (uEven : reflectL2 u = u) (vEven : reflectL2 v = v)
    (support : ∀ᵐ x ∂volume, x ∉ burnolSamplingAnnulus → v x = 0) :
    inner ℂ u v = 2 * inner ℂ (contactRestriction u) (contactRestriction v) := by
  let ru := burnolEvenStrongRepresentative u
  let rv := burnolEvenStrongRepresentative v
  have uRead := burnolEvenStrongRepresentative_ae_eq u uEven
  have vRead := burnolEvenStrongRepresentative_ae_eq v vEven
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x : ℝ, if (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4 then
        star (ru |x|) * rv |x| else 0 := by
      apply integral_congr_ae
      filter_upwards [uRead, vRead, support] with x hu hv hs
      rw [← hu, ← hv]
      simp only [RCLike.inner_apply, Complex.star_def]
      rw [show ru |x| = ru x from representative_abs u x,
        show rv |x| = rv x from representative_abs v x]
      split_ifs with inside
      · ring
      · have zero : rv x = 0 := hv.trans (hs inside)
        change rv x * _ = 0
        rw [zero, zero_mul]
    _ = 2 * ∫ x : ℝ in (1 / 4)..4, star (ru x) * rv x :=
      annulus_integral (fun x => star (ru x) * rv x)
    _ = _ := by
      congr 1
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae uRead, ae_restrict_of_ae vRead,
        LpToLpRestrictCLM_coeFn ℂ (Ioc (1 / 4 : ℝ) 4) u,
        LpToLpRestrictCLM_coeFn ℂ (Ioc (1 / 4 : ℝ) 4) v] with x hu hv hru hrv
      change _ = inner ℂ (contactRestriction u x) (contactRestriction v x)
      change ru x = u x at hu
      change rv x = v x at hv
      change contactRestriction u x = u x at hru
      change contactRestriction v x = v x at hrv
      rw [hu, hv, hru, hrv]
      simp only [RCLike.inner_apply, Complex.star_def]
      ring

theorem even_contact_window_integral (v : BurnolL2) (vEven : reflectL2 v = v)
    (support : ∀ᵐ x ∂volume, x ∉ burnolSamplingAnnulus → v x = 0) :
    burnolSourceWindowIntegral v = 2 * inner ℂ
      (Lp.const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ)) (contactRestriction v) := by
  let rv := burnolEvenStrongRepresentative v
  have vRead := burnolEvenStrongRepresentative_ae_eq v vEven
  change inner ℂ (intervalConstant 4) (burnolRadiusRestriction 4 v) = _
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x : ℝ in symmetricInterval 4, v x := by
      apply integral_congr_ae
      filter_upwards [intervalConstant_coeFn (4 : ℝ),
        LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (4 : ℝ)) v] with x hc hr
      change inner ℂ (intervalConstant 4 x) (burnolRadiusRestriction 4 v x) = _
      change burnolRadiusRestriction 4 v x = v x at hr
      rw [hc, hr]
      simp
    _ = ∫ x : ℝ, v x := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [support] with x hs
      intro outside
      exact hs (fun inside => outside (abs_le.mp inside.2))
    _ = ∫ x : ℝ, if (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4 then rv |x| else 0 := by
      apply integral_congr_ae
      filter_upwards [vRead, support] with x hv hs
      change rv x = v x at hv
      rw [show rv |x| = rv x from representative_abs v x, hv]
      split_ifs with inside
      · rfl
      · exact hs inside
    _ = 2 * ∫ x : ℝ in (1 / 4)..4, rv x := annulus_integral _
    _ = _ := by
      congr 1
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae vRead,
        Lp.coeFn_const 2 (volume.restrict (Ioc (1 / 4 : ℝ) 4)) (1 : ℂ),
        LpToLpRestrictCLM_coeFn ℂ (Ioc (1 / 4 : ℝ) 4) v] with x hv hc hr
      change rv x = inner ℂ _ (contactRestriction v x)
      change rv x = v x at hv
      change contactRestriction v x = v x at hr
      rw [hv, hc, hr]
      simp

theorem pa_tate_source_annulus (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    ∀ᵐ x ∂volume, x ∉ burnolSamplingAnnulus →
      burnolTateReciprocalL2 (burnolMobiusSourceL2 p) x = 0 := by
  let sigma := burnolTateReciprocalL2 (burnolMobiusSourceL2 p)
  have innerGap := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp
    (burnolTateMobiusSource_innerGap p)
  have outerRead := burnolRadiusZeroExtension_coe
    (burnolMobiusWindowSourceRead (evenFaceFourierEquiv burnolUnscaledCommonGapRadius p))
  rw [show burnolRadiusZeroExtension 4
      (burnolMobiusWindowSourceRead (evenFaceFourierEquiv burnolUnscaledCommonGapRadius p)) = sigma from
      burnolMobiusSource_fourier p inside] at outerRead
  filter_upwards [innerGap, outerRead] with x inner outer
  intro outside
  change sigma x = 0
  by_cases low : |x| ≤ (1 / 4 : ℝ)
  · exact inner (abs_le.mp low)
  · have high : x ∉ symmetricInterval (4 : ℝ) := by
      intro bound
      exact outside ⟨lt_of_not_ge low, abs_le.mpr bound⟩
    rw [outer, indicator_of_notMem high]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
