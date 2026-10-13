import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.FiniteKernel
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.BoundaryStates
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
local notation "μ" => (volume.restrict (symmetricInterval 1) : Measure ℝ)
local instance finiteReadUnit : IsFiniteMeasure μ where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

def reactionKernel (t x y : ℝ) : ℂ := (t:ℂ)*(cosineRaw t x*cosineRaw t y-sineRaw t x*sineRaw t y)

theorem reaction_kernel_point_bound (q r t x y : ℝ) (inside : t ∈ uIoc q r) :
    ‖reactionKernel t x y‖ ≤ 8*(|q|+|r|) := by
  have tBound : |t|≤|q|+|r| := by
    rcases le_total q r with ordered | ordered
    · rw [uIoc_of_le ordered] at inside
      exact abs_le.mpr ⟨by linarith [neg_abs_le q,inside.1,abs_nonneg r],by linarith [le_abs_self r,inside.2,abs_nonneg q]⟩
    · rw [uIoc_of_ge ordered] at inside
      exact abs_le.mpr ⟨by linarith [neg_abs_le r,inside.1,abs_nonneg q],by linarith [le_abs_self q,inside.2,abs_nonneg r]⟩
  unfold reactionKernel
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have parts := norm_sub_le (cosineRaw t x*cosineRaw t y) (sineRaw t x*sineRaw t y)
  rw [norm_mul,norm_mul] at parts
  have cx := burnolRadiusBoundaryCosineRaw_norm_le_two t x
  have cy := burnolRadiusBoundaryCosineRaw_norm_le_two t y
  have sx := sine_norm_le t x
  have sy := sine_norm_le t y
  change ‖cosineRaw t x‖≤2 at cx
  change ‖cosineRaw t y‖≤2 at cy
  have total : ‖cosineRaw t x*cosineRaw t y-sineRaw t x*sineRaw t y‖≤8 := by
    nlinarith [norm_nonneg (cosineRaw t x),norm_nonneg (cosineRaw t y),norm_nonneg (sineRaw t x),norm_nonneg (sineRaw t y)]
  nlinarith [abs_nonneg t,norm_nonneg (cosineRaw t x*cosineRaw t y-sineRaw t x*sineRaw t y)]

-- Every Hilbert test reads the same finite rank source programme, including the odd channel.
theorem full_square_finite (q r : ℝ) (qPositive : 0<q) (rPositive : 0<r) (f : H) :
    burnolRechartedTruncatedFourierOperator r (burnolRechartedTruncatedFourierOperator r f) -
      burnolRechartedTruncatedFourierOperator q (burnolRechartedTruncatedFourierOperator q f) =
      ∫ t : ℝ in q..r, rawReaction t f := by
  apply ext_inner_left ℂ
  intro test
  change (innerSL ℂ test) _ = (innerSL ℂ test) _
  rw [← (innerSL ℂ test).intervalIntegral_comp_comm ((reaction_continuous f).intervalIntegrable q r)]
  change inner ℂ test _ = ∫ t : ℝ in q..r, inner ℂ test (rawReaction t f)
  rw [burnolRechartedTruncatedFourierOperator_of_pos rPositive,burnolRechartedTruncatedFourierOperator_of_pos qPositive]
  rw [L2.inner_def]
  have actual := square_finite_raw q r qPositive rPositive f
  have leftRead : (∫ x : ℝ, inner ℂ (test x)
      ((burnolRadiusRechartedTruncatedFourier rPositive (burnolRadiusRechartedTruncatedFourier rPositive f) -
      burnolRadiusRechartedTruncatedFourier qPositive (burnolRadiusRechartedTruncatedFourier qPositive f)) x) ∂μ) =
      ∫ x : ℝ, star (test x) * ∫ y : ℝ, (∫ t : ℝ in q..r,reactionKernel t x y)*f y ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards [actual] with x read
    rw [read]
    simp only [RCLike.inner_apply,starRingEnd_apply,reactionKernel]
    ring
  rw [leftRead]
  -- The finite source integral commutes with the two actual L2 pairings.
  have innerRead (t : ℝ) : inner ℂ test (rawReaction t f) =
      ∫ x : ℝ,star (test x)*∫ y : ℝ,reactionKernel t x y*f y ∂μ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [reaction_coe t f] with x read
    rw [read]
    simp only [reactionKernel,RCLike.inner_apply,starRingEnd_apply]
    ring
  simp only [innerRead]
  have pairInt : Integrable (fun xy : ℝ×ℝ => ‖test xy.1‖*‖f xy.2‖) ((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1))) :=
    (burnolUnitState_integrable test).norm.mul_prod (burnolUnitState_integrable f).norm
  let : IsFiniteMeasure (volume.restrict (uIoc q r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (by simp [Real.volume_uIoc])⟩
  have allInt : Integrable (fun txy : ℝ×(ℝ×ℝ) =>
      star (test txy.2.1)*reactionKernel txy.1 txy.2.1 txy.2.2*f txy.2.2)
      ((volume.restrict (uIoc q r)).prod ((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1)))) := by
    have majorant := (pairInt.comp_snd (volume.restrict (uIoc q r))).const_mul (8*(|q|+|r|))
    apply majorant.mono'
    · have kernelContinuous : Continuous (fun txy : ℝ×(ℝ×ℝ) => reactionKernel txy.1 txy.2.1 txy.2.2) := by
        unfold reactionKernel cosineRaw sineRaw burnolRadiusBoundaryCosineRaw
        fun_prop
      exact ((Lp.memLp test).aestronglyMeasurable.comp_fst.comp_snd).star.mul
        (kernelContinuous.aestronglyMeasurable) |>.mul ((Lp.memLp f).aestronglyMeasurable.comp_snd.comp_snd)
    · have tLocated : ∀ᵐ txy ∂((volume.restrict (uIoc q r)).prod ((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1)))), txy.1 ∈ uIoc q r := by
        apply (Measure.ae_prod_iff_ae_ae (measurableSet_uIoc.preimage measurable_fst)).mpr
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
        exact Filter.Eventually.of_forall (fun _ => ht)
      filter_upwards [tLocated] with txy located
      have source := reaction_kernel_point_bound q r txy.1 txy.2.1 txy.2.2 located
      rw [norm_mul,norm_mul,norm_star]
      have first := mul_le_mul_of_nonneg_left source (norm_nonneg (test txy.2.1))
      have both := mul_le_mul_of_nonneg_right first (norm_nonneg (f txy.2.2))
      exact both.trans_eq (by ring)
  have swap := intervalIntegral_integral_swap (a := q) (b := r)
    (f := fun (t : ℝ) (xy : ℝ×ℝ) => star (test xy.1)*reactionKernel t xy.1 xy.2*f xy.2) allInt
  have orientedInt : Integrable (fun xy : ℝ×ℝ =>
      ∫ t : ℝ in q..r,star (test xy.1)*reactionKernel t xy.1 xy.2*f xy.2)
      ((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1))) := by
    have rawInt := allInt.swap.integral_prod_left
    have scaled : Integrable (fun xy : ℝ×ℝ => (if q≤r then (1:ℝ) else -1) •
        ∫ t : ℝ in uIoc q r,star (test xy.1)*reactionKernel t xy.1 xy.2*f xy.2 ∂volume)
        ((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1))) :=
      rawInt.smul (if q≤r then (1:ℝ) else -1)
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc] using scaled
  have lhsPair : (∫ x : ℝ, star (test x)*∫ y : ℝ,(∫ t : ℝ in q..r,reactionKernel t x y)*f y ∂μ ∂μ) =
      ∫ xy : ℝ×ℝ,(∫ t : ℝ in q..r,star (test xy.1)*reactionKernel t xy.1 xy.2*f xy.2)
        ∂((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1))) := by
    simp_rw [← integral_const_mul,← intervalIntegral.integral_mul_const,← intervalIntegral.integral_const_mul]
    simpa only [mul_assoc] using integral_integral (f := fun x y : ℝ => ∫ t : ℝ in q..r,star (test x)*reactionKernel t x y*f y) orientedInt
  have rhsPair : (∫ t : ℝ in q..r,∫ x : ℝ,star (test x)*∫ y : ℝ,reactionKernel t x y*f y ∂μ ∂μ) =
      ∫ t : ℝ in q..r,(∫ xy : ℝ×ℝ,star (test xy.1)*reactionKernel t xy.1 xy.2*f xy.2
        ∂((volume.restrict (symmetricInterval 1)).prod (volume.restrict (symmetricInterval 1)))) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have actual := allInt.prod_right_ae
    filter_upwards [actual] with t integrable
    simp_rw [← integral_const_mul]
    simpa only [mul_assoc] using integral_integral (f := fun x y : ℝ => star (test x)*reactionKernel t x y*f y) integrable
  rw [lhsPair,rhsPair]
  exact swap.symm

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
