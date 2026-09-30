import H0mework.Arithmetic.BurnolCarrier.AdditiveL2

/-!
# Full-even L² realization and the exact Fourier-side boundary

Evenness transports the positive-half additive realization across the
origin.  This file constructs the resulting full-line `L²` value, proves
that reflection fixes it, and lands it in the position-side constant face.
The only remaining Burnol-face coordinate is then the Fourier-side local
constant law; it is exposed as an exact equivalence rather than assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- A globally measurable even reconstruction from the positive-half
realization. -/
def burnolAdditiveEvenReconstruction (t : ℝ) : ℂ :=
  if t = 0 then burnolAdditiveCoSum 0
  else burnolAdditivePositiveReconstruction |t|

theorem burnolAdditiveEvenReconstruction_eq (t : ℝ) :
    burnolAdditiveEvenReconstruction t = burnolAdditiveCoSum t := by
  by_cases zero : t = 0
  · simp [burnolAdditiveEvenReconstruction, zero]
  · rw [burnolAdditiveEvenReconstruction, if_neg zero,
      burnolAdditivePositiveReconstruction_eq (abs_pos.mpr zero)]
    rcases lt_or_ge t 0 with negative | nonnegative
    · rw [abs_of_neg negative, burnolAdditiveCoSum_even]
    · rw [abs_of_nonneg nonnegative]

theorem burnolAdditiveEvenReconstruction_measurable :
    Measurable burnolAdditiveEvenReconstruction := by
  unfold burnolAdditiveEvenReconstruction
  apply Measurable.ite
  · exact measurableSet_singleton 0
  · exact measurable_const
  · exact burnolAdditivePositiveReconstruction_measurable.comp
      continuous_abs.measurable

theorem burnolAdditiveCoSum_measurable :
    Measurable burnolAdditiveCoSum := by
  rw [← show burnolAdditiveEvenReconstruction = burnolAdditiveCoSum by
    funext t
    exact burnolAdditiveEvenReconstruction_eq t]
  exact burnolAdditiveEvenReconstruction_measurable

private theorem burnolAdditiveCoSum_sq_norm_abs (t : ℝ) :
    ‖burnolAdditiveCoSum |t|‖ ^ 2 =
      ‖burnolAdditiveCoSum t‖ ^ 2 := by
  rcases lt_or_ge t 0 with negative | nonnegative
  · rw [abs_of_neg negative, burnolAdditiveCoSum_even]
  · rw [abs_of_nonneg nonnegative]

private theorem burnolAdditiveCoSum_sq_norm_integrable :
    Integrable (fun t : ℝ => ‖burnolAdditiveCoSum t‖ ^ 2) := by
  have positiveIntegrable : IntegrableOn
      (fun t : ℝ => ‖burnolAdditiveCoSum t‖ ^ 2) (Ioi 0) :=
    (memLp_two_iff_integrable_sq_norm
      burnolAdditiveCoSum_aestronglyMeasurable_positive).mp
        burnolAdditiveCoSum_memLp_positive
  have absPositiveIntegrable : IntegrableOn
      (fun t : ℝ => ‖burnolAdditiveCoSum |t|‖ ^ 2) (Ioi 0) := by
    refine positiveIntegrable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    rw [abs_of_pos positive]
  have absNegativeIntegrable : IntegrableOn
      (fun t : ℝ => ‖burnolAdditiveCoSum |t|‖ ^ 2) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let embedding : MeasurableEmbedding (fun t : ℝ => -t) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [embedding.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      absPositiveIntegrable
  have absIntegrable : Integrable
      (fun t : ℝ => ‖burnolAdditiveCoSum |t|‖ ^ 2) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact absNegativeIntegrable.union absPositiveIntegrable
  refine absIntegrable.congr ?_
  exact ae_of_all (volume : Measure ℝ) fun t =>
    burnolAdditiveCoSum_sq_norm_abs t

/-- The additive co-sum is an actual full-line `L²` function. -/
theorem burnolAdditiveCoSum_memLp_full :
    MemLp burnolAdditiveCoSum 2 (volume : Measure ℝ) := by
  exact (memLp_two_iff_integrable_sq_norm
    burnolAdditiveCoSum_measurable.aestronglyMeasurable).mpr
      burnolAdditiveCoSum_sq_norm_integrable

/-- Concrete full-line even `L²` realization. -/
def burnolAdditiveFullEvenL2 : BurnolL2 :=
  burnolAdditiveCoSum_memLp_full.toLp burnolAdditiveCoSum

theorem burnolAdditiveFullEvenL2_coeFn :
    (burnolAdditiveFullEvenL2 : ℝ → ℂ) =ᵐ[volume]
      burnolAdditiveCoSum :=
  MemLp.coeFn_toLp burnolAdditiveCoSum_memLp_full

/-- The full-line realization lies in the actual even/cosine sector. -/
theorem reflectL2_burnolAdditiveFullEvenL2 :
    reflectL2 burnolAdditiveFullEvenL2 =
      burnolAdditiveFullEvenL2 := by
  apply Lp.ext
  have valueAtNeg := negMeasurePreserving.quasiMeasurePreserving.ae
    burnolAdditiveFullEvenL2_coeFn
  filter_upwards [
    Lp.coeFn_compMeasurePreserving burnolAdditiveFullEvenL2
      negMeasurePreserving,
    valueAtNeg,
    burnolAdditiveFullEvenL2_coeFn] with t href hneg hpos
  calc
    reflectL2 burnolAdditiveFullEvenL2 t =
        burnolAdditiveFullEvenL2 (-t) := href
    _ = burnolAdditiveCoSum (-t) := hneg
    _ = burnolAdditiveCoSum t := burnolAdditiveCoSum_even t
    _ = burnolAdditiveFullEvenL2 t := hpos.symm

theorem burnolAdditiveFullEvenL2_mem_even :
    burnolAdditiveFullEvenL2 ∈ evenL2ClosedFace :=
  mem_evenL2ClosedFace_iff.mpr reflectL2_burnolAdditiveFullEvenL2

private theorem burnolAdditiveFullEven_inner_eq_two_positive :
    inner ℂ burnolAdditiveFullEvenL2 burnolAdditiveFullEvenL2 =
      (2 : ℂ) * inner ℂ burnolAdditivePositiveL2
        burnolAdditivePositiveL2 := by
  let integrand : ℝ → ℂ := fun t =>
    inner ℂ (burnolAdditiveCoSum t) (burnolAdditiveCoSum t)
  have integrandEven (t : ℝ) : integrand (-t) = integrand t := by
    simp only [integrand]
    rw [burnolAdditiveCoSum_even]
  have integrandIntegrable : Integrable integrand := by
    have fullIntegrable := MeasureTheory.L2.integrable_inner
      (𝕜 := ℂ) burnolAdditiveFullEvenL2 burnolAdditiveFullEvenL2
    refine fullIntegrable.congr ?_
    filter_upwards [burnolAdditiveFullEvenL2_coeFn] with t equality
    simp only [integrand]
    rw [equality]
  have negativeIntegral : (∫ t : ℝ in Iic 0, integrand t) =
      ∫ t : ℝ in Ioi 0, integrand t := by
    calc
      (∫ t : ℝ in Iic 0, integrand t) =
          ∫ t : ℝ in Iic 0, integrand (-t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t _
        exact (integrandEven t).symm
      _ = ∫ t : ℝ in Ioi 0, integrand t :=
        by simpa only [neg_zero] using integral_comp_neg_Iic 0 integrand
  have fullIntegral : (∫ t : ℝ, integrand t) =
      (2 : ℂ) * ∫ t : ℝ in Ioi 0, integrand t := by
    calc
      (∫ t : ℝ, integrand t) =
          (∫ t : ℝ in Iic 0, integrand t) +
            ∫ t : ℝ in Ioi 0, integrand t := by
        rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
          setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
            integrandIntegrable.integrableOn integrandIntegrable.integrableOn]
      _ = (2 : ℂ) * ∫ t : ℝ in Ioi 0, integrand t := by
        rw [negativeIntegral]
        ring
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ t : ℝ, inner ℂ (burnolAdditiveFullEvenL2 t)
        (burnolAdditiveFullEvenL2 t)) =
      ∫ t : ℝ, integrand t := by
        apply integral_congr_ae
        filter_upwards [burnolAdditiveFullEvenL2_coeFn] with t equality
        simp only [integrand]
        rw [equality]
    _ = (2 : ℂ) * ∫ t : ℝ in Ioi 0, integrand t := fullIntegral
    _ = (2 : ℂ) *
        ∫ t : ℝ, inner ℂ (burnolAdditivePositiveL2 t)
          (burnolAdditivePositiveL2 t)
            ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [burnolAdditivePositiveL2_coeFn] with t equality
      simp only [integrand]
      rw [equality]

/-- The unnormalized full-even realization has exactly twice the positive
energy. -/
theorem burnolAdditiveFullEvenL2_norm_sq_eq_two_positive :
    ‖burnolAdditiveFullEvenL2‖ ^ 2 =
      2 * ‖burnolAdditivePositiveL2‖ ^ 2 := by
  calc
    ‖burnolAdditiveFullEvenL2‖ ^ 2 =
        (inner ℂ burnolAdditiveFullEvenL2
          burnolAdditiveFullEvenL2).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = ((2 : ℂ) * inner ℂ burnolAdditivePositiveL2
        burnolAdditivePositiveL2).re := by
      rw [burnolAdditiveFullEven_inner_eq_two_positive]
    _ = 2 * (inner ℂ burnolAdditivePositiveL2
        burnolAdditivePositiveL2).re := by norm_num
    _ = 2 * ‖burnolAdditivePositiveL2‖ ^ 2 := by
      congr 1
      convert (InnerProductSpace.norm_sq_eq_re_inner
        (𝕜 := ℂ) burnolAdditivePositiveL2).symm using 1
      all_goals rfl

/-- The honest common gap of the current unscaled reciprocal pair.  The
position source has the larger gap, while its Fourier partner only supplies
radius `1/4`. -/
def burnolUnscaledCommonGapRadius : ℝ := 1 / 4

theorem burnolUnscaledCommonGapRadius_le_one :
    burnolUnscaledCommonGapRadius ≤ 1 := by
  norm_num [burnolUnscaledCommonGapRadius]

/-- The full-even additive realization lands in every position-side gap of
radius at most `1`; in particular this covers the honest common radius
`1 / 4` of the current unscaled reciprocal pair. -/
theorem burnolAdditiveFullEvenL2_mem_locallyConstantFace_of_le_one
    {radius : ℝ} (atMostOne : radius ≤ 1) :
    burnolAdditiveFullEvenL2 ∈ locallyConstantFace radius := by
  rw [mem_locallyConstantFace_iff_exists]
  refine ⟨-burnolAdditiveNormalization, ?_⟩
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_smul (-burnolAdditiveNormalization)
      (intervalConstant radius),
    intervalConstant_coeFn radius,
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius)
      burnolAdditiveFullEvenL2,
    ae_restrict_of_ae burnolAdditiveFullEvenL2_coeFn,
    ae_restrict_mem (measurableSet_symmetricInterval radius)]
      with t hsmul hconstant hrestrict hfull inside
  have absBound : |t| ≤ 1 := by
    change t ∈ Icc (-radius) radius at inside
    exact (abs_le.mpr inside).trans atMostOne
  calc
    ((-burnolAdditiveNormalization) • intervalConstant radius) t =
        (-burnolAdditiveNormalization) * intervalConstant radius t := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = -burnolAdditiveNormalization := by rw [hconstant, mul_one]
    _ = burnolAdditiveCoSum t :=
      (burnolAdditiveCoSum_eq_neg_normalization_of_abs_le_one
        absBound).symm
    _ = burnolAdditiveFullEvenL2 t := hfull.symm
    _ = restrictToInterval radius burnolAdditiveFullEvenL2 t :=
      hrestrict.symm

theorem burnolAdditiveFullEvenL2_mem_unscaledCommonLocallyConstantFace :
    burnolAdditiveFullEvenL2 ∈
      locallyConstantFace burnolUnscaledCommonGapRadius :=
  burnolAdditiveFullEvenL2_mem_locallyConstantFace_of_le_one
    burnolUnscaledCommonGapRadius_le_one

/-- After the `L²`, evenness, and position landing producers have been paid,
the full Burnol face is equivalent to one exact remaining statement: local
constancy of the actual additive Fourier transform. -/
theorem burnolAdditiveFullEvenL2_mem_burnolFace_iff_fourierLocalConstant :
    burnolAdditiveFullEvenL2 ∈ burnolFace burnolUnscaledCommonGapRadius ↔
      fourierL2 burnolAdditiveFullEvenL2 ∈
        locallyConstantFace burnolUnscaledCommonGapRadius := by
  rw [mem_burnolFace_iff]
  exact and_iff_right
    burnolAdditiveFullEvenL2_mem_unscaledCommonLocallyConstantFace

/-- Exact physical landing mouth.  The even coordinate is already closed,
so this has precisely the same Fourier-side obstruction. -/
theorem burnolAdditiveFullEvenL2_mem_evenBurnolClosedFace_iff :
    burnolAdditiveFullEvenL2 ∈
        evenBurnolClosedFace burnolUnscaledCommonGapRadius ↔
      fourierL2 burnolAdditiveFullEvenL2 ∈
        locallyConstantFace burnolUnscaledCommonGapRadius := by
  change (burnolAdditiveFullEvenL2 ∈
      burnolFace burnolUnscaledCommonGapRadius ∧
      burnolAdditiveFullEvenL2 ∈ evenL2ClosedFace) ↔ _
  rw [burnolAdditiveFullEvenL2_mem_burnolFace_iff_fourierLocalConstant]
  exact and_iff_left burnolAdditiveFullEvenL2_mem_even

end


end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
