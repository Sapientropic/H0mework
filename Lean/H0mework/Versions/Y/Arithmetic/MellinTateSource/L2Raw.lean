import H0mework.Versions.Y.Arithmetic.MobiusSource.WindowClosedRange
import H0mework.Versions.Y.Arithmetic.MellinBoundary.ProperMellinL1StarInversion

/-! The literal reciprocal and its Jacobian generate an actual full-line L² value. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace ENNReal
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

/-- The literal weight-one Tate reciprocal on the additive real chart. -/
def burnolTateReciprocalRaw (value : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((|x| : ℝ) : ℂ)⁻¹) * value x⁻¹

private theorem tateReciprocalRaw_aestronglyMeasurable (value : BurnolL2) :
    AEStronglyMeasurable (burnolTateReciprocalRaw value) volume := by
  apply AEStronglyMeasurable.mul
  · exact ((continuous_abs.measurable.complex_ofReal.inv).aestronglyMeasurable)
  · exact (Lp.stronglyMeasurable value).measurable.comp measurable_inv
      |>.aestronglyMeasurable

private theorem tateReciprocalNormSq_integrableOn_pos (value : BurnolL2) :
    IntegrableOn (fun x : ℝ ↦ ‖burnolTateReciprocalRaw value x‖ ^ 2)
      (Ioi 0) := by
  have source : IntegrableOn (fun x : ℝ ↦ ‖value x‖ ^ 2) (Ioi 0) :=
    ((Lp.memLp value).integrable_norm_pow (by norm_num : 2 ≠ 0)).integrableOn
  have transformed := (integrableOn_Ioi_comp_rpow_iff
    (fun x : ℝ ↦ ‖value x‖ ^ 2) (p := (-1 : ℝ)) (by norm_num)).2 source
  apply transformed.congr_fun
  · intro x hx
    have positive : 0 < x := hx
    have nonzero : x ≠ 0 := positive.ne'
    simp only [burnolTateReciprocalRaw, norm_mul, norm_inv,
      norm_real, Real.norm_eq_abs, abs_of_pos positive,
      abs_neg, abs_one, one_mul, Real.rpow_neg_one, smul_eq_mul]
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      Real.rpow_neg positive.le, Real.rpow_two]
    field_simp [nonzero]
  · exact measurableSet_Ioi

private theorem tateReciprocalNormSq_integrableOn_neg (value : BurnolL2) :
    IntegrableOn (fun x : ℝ ↦ ‖burnolTateReciprocalRaw value x‖ ^ 2)
      (Iic 0) := by
  have sourceGlobal : Integrable (fun x : ℝ ↦ ‖value x‖ ^ 2) :=
    (Lp.memLp value).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have source : IntegrableOn (fun x : ℝ ↦ ‖value (-x)‖ ^ 2) (Ioi 0) := by
    have reflected := (Measure.measurePreserving_neg (volume : Measure ℝ))
      |>.integrable_comp_of_integrable sourceGlobal
    simpa only [Function.comp_def] using reflected.integrableOn
  have changed := (integrableOn_Ioi_comp_rpow_iff
    (fun x : ℝ ↦ ‖value (-x)‖ ^ 2) (p := (-1 : ℝ)) (by norm_num)).2 source
  have transformed : IntegrableOn
      ((fun x : ℝ ↦ ‖burnolTateReciprocalRaw value x‖ ^ 2) ∘ fun x ↦ -x)
      (Ioi 0) := by
    apply changed.congr_fun
    · intro x hx
      have positive : 0 < x := hx
      have nonzero : x ≠ 0 := positive.ne'
      simp only [Function.comp_def, burnolTateReciprocalRaw,
        norm_mul, norm_inv, norm_real, Real.norm_eq_abs, abs_abs,
        abs_neg, abs_of_pos positive, abs_one, one_mul, Real.rpow_neg_one,
        smul_eq_mul]
      rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
        Real.rpow_neg positive.le, Real.rpow_two]
      field_simp [nonzero]
    · exact measurableSet_Ioi
  apply ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).1
  simpa only [neg_preimage, neg_Iic, neg_zero] using
    ((integrableOn_Ici_iff_integrableOn_Ioi
      (f := (fun x : ℝ ↦ ‖burnolTateReciprocalRaw value x‖ ^ 2) ∘
        fun x ↦ -x) (b := 0)).2 transformed)

theorem burnolTateReciprocalRaw_memLp (value : BurnolL2) :
    MemLp (burnolTateReciprocalRaw value) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (tateReciprocalRaw_aestronglyMeasurable value)).2
  rw [← integrableOn_univ]
  have joined := (tateReciprocalNormSq_integrableOn_neg value).union
    (tateReciprocalNormSq_integrableOn_pos value)
  simpa only [Iic_union_Ioi] using joined

/-- The actual `L²` value of the Tate reciprocal. -/
def burnolTateReciprocalValue (value : BurnolL2) : BurnolL2 :=
  (burnolTateReciprocalRaw_memLp value).toLp
    (burnolTateReciprocalRaw value)

theorem burnolTateReciprocalValue_coeFn (value : BurnolL2) :
    (burnolTateReciprocalValue value : ℝ → ℂ) =ᵐ[volume]
      burnolTateReciprocalRaw value :=
  (burnolTateReciprocalRaw_memLp value).coeFn_toLp

private theorem positiveInverse_ae_congr_L2
    {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfg : f =ᵐ[volume] g) :
    (fun t : ℝ ↦ f (t ^ (-1 : ℝ))) =ᵐ[volume.restrict (Ioi 0)]
      fun t : ℝ ↦ g (t ^ (-1 : ℝ)) := by
  let distance : ℝ → ℝ := fun t ↦ ‖f t - g t‖ ^ 2
  have distanceIntegrable : Integrable distance := by
    apply (memLp_two_iff_integrable_sq_norm (hf.sub hg).1).1
    exact hf.sub hg
  let pulled : ℝ → ℝ := fun t ↦
    t ^ (-2 : ℝ) * distance (t ^ (-1 : ℝ))
  have pulledIntegrable : IntegrableOn pulled (Ioi 0) := by
    have transformed := (integrableOn_Ioi_comp_rpow_iff distance
      (p := (-1 : ℝ)) (by norm_num)).2 distanceIntegrable.integrableOn
    apply transformed.congr_fun
    · intro t ht
      simp only [pulled, smul_eq_mul]
      congr 1
      norm_num
    · exact measurableSet_Ioi
  have distanceZero : distance =ᵐ[volume] 0 := by
    filter_upwards [hfg] with t ht
    simp [distance, ht]
  have distanceIntegralZero : (∫ t : ℝ in Ioi 0, distance t) = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae distanceZero)]
    simp
  have pulledIntegral : (∫ t : ℝ in Ioi 0, pulled t) =
      ∫ t : ℝ in Ioi 0, distance t := by
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
            distance (t ^ (-1 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [pulled, smul_eq_mul]
        congr 1
        norm_num
      _ = _ := integral_comp_rpow_Ioi distance (by norm_num)
  have pulledNonnegative : 0 ≤ᵐ[volume.restrict (Ioi 0)] pulled := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (sq_nonneg _)
  have pulledZero : pulled =ᵐ[volume.restrict (Ioi 0)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae pulledNonnegative pulledIntegrable).1
      (pulledIntegral.trans distanceIntegralZero)
  filter_upwards [pulledZero, ae_restrict_mem measurableSet_Ioi]
    with t htZero htPositive
  have weightNe : t ^ (-2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos htPositive _).ne'
  have distanceAtZero : distance (t ^ (-1 : ℝ)) = 0 := by
    apply (mul_eq_zero.mp (show t ^ (-2 : ℝ) *
      distance (t ^ (-1 : ℝ)) = 0 by simpa [pulled] using htZero)).resolve_left
    exact weightNe
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (sq_eq_zero_iff.mp (by simpa [distance] using distanceAtZero)))

theorem burnolTateReciprocalRaw_ae_congr
    {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfg : f =ᵐ[volume] g) :
    burnolTateReciprocalRaw f =ᵐ[volume]
      burnolTateReciprocalRaw g := by
  have positive := positiveInverse_ae_congr_L2 hf hg hfg
  have hfgNeg : (fun x : ℝ ↦ f (-x)) =ᵐ[volume] fun x ↦ g (-x) := by
    have pulled := (Measure.measurePreserving_neg (volume : Measure ℝ))
      |>.quasiMeasurePreserving.ae hfg
    filter_upwards [pulled] with x hx
    exact hx
  have negativeAtPositive := positiveInverse_ae_congr_L2
    (hf.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ)))
    (hg.comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ))) hfgNeg
  have positiveGlobal := (ae_restrict_iff' measurableSet_Ioi).mp positive
  have negativeGlobal := (Measure.measurePreserving_neg (volume : Measure ℝ))
    |>.quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioi).mp negativeAtPositive)
  filter_upwards [positiveGlobal, negativeGlobal] with x hpos hneg
  by_cases hx : x = 0
  · simp [burnolTateReciprocalRaw, hx]
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · unfold burnolTateReciprocalRaw
    congr 1
    have read := hneg (show -x ∈ Ioi (0 : ℝ) by simpa using neg_pos.mpr hxneg)
    have inverseRead : -((-x) ^ (-1 : ℝ)) = x⁻¹ := by
      rw [Real.rpow_neg_one]
      field_simp
    simpa only [Function.comp_def, inverseRead] using read
  · unfold burnolTateReciprocalRaw
    congr 1
    simpa only [Real.rpow_neg_one] using hpos hxpos

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
