import H0mework.Arithmetic.BurnolCarrier.AdditiveNonzeroBoundary

/-!
# Integrable reciprocal source for the additive Fourier calculation

This file records the compact reciprocal source facts needed to justify
Fourier pairing and sum/integral interchange.  It introduces no Fourier
landing statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal SchwartzMap

noncomputable section

theorem burnolAdditiveAnnulusSource_zero_of_four_le_abs
    {t : ℝ} (outside : 4 ≤ |t|) :
    burnolAdditiveAnnulusSource t = 0 := by
  have nonzero : t ≠ 0 := by
    intro zero
    subst t
    norm_num at outside
  have absPositive : 0 < |t| := abs_pos.mpr nonzero
  have inverseInner : |t⁻¹| ≤ (1 / 4 : ℝ) := by
    rw [abs_inv]
    have inverseOrder : |t|⁻¹ ≤ (4 : ℝ)⁻¹ :=
      (inv_le_inv₀ absPositive (by norm_num)).mpr outside
    norm_num at inverseOrder ⊢
    exact inverseOrder
  have inverseInnerNeg : |-t⁻¹| ≤ (1 / 4 : ℝ) := by
    simpa only [abs_neg] using inverseInner
  have annulusZero : burnolEvenAnnulusSchwartz t⁻¹ = 0 := by
    simp only [burnolEvenAnnulusSchwartz, add_apply,
      burnolAnnulusSchwartzReflection_apply,
      burnolAnnulusSchwartz_apply]
    rw [burnolAnnulusBump_zero_of_abs_le_quarter inverseInner,
      burnolAnnulusBump_zero_of_abs_le_quarter inverseInnerNeg]
    norm_num
  rw [burnolAdditiveAnnulusSource, if_neg nonzero, annulusZero, mul_zero]

theorem burnolAdditiveAnnulusSource_measurable :
    Measurable burnolAdditiveAnnulusSource := by
  unfold burnolAdditiveAnnulusSource
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · fun_prop

theorem burnolAdditiveAnnulusSource_norm_le (t : ℝ) :
    ‖burnolAdditiveAnnulusSource t‖ ≤
      (SchwartzMap.seminorm ℝ 0 0) burnolEvenAnnulusSchwartz := by
  by_cases inside : |t| ≤ 1
  · rw [burnolAdditiveAnnulusSource_zero_of_abs_le_one inside, norm_zero]
    exact apply_nonneg _ _
  · have nonzero : t ≠ 0 := by
      intro zero
      subst t
      simp at inside
    have absPositive : 0 < |t| := abs_pos.mpr nonzero
    have oneLe : (1 : ℝ) ≤ |t| := le_of_not_ge inside
    have coefficient : ‖(((|t| : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
      simp only [norm_inv, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg t)]
      exact (inv_le_one₀ absPositive).mpr oneLe
    rw [burnolAdditiveAnnulusSource, if_neg nonzero, norm_mul]
    calc
      _ ≤ 1 * ‖burnolEvenAnnulusSchwartz t⁻¹‖ :=
        mul_le_mul_of_nonneg_right coefficient (norm_nonneg _)
      _ ≤ 1 * (SchwartzMap.seminorm ℝ 0 0)
          burnolEvenAnnulusSchwartz :=
        mul_le_mul_of_nonneg_left
          (SchwartzMap.norm_le_seminorm ℝ burnolEvenAnnulusSchwartz t⁻¹)
          zero_le_one
      _ = _ := one_mul _

theorem burnolAdditiveAnnulusSource_integrable :
    Integrable burnolAdditiveAnnulusSource := by
  have onInterval : IntegrableOn burnolAdditiveAnnulusSource
      (Icc (-4 : ℝ) 4) :=
    IntegrableOn.of_bound (by rw [Real.volume_Icc]; norm_num)
      burnolAdditiveAnnulusSource_measurable.aestronglyMeasurable.restrict
      ((SchwartzMap.seminorm ℝ 0 0) burnolEvenAnnulusSchwartz)
      (ae_of_all ((volume : Measure ℝ).restrict (Icc (-4 : ℝ) 4))
        burnolAdditiveAnnulusSource_norm_le)
  apply onInterval.integrable_of_forall_notMem_eq_zero
  intro t outside
  apply burnolAdditiveAnnulusSource_zero_of_four_le_abs
  change ¬(-4 ≤ t ∧ t ≤ 4) at outside
  rcases lt_or_ge t (-4) with left | left
  · rw [abs_of_neg (by linarith)]
    linarith
  · have right : 4 < t := lt_of_not_ge fun upper => outside ⟨left, upper⟩
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem burnolEvenAnnulus_positive_integral_eq_normalization :
    (∫ t : ℝ in Ioi 0, burnolEvenAnnulusSchwartz t) =
      burnolAdditiveNormalization := by
  have negativeIntegral :
      (∫ t : ℝ in Iic 0, burnolEvenAnnulusSchwartz t) =
        ∫ t : ℝ in Ioi 0, burnolEvenAnnulusSchwartz t := by
    calc
      (∫ t : ℝ in Iic 0, burnolEvenAnnulusSchwartz t) =
          ∫ t : ℝ in Iic 0, burnolEvenAnnulusSchwartz (-t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t _
        exact (burnolEvenAnnulusSchwartz_even t).symm
      _ = ∫ t : ℝ in Ioi 0, burnolEvenAnnulusSchwartz t := by
        simpa only [neg_zero] using
          integral_comp_neg_Iic 0 burnolEvenAnnulusSchwartz
  have fullIntegral : (∫ t : ℝ, burnolEvenAnnulusSchwartz t) =
      2 * ∫ t : ℝ in Ioi 0, burnolEvenAnnulusSchwartz t := by
    calc
      (∫ t : ℝ, burnolEvenAnnulusSchwartz t) =
          (∫ t : ℝ in Iic 0, burnolEvenAnnulusSchwartz t) +
            ∫ t : ℝ in Ioi 0, burnolEvenAnnulusSchwartz t := by
        rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
          setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
            burnolEvenAnnulusSchwartz.integrable.integrableOn
            burnolEvenAnnulusSchwartz.integrable.integrableOn]
      _ = _ := by rw [negativeIntegral]; ring
  unfold burnolAdditiveNormalization
  rw [fullIntegral]
  ring

/-- The full-line normalization is the actual reciprocal `dt/t` moment of
the positive additive source. -/
theorem burnolAdditiveSource_reciprocalMoment_eq_normalization :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ)⁻¹ * burnolAdditiveAnnulusSource t) =
        burnolAdditiveNormalization := by
  have change := MeasureTheory.integral_comp_rpow_Ioi
    (fun y : ℝ => burnolEvenAnnulusSchwartz y)
    (p := (-1 : ℝ)) (by norm_num)
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ)⁻¹ * burnolAdditiveAnnulusSource t) =
      ∫ t : ℝ in Ioi 0,
        (|-1| * t ^ ((-1 : ℝ) - 1)) •
          burnolEvenAnnulusSchwartz (t ^ (-1 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t positive
      have tNe : t ≠ 0 := ne_of_gt positive
      unfold burnolAdditiveAnnulusSource
      dsimp only
      rw [if_neg tNe, abs_of_pos positive,
        Real.rpow_neg_one]
      simp only [abs_neg, abs_one, one_mul, Complex.real_smul]
      rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
        Real.rpow_neg (le_of_lt positive), Real.rpow_two]
      push_cast
      field_simp [tNe]
    _ = ∫ y : ℝ in Ioi 0, burnolEvenAnnulusSchwartz y := change
    _ = burnolAdditiveNormalization :=
      burnolEvenAnnulus_positive_integral_eq_normalization

theorem burnolAdditiveReciprocalWeightedSource_integrable :
    Integrable (fun t : ℝ =>
      (t : ℂ)⁻¹ * burnolAdditiveAnnulusSource t) := by
  have measurable : AEStronglyMeasurable (fun t : ℝ =>
      (t : ℂ)⁻¹ * burnolAdditiveAnnulusSource t) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact burnolAdditiveAnnulusSource_measurable
  apply burnolAdditiveAnnulusSource_integrable.norm.mono' measurable
  exact ae_of_all (volume : Measure ℝ) fun t => by
    by_cases inside : |t| ≤ 1
    · rw [burnolAdditiveAnnulusSource_zero_of_abs_le_one inside]
      simp
    · have nonzero : t ≠ 0 := by
        intro zero
        subst t
        simp at inside
      have absPositive : 0 < |t| := abs_pos.mpr nonzero
      have oneLe : (1 : ℝ) ≤ |t| := le_of_not_ge inside
      rw [norm_mul, norm_inv, norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((inv_le_one₀ absPositive).mpr oneLe)

/-- The constant appearing on the Fourier-side gap. -/
def burnolAdditiveFourierGapConstant : ℂ :=
  -(∫ t : ℝ in Ioi 0, burnolAdditiveAnnulusSource t)

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
