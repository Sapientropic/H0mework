import H0mework.Arithmetic.MobiusSource.MobiusDivisorInverse

/-! # Exact source recovery and normalization from the centred Möbius inverse -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators
noncomputable section

theorem burnolCompactCenteredMobiusInverse_roundtrip
    (source : burnolCompactAnnulusSource) (t : ℝ) :
    burnolCenteredMobiusInverse (burnolCompactAdditiveCoSum source) t =
      burnolCompactAdditiveSource source t := by
  rw [burnolCompactCenteredMobiusInverse_eq_joint,
    burnolCompactMobiusJointTerm_tsum]

theorem burnolCompactAnnulusSource_eq_inverse_reciprocal
    (source : burnolCompactAnnulusSource) (u : ℝ) :
    source.1 u = (((|u| : ℝ) : ℂ)⁻¹) *
      burnolCenteredMobiusInverse (burnolCompactAdditiveCoSum source) u⁻¹ := by
  rw [burnolCompactCenteredMobiusInverse_roundtrip]
  by_cases hu : u = 0
  · subst u
    rw [source.2.2.1 0 (by norm_num)]
    simp [burnolCompactAdditiveSource]
  · rw [burnolCompactAdditiveSource, if_neg (inv_ne_zero hu), inv_inv,
      abs_inv]
    push_cast
    field_simp [abs_ne_zero.mpr hu]

theorem burnolCompactCenteredMobiusInverse_annularSupport (source : burnolCompactAnnulusSource) :
    (∀ {t : ℝ}, |t| ≤ (1 / 4 : ℝ) →
      burnolCenteredMobiusInverse (burnolCompactAdditiveCoSum source) t = 0) ∧
    (∀ {t : ℝ}, 4 ≤ |t| →
      burnolCenteredMobiusInverse (burnolCompactAdditiveCoSum source) t = 0) := by
  constructor <;> intro t ht <;>
    rw [burnolCompactCenteredMobiusInverse_roundtrip]
  · exact burnolCompactAdditiveSource_zero_of_abs_le_quarter source ht
  · exact burnolCompactAdditiveSource_zero_of_four_le_abs source ht

theorem burnolCompactCenteredMobiusInverse_reciprocalMoment (source : burnolCompactAnnulusSource) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)⁻¹ * burnolCenteredMobiusInverse
      (burnolCompactAdditiveCoSum source) t) = -burnolCompactAdditiveCoSum source 0 := by
  simp_rw [burnolCompactCenteredMobiusInverse_roundtrip]
  have positiveIntegral : (∫ t : ℝ in Ioi 0, source.1 t) =
      (1 / 2 : ℂ) * ∫ t : ℝ, source.1 t := by
    have negative : (∫ t : ℝ in Iic 0, source.1 t) =
        ∫ t : ℝ in Ioi 0, source.1 t := by
      calc
        _ = ∫ t : ℝ in Iic 0, source.1 (-t) := by
          exact setIntegral_congr_fun measurableSet_Iic fun t _ ↦ (source.2.1 t).symm
        _ = _ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 source.1
    have full : (∫ t : ℝ, source.1 t) =
        2 * ∫ t : ℝ in Ioi 0, source.1 t := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          source.1.integrable.integrableOn source.1.integrable.integrableOn, negative]
      ring
    rw [full]
    ring
  have change := MeasureTheory.integral_comp_rpow_Ioi
    (fun y : ℝ ↦ source.1 y) (p := (-1 : ℝ)) (by norm_num)
  calc
    _ = ∫ t : ℝ in Ioi 0,
        (|-1| * t ^ ((-1 : ℝ) - 1)) • source.1 (t ^ (-1 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have tNe : t ≠ 0 := ht.ne'
      dsimp only
      rw [burnolCompactAdditiveSource, if_neg tNe, abs_of_pos ht,
        Real.rpow_neg_one]
      simp only [abs_neg, abs_one, one_mul, Complex.real_smul]
      rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
        Real.rpow_neg ht.le, Real.rpow_two]
      push_cast
      field_simp [tNe]
    _ = ∫ y : ℝ in Ioi 0, source.1 y := change
    _ = burnolCompactAdditiveNormalization source := positiveIntegral.trans rfl
    _ = -burnolCompactAdditiveCoSum source 0 := by
      rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
        source (t := 0) (by norm_num)]
      ring
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
