import H0mework.Versions.Y.Arithmetic.Mellin.ProperMellinL1

/-!
# Proper Mellin L¹ conjugate inversion

The actual proper Mellin carrier admits the Jacobian-corrected involution
`f(t) ↦ t⁻² star (f(t⁻¹))`.  It is semilinear over `starRingEnd ℂ`, preserves
null equality by the same change-of-variables law, is involutive, and sends
the source integral to its complex conjugate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set

noncomputable section

def positiveMellinL1StarInversionFunction
    (value : PositiveMellinL1) : ℝ → ℂ :=
  fun t => (t ^ (-2 : ℝ)) • star (value (t ^ (-1 : ℝ)))

theorem positiveMellinL1StarInversionFunction_integrable
    (value : PositiveMellinL1) :
    Integrable (positiveMellinL1StarInversionFunction value)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have source : Integrable (fun t : ℝ => star (value t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (L1.integrable_coeFn value)
  change IntegrableOn (fun t : ℝ => star (value t)) (Ioi 0) at source
  have transformed :=
    (integrableOn_Ioi_comp_rpow_iff
      (fun t : ℝ => star (value t))
      (p := (-1 : ℝ)) (by norm_num)).2 source
  change IntegrableOn (positiveMellinL1StarInversionFunction value) (Ioi 0)
  apply transformed.congr_fun
  · intro t ht
    change 0 < t at ht
    simp only [positiveMellinL1StarInversionFunction, real_smul]
    congr 1
    norm_num
  · exact measurableSet_Ioi

def positiveMellinL1StarInversionValue
    (value : PositiveMellinL1) : PositiveMellinL1 :=
  (positiveMellinL1StarInversionFunction_integrable value).toL1
    (positiveMellinL1StarInversionFunction value)

theorem positiveMellinL1StarInversionValue_ae
    (value : PositiveMellinL1) :
    (positiveMellinL1StarInversionValue value : ℝ → ℂ) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      positiveMellinL1StarInversionFunction value :=
  (positiveMellinL1StarInversionFunction_integrable value).coeFn_toL1

/-- Inversion preserves null equality on the positive half-line.  The proof
uses the Jacobian change of variables, not a free measure-preserving claim. -/
theorem positiveInverse_ae_congr
    {f g : ℝ → ℂ}
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ))))
    (hg : Integrable g (volume.restrict (Ioi (0 : ℝ))))
    (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    (fun t : ℝ => f (t ^ (-1 : ℝ))) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => g (t ^ (-1 : ℝ))) := by
  let distance : ℝ → ℝ := fun t => ‖f t - g t‖
  have distanceIntegrable :
      Integrable distance (volume.restrict (Ioi (0 : ℝ))) :=
    (hf.sub hg).norm
  have distanceIntegrableOn : IntegrableOn distance (Ioi (0 : ℝ)) :=
    distanceIntegrable
  let pulled : ℝ → ℝ := fun t =>
    t ^ (-2 : ℝ) * distance (t ^ (-1 : ℝ))
  have pulledIntegrableOn : IntegrableOn pulled (Ioi (0 : ℝ)) := by
    have transformed :=
      (integrableOn_Ioi_comp_rpow_iff distance
        (p := (-1 : ℝ)) (by norm_num)).2 distanceIntegrableOn
    apply transformed.congr_fun
    · intro t ht
      change 0 < t at ht
      simp only [pulled]
      congr 1
      norm_num
    · exact measurableSet_Ioi
  have distanceZero : distance =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [hfg] with t ht
    simp [distance, ht]
  have distanceIntegralZero :
      (∫ t : ℝ in Ioi 0, distance t) = 0 := by
    rw [integral_congr_ae distanceZero]
    simp
  have pulledIntegral :
      (∫ t : ℝ in Ioi 0, pulled t) =
        ∫ t : ℝ in Ioi 0, distance t := by
    calc
      (∫ t : ℝ in Ioi 0, pulled t) =
          ∫ t : ℝ in Ioi 0,
            (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
              distance (t ^ (-1 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 0 < t at ht
        simp only [pulled]
        congr 1
        norm_num
      _ = ∫ t : ℝ in Ioi 0, distance t :=
        integral_comp_rpow_Ioi distance (by norm_num)
  have pulledNonnegative : 0 ≤ᵐ[
      volume.restrict (Ioi (0 : ℝ))] pulled := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _)
  have pulledZero : pulled =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      pulledNonnegative pulledIntegrableOn).1
      (pulledIntegral.trans distanceIntegralZero)
  filter_upwards [pulledZero, ae_restrict_mem measurableSet_Ioi]
    with t htZero htPositive
  change 0 < t at htPositive
  have weightNe : t ^ (-2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos htPositive _).ne'
  have distanceAtZero : distance (t ^ (-1 : ℝ)) = 0 := by
    have productZero :
        t ^ (-2 : ℝ) * distance (t ^ (-1 : ℝ)) = 0 := by
      simpa [pulled] using htZero
    exact (mul_eq_zero.mp productZero).resolve_left weightNe
  exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [distance] using distanceAtZero))

theorem positiveMellinL1StarInversionFunction_integral
    (value : PositiveMellinL1) :
    (∫ t : ℝ in Ioi 0,
        positiveMellinL1StarInversionFunction value t) =
      star (∫ t : ℝ in Ioi 0, value t) := by
  calc
    (∫ t : ℝ in Ioi 0,
        positiveMellinL1StarInversionFunction value t) =
        ∫ t : ℝ in Ioi 0,
          (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
            star (value (t ^ (-1 : ℝ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      simp only [positiveMellinL1StarInversionFunction, real_smul]
      congr 1
      norm_num
    _ = ∫ t : ℝ in Ioi 0, star (value t) :=
      integral_comp_rpow_Ioi (fun t : ℝ => star (value t)) (by norm_num)
    _ = star (∫ t : ℝ in Ioi 0, value t) := integral_conj

theorem positiveMellinL1Integral_starInversionValue
    (value : PositiveMellinL1) :
    positiveMellinL1Integral
        (positiveMellinL1StarInversionValue value) =
      star (positiveMellinL1Integral value) := by
  unfold positiveMellinL1Integral
  rw [← L1.integral_eq' ℂ]
  change L1.integral
      (positiveMellinL1StarInversionFunction_integrable value).toL1 = _
  rw [← MeasureTheory.integral_eq
    (positiveMellinL1StarInversionFunction value)
    (positiveMellinL1StarInversionFunction_integrable value)]
  rw [positiveMellinL1StarInversionFunction_integral]
  congr 1
  calc
    (∫ t : ℝ in Ioi 0, value t) =
        L1.integral ((L1.integrable_coeFn value).toL1
          (fun t : ℝ => value t)) :=
      MeasureTheory.integral_eq _ (L1.integrable_coeFn value)
    _ = L1.integral value := by rw [Integrable.toL1_coeFn]
    _ = (L1.integralCLM' ℂ) value := L1.integral_eq' ℂ value

theorem positiveMellinL1StarInversionValue_add
    (left right : PositiveMellinL1) :
    positiveMellinL1StarInversionValue (left + right) =
      positiveMellinL1StarInversionValue left +
        positiveMellinL1StarInversionValue right := by
  have inverseAdd := positiveInverse_ae_congr
    (L1.integrable_coeFn (left + right))
    ((L1.integrable_coeFn left).add (L1.integrable_coeFn right))
    (Lp.coeFn_add left right)
  apply Lp.ext
  filter_upwards
    [positiveMellinL1StarInversionValue_ae (left + right),
      positiveMellinL1StarInversionValue_ae left,
      positiveMellinL1StarInversionValue_ae right,
      Lp.coeFn_add (positiveMellinL1StarInversionValue left)
        (positiveMellinL1StarInversionValue right), inverseAdd]
    with t hsum hleft hright hadd hinverse
  rw [hsum, hadd]
  simp only [Pi.add_apply]
  rw [hleft, hright]
  simp only [positiveMellinL1StarInversionFunction]
  rw [hinverse]
  simp [smul_add]

theorem positiveMellinL1StarInversionValue_smul
    (scalar : ℂ) (value : PositiveMellinL1) :
    positiveMellinL1StarInversionValue (scalar • value) =
      star scalar • positiveMellinL1StarInversionValue value := by
  have inverseSmul := positiveInverse_ae_congr
    (L1.integrable_coeFn (scalar • value))
    ((L1.integrable_coeFn value).smul scalar)
    (Lp.coeFn_smul scalar value)
  apply Lp.ext
  filter_upwards
    [positiveMellinL1StarInversionValue_ae (scalar • value),
      positiveMellinL1StarInversionValue_ae value,
      Lp.coeFn_smul (star scalar)
        (positiveMellinL1StarInversionValue value), inverseSmul]
    with t hscaled hvalue hsmul hinverse
  rw [hscaled, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hvalue]
  simp only [positiveMellinL1StarInversionFunction]
  rw [hinverse]
  simp only [Pi.smul_apply, smul_eq_mul, real_smul]
  rw [star_mul]
  ring

def positiveMellinL1StarInversion :
    PositiveMellinL1 →ₛₗ[starRingEnd ℂ] PositiveMellinL1 where
  toFun := positiveMellinL1StarInversionValue
  map_add' := positiveMellinL1StarInversionValue_add
  map_smul' := positiveMellinL1StarInversionValue_smul

theorem positiveMellinL1Integral_starInversion
    (value : PositiveMellinL1) :
    positiveMellinL1Integral (positiveMellinL1StarInversion value) =
      star (positiveMellinL1Integral value) :=
  positiveMellinL1Integral_starInversionValue value

theorem positiveMellinL1StarInversion_involutive
    (value : PositiveMellinL1) :
    positiveMellinL1StarInversion
        (positiveMellinL1StarInversion value) = value := by
  let inverted := positiveMellinL1StarInversionValue value
  have innerRead := positiveMellinL1StarInversionValue_ae value
  have innerInverseRead := positiveInverse_ae_congr
    (L1.integrable_coeFn inverted)
    (positiveMellinL1StarInversionFunction_integrable value) innerRead
  have outerRead := positiveMellinL1StarInversionValue_ae inverted
  apply Lp.ext
  filter_upwards [outerRead, innerInverseRead,
      ae_restrict_mem measurableSet_Ioi]
    with t houter hinner tPositive
  change 0 < t at tPositive
  change (positiveMellinL1StarInversionValue inverted : ℝ → ℂ) t =
    (value : ℝ → ℂ) t
  rw [houter]
  simp only [positiveMellinL1StarInversionFunction]
  rw [hinner]
  simp only [positiveMellinL1StarInversionFunction,
    Real.rpow_neg_one, inv_inv, star_smul, star_star]
  rw [Real.rpow_neg (le_of_lt tPositive),
    Real.rpow_neg (le_of_lt (inv_pos.mpr tPositive))]
  norm_num [Real.rpow_two, real_smul]
  field_simp [tPositive.ne']

theorem positiveMellinL1Integral_eq_setIntegral
    (value : PositiveMellinL1) :
    positiveMellinL1Integral value =
      ∫ t : ℝ in Ioi 0, value t := by
  unfold positiveMellinL1Integral
  rw [← L1.integral_eq' ℂ]
  symm
  calc
    (∫ t : ℝ in Ioi 0, value t) =
        L1.integral ((L1.integrable_coeFn value).toL1
          (fun t : ℝ => value t)) :=
      MeasureTheory.integral_eq _ (L1.integrable_coeFn value)
    _ = L1.integral value := by rw [Integrable.toL1_coeFn]

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
