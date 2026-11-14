import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.DirectRightResolvent

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DualSource

open Complex MeasureTheory Set

local notation "D" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolvent

private theorem inverse_clock_image (upper : ℝ) (positive : 0 < upper) :
    (fun h : ℝ => upper * Real.exp (-h/2)) '' Ioi (0 : ℝ) = Ioo 0 upper := by
  ext a
  constructor
  · rintro ⟨h, after, rfl⟩
    have short : Real.exp (-h/2) < 1 := Real.exp_lt_one_iff.mpr (by linarith [show 0 < h from after])
    exact ⟨mul_pos positive (Real.exp_pos _),
      by simpa only [mul_one] using mul_lt_mul_of_pos_left short positive⟩
  · intro within
    have ratio : 0 < a/upper := div_pos within.1 positive
    have short : a/upper < 1 := (div_lt_one positive).mpr within.2
    refine ⟨-2*Real.log (a/upper), by
      change 0 < -2*Real.log (a/upper)
      linarith [Real.log_neg ratio short], ?_⟩
    change upper * Real.exp (-(-2*Real.log (a/upper))/2) = a
    rw [show -(-2*Real.log (a/upper))/2 = Real.log (a/upper) by ring, Real.exp_log ratio]
    rw [← mul_div_assoc, mul_div_cancel_left₀ a positive.ne']

/-- The original inverse continuous normalization is an actual resolvent at its integration endpoint. -/
theorem actual_inverse_normalization (upper : ℝ) (positive : 0 < upper) (value : BurnolL2) :
    (∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel 1 a value) =
      -((Real.sqrt upper/2 : ℝ) : ℂ) • D (Real.log upper) (R (1/2) value) := by
  let clock := fun h : ℝ => upper * Real.exp (-h/2)
  let drift := fun h : ℝ => (-upper/2) * Real.exp (-h/2)
  have image : clock '' Ioi (0 : ℝ) = Ioo 0 upper := inverse_clock_image upper positive
  have derivative (h : ℝ) (_ : h ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt clock (drift h) (Ioi (0 : ℝ)) h := by
    have source : HasDerivAt (fun t : ℝ => upper * Real.exp (-t/2))
        (upper * (Real.exp (-h/2) * ((-1 : ℝ)/2))) h :=
      ((hasDerivAt_id h).neg.div_const 2).exp.const_mul upper
    have same : upper * (Real.exp (-h/2) * ((-1 : ℝ)/2)) = drift h := by
      dsimp only [drift]
      ring
    rw [← same]
    exact source.hasDerivWithinAt
  have injective : InjOn clock (Ioi (0 : ℝ)) := by
    intro h _ k _ same
    change upper * Real.exp (-h/2) = upper * Real.exp (-k/2) at same
    have hours := Real.exp_injective (mul_left_cancel₀ positive.ne' same)
    linarith
  have aeCut : Ioc (0 : ℝ) upper =ᵐ[volume] Ioo 0 upper := by
    filter_upwards [volume.ae_ne upper] with a different
    change (0 < a ∧ a ≤ upper) = (0 < a ∧ a < upper)
    exact propext (and_congr_right fun _ => ⟨fun le => lt_of_le_of_ne le different, le_of_lt⟩)
  rw [setIntegral_congr_set aeCut, ← image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi derivative injective]
  have point (h : ℝ) (_ : h ∈ Ioi (0 : ℝ)) :
      |drift h| • ContinuousChannels.channel 1 (clock h) value =
        ((Real.sqrt upper/2 : ℝ) : ℂ) • D (Real.log upper)
          (burnolDirectRightResolventIntegrand (1/2) value h) := by
    have falling : drift h < 0 := mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
    have root : Real.sqrt (Real.exp (-h/2)) = Real.exp (-h/4) := by
      rw [← Real.exp_half, show (-h/2)/2 = -h/4 by ring]
    have scale : -(drift h) * (Real.sqrt upper * Real.exp (-h/4))⁻¹ =
        Real.sqrt upper/2 * Real.exp (-h/4) := by
      have exponential : Real.exp (-h/2) = (Real.exp (-h/4))^2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have live := (Real.sqrt_pos.mpr positive).ne'
      have halfSquare : upper/2 = (Real.sqrt upper)^2/2 := by rw [Real.sq_sqrt positive.le]
      have magnitude : -(drift h) = upper/2 * Real.exp (-h/2) := by
        dsimp only [drift]
        ring
      rw [magnitude, halfSquare, exponential]
      field_simp [live, (Real.exp_pos (-h/4)).ne']
    have exponent : ((1/4 : ℂ)-1/2)*(h : ℂ) = ((-h/4 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [abs_of_neg falling, RCLike.real_smul_eq_coe_smul (K := ℂ), ContinuousChannels.channel,
      one_mul, burnolDirectRightResolventIntegrand, positiveMellinQuarterRightResolventWeight,
      exponent, ← Complex.ofReal_exp, map_smul, smul_smul, smul_smul]
    change (((-(drift h) : ℝ) : ℂ) * ((Real.sqrt (upper*Real.exp (-h/2)) : ℂ))⁻¹) •
      D (Real.log (upper*Real.exp (-h/2))) value = _
    rw [Real.sqrt_mul positive.le, root, ← Complex.ofReal_inv, ← Complex.ofReal_mul, scale,
      Complex.ofReal_mul, Real.log_mul positive.ne' (Real.exp_ne_zero _), Real.log_exp,
      ← burnolMultiplicativeDilation_add]
  rw [setIntegral_congr_fun measurableSet_Ioi point, integral_smul]
  let action := (D (Real.log upper)).toContinuousLinearEquiv.toContinuousLinearMap
  have integral := action.integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn (1/2) (by norm_num) value)
  change ((Real.sqrt upper/2 : ℝ) : ℂ) •
      (∫ h : ℝ in Ioi 0, action (burnolDirectRightResolventIntegrand (1/2) value h)) =
    -((Real.sqrt upper/2 : ℝ) : ℂ) • action (R (1/2) value)
  rw [integral, burnolDirectRightResolvent, map_neg, smul_neg, neg_smul, neg_neg]

/-- The original first cutoff contains the continuous normalization. -/
theorem actual_first_source (value : BurnolL2) :
    source 1 value = (1/2 : ℂ) • R (1/2) value := by
  simp only [source, Finset.Ico_self, Finset.sum_empty, zero_sub, Nat.cast_one]
  rw [actual_inverse_normalization (1 : ℝ) zero_lt_one]
  simp only [Real.sqrt_one, Real.log_one, burnolMultiplicativeDilation_zero,
    neg_smul, neg_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

end OriginalRieszFinitePairing.CoPoisson.Ward.DualSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
