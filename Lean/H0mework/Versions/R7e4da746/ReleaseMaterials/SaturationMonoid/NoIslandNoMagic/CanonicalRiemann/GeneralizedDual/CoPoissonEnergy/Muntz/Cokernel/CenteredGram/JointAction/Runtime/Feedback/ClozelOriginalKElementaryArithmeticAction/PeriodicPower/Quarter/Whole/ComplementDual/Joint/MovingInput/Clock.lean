import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Band

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Clock
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Band OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)

private theorem linear_band_change (h : ℝ) (w f : ℝ → ℂ) :
    (∫ t : ℝ in q..q*Real.exp h, w t * f (Real.exp (-h)*t)) =
      (Real.exp h : ℂ) * ∫ u : ℝ in q*Real.exp (-h)..q, w (Real.exp h*u) * f u := by
  have cancel (u : ℝ) : Real.exp (-h)*(Real.exp h*u) = u := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have endpoint : Real.exp h*(q*Real.exp (-h)) = q := by
    rw [mul_comm q, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have source := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => w t*f (Real.exp (-h)*t)) (a := q*Real.exp (-h)) (b := q) (Real.exp h)
  simp only [cancel, endpoint, mul_comm (Real.exp h) q, Complex.real_smul] at source
  exact source.symm

private theorem reciprocal_band_change (a : ℝ) (positive : 0 < a) (bounded : a ≤ 1) (w f : ℝ → ℂ) :
    (∫ t : ℝ in 4*a..4, w t * (t : ℂ)⁻¹ * f (a/t)) =
      ∫ u : ℝ in q*a..q, w (a/u) * (u : ℂ)⁻¹ * f u := by
  let F : ℝ → ℝ := fun t => a/t
  let F' : ℝ → ℝ := fun t => -a/t^2
  let g : ℝ → ℂ := fun u => w (a/u)*(u : ℂ)⁻¹*f u
  have ordered : 4*a ≤ (4 : ℝ) := by linarith
  have continuous : ContinuousOn F (uIcc (4*a) 4) :=
    continuousOn_const.div continuousOn_id (fun t inside => by
      rw [uIcc_of_le ordered] at inside
      change t ≠ 0
      nlinarith only [positive, inside.1])
  have derivative : ∀ t ∈ Ioo (min (4*a) 4) (max (4*a) 4), HasDerivAt F (F' t) t := by
    intro t inside
    rw [min_eq_left ordered, max_eq_right ordered] at inside
    have tn : t ≠ 0 := by nlinarith only [positive, inside.1]
    simpa only [F,F', id_eq, zero_mul, mul_one, zero_sub] using!
      (hasDerivAt_const t a).div (hasDerivAt_id t) tn
  have negative : ∀ t ∈ Ioo (min (4*a) 4) (max (4*a) 4), F' t ≤ 0 :=
    fun t _ => div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have source := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (g := g) continuous derivative negative
  have start : F (4*a) = q := by dsimp only [F]; field_simp [positive.ne']
  have stop : F 4 = q*a := by dsimp only [F]; ring
  rw [start, stop] at source
  nth_rw 2 [intervalIntegral.integral_symm] at source
  have integrand : (∫ t : ℝ in 4*a..4, F' t • (g ∘ F) t) =
      -(∫ t : ℝ in 4*a..4, w t*(t : ℂ)⁻¹*f (a/t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t inside
    rw [uIcc_of_le ordered] at inside
    have tn : t ≠ 0 := by nlinarith only [positive, inside.1]
    have inverse : a/(a/t) = t := by field_simp [positive.ne',tn]
    dsimp only [F,F',g,Function.comp_apply]
    rw [inverse, Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne', Complex.ofReal_ne_zero.mpr tn, positive.ne', tn]
  rw [integrand] at source
  exact neg_injective source

def lowerClockBand (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) : ℂ :=
  ∫ u : ℝ in Icc (q*Real.exp (-h)) q,
    (u : ℂ)^(-c.value) * ((h : ℂ)+(Real.log (u/q) : ℂ))^j * burnolRieszSingleFourierSourceRaw c u

def upperClockBand (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) : ℂ :=
  ∫ u : ℝ in Icc (q*Real.exp (-h)) q,
    (u : ℂ)^(c.value-1) * (Real.log (Real.exp (-h)/(q*u)) : ℂ)^j * positionSource c u

private theorem lower_weight (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) (u : ℝ) (positive : 0 < u) :
    portWeight c j (Real.exp h*u) = (Real.exp h : ℂ)^(-c.value) *
      ((u : ℂ)^(-c.value) * ((h : ℂ)+(Real.log (u/q) : ℂ))^j) := by
  have argument : Real.exp h*u/q = Real.exp h*(u/q) := by ring
  rw [portWeight, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le positive.le,
    argument, Real.log_mul (Real.exp_ne_zero _) (div_ne_zero positive.ne' (by norm_num)), Real.log_exp,
    Complex.ofReal_add]
  ring

private theorem upper_weight (c : BurnolCompletedMellinCoordinate) (h : ℝ) (j : ℕ) (u : ℝ) (positive : 0 < u) :
    portWeight c j (Real.exp (-h)/u) * (u : ℂ)⁻¹ = (Real.exp (-h) : ℂ)^(-c.value) *
      ((u : ℂ)^(c.value-1) * (Real.log (Real.exp (-h)/(q*u)) : ℂ)^j) := by
  have argument : (Real.exp (-h)/u)/q = Real.exp (-h)/(q*u) := by ring
  have power : (u : ℂ)^c.value*(u : ℂ)⁻¹ = (u : ℂ)^(c.value-1) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
  rw [portWeight, argument, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le (inv_nonneg.mpr positive.le),
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg positive.le,
    ← Complex.cpow_neg, neg_neg]
  linear_combination (Real.exp (-h) : ℂ)^(-c.value) *
    (Real.log (Real.exp (-h)/(q*u)) : ℂ)^j * power

private theorem exp_cpow (h : ℝ) (z : ℂ) : (Real.exp h : ℂ)^z = Complex.exp (z*(h : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  congr 1
  ring

/-- Both true source bands are calculated on the same finite q-clock; the reciprocal clock is retained. -/
theorem actual_lower_clock (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) (j : ℕ) :
    lowerBand c h j = (Real.exp h : ℂ)*(Real.exp h : ℂ)^(-c.value) * lowerClockBand c h j := by
  have aLe : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have lowOrder : q*Real.exp (-h) ≤ q := by nlinarith
  have highOrder : q ≤ q*Real.exp h := le_mul_of_one_le_right (by norm_num) (Real.one_le_exp_iff.mpr nonnegative)
  rw [lowerBand, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le highOrder,
    linear_band_change]
  have weighted : (∫ u : ℝ in q*Real.exp (-h)..q,
      portWeight c j (Real.exp h*u)*burnolRieszSingleFourierSourceRaw c u) =
      (Real.exp h : ℂ)^(-c.value) * lowerClockBand c h j := by
    rw [intervalIntegral.integral_of_le lowOrder, ← integral_Icc_eq_integral_Ioc,
      lowerClockBand, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u inside
    dsimp only
    rw [lower_weight c h j u (lt_of_lt_of_le (by positivity : 0 < q*Real.exp (-h)) inside.1)]
    ring
  rw [weighted]
  ring

theorem actual_upper_clock (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) (j : ℕ) :
    upperBand c h j = (Real.exp (-h) : ℂ)^(-c.value) * upperClockBand c h j := by
  have aLe : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have lowOrder : q*Real.exp (-h) ≤ q := by nlinarith
  have highOrder : 4*Real.exp (-h) ≤ 4 := by nlinarith
  have argument (t : ℝ) : (Real.exp h*t)⁻¹ = Real.exp (-h)/t := by
    rw [mul_inv_rev, Real.exp_neg, div_eq_mul_inv, mul_comm]
  rw [upperBand, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le highOrder]
  simp_rw [argument]
  rw [reciprocal_band_change _ (Real.exp_pos _) aLe,
    intervalIntegral.integral_of_le lowOrder, ← integral_Icc_eq_integral_Ioc,
    upperClockBand, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u inside
  dsimp only
  rw [upper_weight c h j u (lt_of_lt_of_le (by positivity : 0 < q*Real.exp (-h)) inside.1)]
  ring

/-- Literal original port fee, with the two true reciprocal characters and both complete B feet. -/
theorem actual_joint_clock_moment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (j : ℕ) :
    jointMoment c zero h j =
      -(Complex.exp (((1/2 : ℂ)-c.value)*(h : ℂ)))/2 * lowerClockBand c h j -
      (Complex.exp ((c.value-1/2)*(h : ℂ)))/2 * upperClockBand c h j := by
  rw [actual_joint_band_moment c zero h nonnegative bounded j,
    actual_lower_clock c h nonnegative j, actual_upper_clock c h nonnegative j]
  have lower : (Real.exp (-h/2) : ℂ)*(Real.exp h : ℂ)*(Real.exp h : ℂ)^(-c.value) =
      Complex.exp (((1/2 : ℂ)-c.value)*(h : ℂ)) := by
    rw [exp_cpow, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have upper : (Real.exp (-h/2) : ℂ)*(Real.exp (-h) : ℂ)^(-c.value) =
      Complex.exp ((c.value-1/2)*(h : ℂ)) := by
    rw [exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination -(lowerClockBand c h j)/2 * lower - (upperClockBand c h j)/2 * upper

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Clock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
