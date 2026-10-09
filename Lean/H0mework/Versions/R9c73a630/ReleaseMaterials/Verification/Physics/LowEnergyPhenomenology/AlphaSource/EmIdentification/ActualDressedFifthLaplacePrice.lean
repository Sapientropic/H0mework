import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedObservedPolePrice
open Set Filter MeasureTheory
open scoped Topology

private theorem moment_integral (n : ℕ) (sigma : ℝ) (positive : 0<sigma) :
    (∫t : ℝ in Ioi 0,t^n*Real.exp (-(sigma*t)))=
      (1/sigma)^(n+1)*(n.factorial:ℝ) := by
  have source:=Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a:=(n:ℝ)+1) (r:=sigma) (by positivity) positive
  have cast : (n:ℝ)+1=((n+1:ℕ):ℝ) := by norm_cast
  rw [cast,Real.rpow_natCast] at source
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast,Real.Gamma_nat_eq_factorial] using source

private theorem moment_integrable (n : ℕ) (sigma : ℝ) (positive : 0<sigma) :
    IntegrableOn (fun t : ℝ=>t^n*Real.exp (-(sigma*t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [moment_integral n sigma positive]
  positivity

private theorem fifth_polynomial_price (t : ℝ) (future : 0≤t) :
    (1+t)^5≤32*(1+t^5) := by
  by_cases small : t≤1
  · have power : (1+t)^5≤(2:ℝ)^5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    norm_num at power
    nlinarith [pow_nonneg future 5]
  · have power : (1+t)^5≤(2*t)^5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    nlinarith [power]

theorem fifth_laplace_integrable (sigma : ℝ) (positive : 0<sigma) :
    IntegrableOn (fun t : ℝ=>Real.exp (-(sigma*t))*(1+t)^5) (Ioi 0) := by
  have zeroth : IntegrableOn (fun t : ℝ=>Real.exp (-(sigma*t))) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using moment_integrable 0 sigma positive
  have fifth:=moment_integrable 5 sigma positive
  have majorant:= (zeroth.add fifth).const_mul 32
  have continuous : Continuous (fun t : ℝ=>Real.exp (-(sigma*t))*(1+t)^5) := by fun_prop
  apply majorant.mono' continuous.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
  have future0 : 0≤t := future.le
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have bound:=mul_le_mul_of_nonneg_left (fifth_polynomial_price t future.le)
    (Real.exp_nonneg (-(sigma*t)))
  exact bound.trans_eq (by simp only [Pi.add_apply];ring)

/-- A fixed fifth-degree price has sixth-order damping cost, with an explicit scale-free coefficient. -/
theorem fifth_laplace_sigma_six_price (sigma : ℝ) (positive : 0<sigma) (small : sigma≤1) :
    sigma^6*(∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)^5)≤3872 := by
  have zeroth : IntegrableOn (fun t : ℝ=>Real.exp (-(sigma*t))) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using moment_integrable 0 sigma positive
  have fifth:=moment_integrable 5 sigma positive
  have bound : (∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)^5)≤
      32*(1/sigma+120*(1/sigma)^6) := by
    calc
      _≤∫t : ℝ in Ioi 0,32*(Real.exp (-(sigma*t))+t^5*Real.exp (-(sigma*t))) := by
        apply integral_mono_ae (fifth_laplace_integrable sigma positive) ((zeroth.add fifth).const_mul 32)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
        exact (mul_le_mul_of_nonneg_left (fifth_polynomial_price t future.le)
          (Real.exp_nonneg _)).trans_eq (by simp only [Pi.add_apply];ring)
      _=32*(1/sigma+120*(1/sigma)^6) := by
        rw [integral_const_mul,integral_add zeroth fifth]
        have zero:=moment_integral 0 sigma positive
        have five:=moment_integral 5 sigma positive
        simp only [pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one,mul_one] at zero
        rw [zero,five]
        norm_num
        ring
  have algebra : sigma^6*(32*(1/sigma+120*(1/sigma)^6))=32*(sigma^5+120) := by
    field_simp [positive.ne']
  have power : sigma^5≤1 := pow_le_one₀ positive.le small
  exact ((mul_le_mul_of_nonneg_left bound (pow_nonneg positive.le 6)).trans_eq algebra).trans
    (by nlinarith)

end LowEnergy.GaussComposite.ActualDressedObservedPolePrice
