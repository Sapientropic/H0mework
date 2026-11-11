import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Counting
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology ENNReal InnerProductSpace
local notation "μplus" => volume.restrict (Ioi (0:ℝ))

private def cutTerm (f:ℝ→ℂ) (T:ℝ) (n:ℕ):ℝ→ℂ:=
  (Ioc (0:ℝ) (T/((n+1:ℕ):ℝ))).indicator f

private def scaledTerm (f:ℝ→ℂ) (n:ℕ) (y:ℝ):ℂ:=
  (((n+1:ℕ):ℂ)⁻¹)*f (y/((n+1:ℕ):ℝ))

private theorem cut_integrable (f:ℝ→ℂ) (continuous:Continuous f) (T:ℝ) (n:ℕ):
    Integrable (cutTerm f T n) μplus:=
  ((integrable_indicator_iff measurableSet_Ioc).mpr
    (continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).integrableOn

private theorem cut_integral (f:ℝ→ℂ) (T:ℝ) (positive:0<T) (n:ℕ):
    (∫u:ℝ,cutTerm f T n u ∂μplus)=∫u:ℝ in (0:ℝ)..(T/((n+1:ℕ):ℝ)),f u:=by
  rw [cutTerm,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (div_nonneg positive.le (by positivity))]

private theorem cut_norm_integral (f:ℝ→ℂ) (T:ℝ) (positive:0<T) (n:ℕ):
    (∫u:ℝ,‖cutTerm f T n u‖ ∂μplus)=∫u:ℝ in (0:ℝ)..(T/((n+1:ℕ):ℝ)),‖f u‖:=by
  have read:(fun u:ℝ=>‖cutTerm f T n u‖)=
      (Ioc (0:ℝ) (T/((n+1:ℕ):ℝ))).indicator (fun u=>‖f u‖):=by
    funext u
    by_cases inside:u∈Ioc (0:ℝ) (T/((n+1:ℕ):ℝ))
    · simp only [cutTerm,indicator_of_mem inside]
    · simp only [cutTerm,indicator_of_notMem inside,norm_zero]
  rw [read,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (div_nonneg positive.le (by positivity))]

private theorem cut_norm_summable (f:ℝ→ℂ) (continuous:Continuous f)
    (A:ℝ) (nonnegative:0≤A) (growth:∀u:ℝ,0<u→‖f u‖≤A*u)
    (T:ℝ) (positive:0<T):Summable (fun n:ℕ=>∫u:ℝ,‖cutTerm f T n u‖ ∂μplus):=by
  have series:Summable (fun n:ℕ=>((n+1:ℕ):ℝ)^(-(2:ℝ))):=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  apply (series.mul_left (A*T^2)).of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _))
  intro n
  have np:(0:ℝ)<(n+1:ℕ):=by positivity
  rw [cut_norm_integral f T positive]
  calc
    _≤∫u:ℝ in (0:ℝ)..(T/((n+1:ℕ):ℝ)),A*(T/((n+1:ℕ):ℝ)):=by
      apply intervalIntegral.integral_mono_on (div_nonneg positive.le np.le)
        (continuous.norm.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      intro u inside
      rcases eq_or_lt_of_le inside.1 with atZero|positiveU
      · have atOrigin:‖f 0‖=0:=by
          have limiting:Tendsto (fun u:ℝ=>‖f u‖) (𝓝[>] 0) (𝓝 ‖f 0‖):=
            continuous.norm.continuousAt.tendsto.mono_left inf_le_left
          have bounds:∀ᶠu:ℝ in 𝓝[>] 0,‖f u‖≤A*u:=by
            filter_upwards [self_mem_nhdsWithin] with u up
            exact growth u up
          have right:Tendsto (fun u:ℝ=>A*u) (𝓝[>] 0) (𝓝 (A*0)):=
            (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left inf_le_left
          exact le_antisymm (by simpa only [mul_zero] using le_of_tendsto_of_tendsto limiting right bounds) (norm_nonneg _)
        rw [←atZero,atOrigin]
        positivity
      · exact (growth u positiveU).trans (mul_le_mul_of_nonneg_left inside.2 nonnegative)
    _=(A*T^2)*((n+1:ℕ):ℝ)^(-(2:ℝ)):=by
      rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,Real.rpow_neg np.le,Real.rpow_two]
      ring

private theorem floor_sum (f:ℝ→ℂ) (T u:ℝ) (positive:0<u):
    (∑'n:ℕ,cutTerm f T n u)=(⌊T/u⌋₊:ℂ)*f u:=by
  classical
  let M:ℕ:=⌊T/u⌋₊
  have active (n:ℕ):u∈Ioc (0:ℝ) (T/((n+1:ℕ):ℝ))↔n<M:=by
    simp only [mem_Ioc,positive,true_and]
    change u≤T/((n+1:ℕ):ℝ)↔n+1≤⌊T/u⌋₊
    rw [Nat.le_floor_iff' (Nat.succ_ne_zero n),le_div_iff₀ positive,
      le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))]
    rw [mul_comm]
  rw [tsum_eq_sum (s:=Finset.range M) (fun n outside=>by
    rw [cutTerm,indicator_of_notMem (by
      rw [active]
      simpa only [Finset.mem_range] using outside)])]
  have inside:∀n∈Finset.range M,cutTerm f T n u=f u:=by
    intro n hn
    exact indicator_of_mem ((active n).mpr (Finset.mem_range.mp hn)) f
  rw [Finset.sum_congr rfl inside]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,M]

private theorem scaled_integral (f:ℝ→ℂ) (T:ℝ) (positive:0<T) (n:ℕ):
    (∫y:ℝ in (0:ℝ)..T,scaledTerm f n y)=∫u:ℝ,cutTerm f T n u ∂μplus:=by
  have np:(0:ℝ)<(n+1:ℕ):=by positivity
  simp only [scaledTerm]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div f np.ne',
    zero_div,cut_integral f T positive,Complex.real_smul]
  simp only [Complex.ofReal_natCast]
  rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero n)),one_mul]

private theorem scaled_norm_integral (f:ℝ→ℂ) (T:ℝ) (positive:0<T) (n:ℕ):
    (∫y:ℝ in (0:ℝ)..T,‖scaledTerm f n y‖)=∫u:ℝ,‖cutTerm f T n u‖ ∂μplus:=by
  have np:(0:ℝ)<(n+1:ℕ):=by positivity
  simp only [scaledTerm,norm_mul,norm_inv,Complex.norm_natCast]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div (fun u:ℝ=>‖f u‖) np.ne',
    zero_div,cut_norm_integral f T positive,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ np.ne',one_mul]

/-- A finite ordinary interval computes the exact whole integer-grid adjoint floor kernel. -/
theorem actual_finite_counting_integral (f:ℝ→ℂ) (continuous:Continuous f)
    (A:ℝ) (nonnegative:0≤A) (growth:∀u:ℝ,0<u→‖f u‖≤A*u) (T:ℝ) (positive:0<T):
    (∫y:ℝ in (0:ℝ)..T,∑'n:ℕ,(((n+1:ℕ):ℂ)⁻¹)*f (y/((n+1:ℕ):ℝ)))=
      ∫u:ℝ in Ioi (0:ℝ),(⌊T/u⌋₊:ℂ)*f u:=by
  let μT:=volume.restrict (Ioc (0:ℝ) T)
  have scaledDomain (n:ℕ):Integrable (scaledTerm f n) μT:=
    ((continuous_const.mul (continuous.comp (continuous_id.div_const _))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have scaledNorm:Summable (fun n:ℕ=>∫y:ℝ,‖scaledTerm f n y‖ ∂μT):=by
    have original:=cut_norm_summable f continuous A nonnegative growth T positive
    have equality (n:ℕ):(∫y:ℝ,‖scaledTerm f n y‖ ∂μT)=∫u:ℝ,‖cutTerm f T n u‖ ∂μplus:=by
      rw [←intervalIntegral.integral_of_le positive.le]
      exact scaled_norm_integral f T positive n
    simpa only [equality] using original
  have left:=hasSum_integral_of_summable_integral_norm scaledDomain scaledNorm
  have right:=hasSum_integral_of_summable_integral_norm (cut_integrable f continuous T)
    (cut_norm_summable f continuous A nonnegative growth T positive)
  have integrals:(fun n:ℕ=>∫y:ℝ,scaledTerm f n y ∂μT)=(fun n:ℕ=>∫u:ℝ,cutTerm f T n u ∂μplus):=by
    funext n
    rw [←intervalIntegral.integral_of_le positive.le]
    exact scaled_integral f T positive n
  rw [integrals] at left
  have same:=left.unique right
  rw [←intervalIntegral.integral_of_le positive.le] at same
  change (∫y:ℝ in (0:ℝ)..T,∑'n:ℕ,(((n+1:ℕ):ℂ)⁻¹)*f (y/((n+1:ℕ):ℝ)))=_ at same
  refine same.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u up
  exact floor_sum f T u up

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Counting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
