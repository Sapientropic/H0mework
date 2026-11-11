import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Fourier
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Moment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair
open scoped Topology InnerProductSpace
open private forcing_positive_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RegularQuadrature
local notation "q" => (1/4:ℝ)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)
local notation "λ₀" => ForcingPrimitive.leadingCoefficient

def remainderRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ :=
  resolvedFourierRaw c x-λ₀ c*(x:ℂ)^(star c.value-1)

private theorem remainder_read (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x):
    remainderRaw c x=ForcingTail.forcingRemainder c x-jumpCoefficient c*box x := by
  rw [remainderRaw,resolvedFourierRaw,forcing_positive_read c x positive]
  ring

/-- The actual weak forcing head and the actual resolved Fourier tail bound one whole remainder. -/
theorem actual_remainder_bound (c:BurnolCompletedMellinCoordinate):
    ∃B:ℝ,0≤B∧∀x:ℝ,0<x→‖remainderRaw c x‖≤B := by
  have head:ContinuousOn (fun x:ℝ=>ForcingTail.forcingRemainder c x-jumpCoefficient c*box x)
      (Icc (0:ℝ) q):=
    (RegularQuadrature.forcing_continuous c).sub
      (continuous_const.mul (burnolRadiusTruncatedFourierRaw_continuous _)).continuousOn
  obtain ⟨C,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn head
  have nonnegative:0≤C:=(norm_nonneg _).trans (bounded 0 (by constructor <;> norm_num))
  let D:ℝ:=tailBound c/q^2+‖λ₀ c‖*q^(c.value.re-1)
  have dnonnegative:0≤D:=by dsimp [D];positivity [tailBound_nonnegative c]
  refine ⟨C+D,add_nonneg nonnegative dnonnegative,fun x positive=>?_⟩
  by_cases small:x≤q
  · rw [remainder_read c x positive]
    exact (bounded x ⟨positive.le,small⟩).trans (le_add_of_nonneg_right dnonnegative)
  · have large:q≤x:=le_of_not_ge small
    have fourier:‖resolvedFourierRaw c x‖≤tailBound c/q^2 := by
      have native:=actual_resolved_fourier_bound c x positive.ne'
      rw [abs_of_pos positive] at native
      exact native.trans (div_le_div_of_nonneg_left (tailBound_nonnegative c)
        (by norm_num : (0:ℝ)<q^2) (by nlinarith))
    have power:‖(x:ℂ)^(star c.value-1)‖≤q^(c.value.re-1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos positive]
      simp only [sub_re,star_def,conj_re,one_re]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) large (by linarith [c.belowOne])
    have native:‖remainderRaw c x‖≤D := by
      apply (norm_sub_le _ _).trans
      rw [norm_mul]
      exact add_le_add fourier (mul_le_mul_of_nonneg_left power (norm_nonneg _))
    exact native.trans (le_add_of_nonneg_left nonnegative)

private theorem power_scale (c:BurnolCompletedMellinCoordinate) (h x:ℝ) (positive:0<x):
    Complex.exp ((h:ℂ)*(star c.value-1))*
      ((Real.exp (-h)*x:ℝ):ℂ)^(star c.value-1)=(x:ℂ)^(star c.value-1) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Real.exp_pos (-h)).le positive.le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-h))),
    ←Complex.ofReal_log (Real.exp_pos (-h)).le,Real.log_exp,←mul_assoc,←Complex.exp_add]
  have cancel:(h:ℂ)*(star c.value-1)+((-h:ℝ):ℂ)*(star c.value-1)=0 := by
    push_cast
    ring
  rw [cancel,Complex.exp_zero,one_mul]

def errorReading (c:BurnolCompletedMellinCoordinate) (n:ℕ) (x:ℝ):ℂ :=
  fourierReading c n x-λ₀ c*gaussianPower (star c.value) x

private theorem actual_error_read (c:BurnolCompletedMellinCoordinate) (n:ℕ)
    (x:ℝ) (positive:0<x):
    errorReading c n x=Complex.exp ((n:ℂ)*(star c.value-1))*
      remainderRaw c (Real.exp (-(n:ℝ))*x)*burnolGaussianRaw 1 x := by
  have power:=power_scale c n x positive
  simp only [Complex.ofReal_natCast] at power
  unfold errorReading fourierReading gaussianPower remainderRaw
  simp only [Complex.ofReal_natCast]
  linear_combination λ₀ c*burnolGaussianRaw 1 x*power

private theorem scale_norm (c:BurnolCompletedMellinCoordinate) (n:ℕ):
    ‖Complex.exp ((n:ℂ)*(star c.value-1))‖=Real.exp ((n:ℝ)*(c.value.re-1)) := by
  simp only [Complex.norm_exp,mul_re,natCast_re,natCast_im,sub_re,star_def,conj_re,one_re,
    zero_mul,sub_zero]

private theorem scale_decay (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun n:ℕ=>‖Complex.exp ((n:ℂ)*(star c.value-1))‖) atTop (𝓝 0) := by
  simp_rw [scale_norm]
  apply Real.tendsto_exp_atBot.comp
  exact (tendsto_mul_const_atBot_of_neg (by linarith [c.belowOne])).mpr
    (tendsto_natCast_atTop_atTop (R:=ℝ))

private theorem scale_bound (c:BurnolCompletedMellinCoordinate) (n:ℕ):
    ‖Complex.exp ((n:ℂ)*(star c.value-1))‖≤1 := by
  rw [scale_norm,Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith [c.belowOne])

private theorem error_integrable (c:BurnolCompletedMellinCoordinate) (n:ℕ):
    IntegrableOn (errorReading c n) (Ioi 0) :=
  (actual_fourier_integrable c n).sub
    ((actual_gaussian_power_integrable (star c.value) (by simp only [star_def,conj_re];linarith [c.rightHalf])).const_mul (λ₀ c))

/-- The source remainder vanishes under the actual shrinking Fourier clock, with a Gaussian dominator. -/
theorem actual_error_integral_limit (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun n:ℕ=>∫x:ℝ in Ioi 0,errorReading c n x) atTop (𝓝 0) := by
  obtain ⟨B,nonnegative,bound⟩:=actual_remainder_bound c
  have errorBound (n:ℕ) (x:ℝ) (positive:0<x):
      ‖errorReading c n x‖≤‖Complex.exp ((n:ℂ)*(star c.value-1))‖*
        B*‖burnolGaussianRaw 1 x‖ := by
    rw [actual_error_read c n x positive,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (bound _ (mul_pos (Real.exp_pos _) positive)) (norm_nonneg _))
      (norm_nonneg _)
  have generated:Tendsto (fun n:ℕ=>∫x:ℝ in Ioi 0,errorReading c n x) atTop
      (𝓝 (∫x:ℝ in Ioi 0,(0:ℂ))) := by
    apply tendsto_integral_of_dominated_convergence (fun x=>B*‖burnolGaussianRaw 1 x‖)
    · intro n
      exact (error_integrable c n).aestronglyMeasurable
    · exact ((burnolGaussianRaw_integrable (by norm_num : (0:ℝ)<1)).norm.const_mul B).integrableOn
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positive
      apply (errorBound n x positive).trans
      have scalar:=mul_le_mul_of_nonneg_right (scale_bound c n) nonnegative
      simpa only [one_mul] using mul_le_mul_of_nonneg_right scalar (norm_nonneg (burnolGaussianRaw 1 x))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positive
      apply squeeze_zero_norm (fun n=>errorBound n x positive)
      simpa only [zero_mul] using ((scale_decay c).mul_const B).mul_const ‖burnolGaussianRaw 1 x‖
  simpa only [integral_zero] using generated

/-- The actual original Fourier Gaussian reading computes the original forcing coefficient. -/
theorem actual_fourier_gaussian_limit (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun n:ℕ=>∫x:ℝ in Ioi 0,fourierReading c n x) atTop
      (𝓝 (λ₀ c*Gammaℝ (star c.value)/2)) := by
  have powerPositive:0<(star c.value).re:=by simp only [star_def,conj_re];linarith [c.rightHalf]
  have read (n:ℕ):(∫x:ℝ in Ioi 0,errorReading c n x)=
      (∫x:ℝ in Ioi 0,fourierReading c n x)-λ₀ c*Gammaℝ (star c.value)/2 := by
    unfold errorReading
    rw [integral_sub (actual_fourier_integrable c n)
      ((actual_gaussian_power_integrable (star c.value) powerPositive).const_mul (λ₀ c)),
      integral_const_mul,actual_gaussian_power_integral (star c.value) powerPositive]
    ring
  have limit:=(actual_error_integral_limit c).add_const (λ₀ c*Gammaℝ (star c.value)/2)
  simpa only [read,sub_add_cancel,zero_add] using limit

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Fourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
