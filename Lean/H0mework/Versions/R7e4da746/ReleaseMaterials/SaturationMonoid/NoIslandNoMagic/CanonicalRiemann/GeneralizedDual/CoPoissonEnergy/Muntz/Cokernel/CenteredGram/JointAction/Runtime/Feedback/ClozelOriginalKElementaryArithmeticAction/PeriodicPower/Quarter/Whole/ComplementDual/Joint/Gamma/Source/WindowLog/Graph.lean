import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Kernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Budget

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WindowLog

open Complex Filter MeasureTheory Set
open OriginalGamma.Source.FiniteLogCounting
open private powerProfile from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
open private profile_nonnegative from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Budget

private def logarithmicKernel (x y : ℝ) : ℂ :=
  ((Real.log (|x|) - Real.log (|y|) : ℝ) : ℂ) * quarterSincKernel x y

private def logarithmicRead (v : BurnolL2) (x : ℝ) : ℂ :=
  ∫ y : ℝ, logarithmicKernel x y * v y

private theorem logarithmic_kernel_measurable :
    Measurable (fun xy : ℝ × ℝ => logarithmicKernel xy.1 xy.2) := by
  unfold logarithmicKernel quarterSincKernel
  have sincMeasured : Measurable (fun y : ℝ =>
      burnolRadiusTruncatedFourierRaw (1/4 : ℝ) (intervalConstant (1/4 : ℝ)) y) :=
    (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant (1/4 : ℝ))).measurable
  exact (by fun_prop : Measurable (fun xy : ℝ × ℝ =>
    ((Real.log (|xy.1|) - Real.log (|xy.2|) : ℝ) : ℂ))).mul
    ((Complex.continuous_conj.measurable.comp (sincMeasured.comp (by fun_prop))))

private theorem logarithmic_integrand_bound (v : BurnolL2) (x y : ℝ)
    (nonzeroX : x ≠ 0) (nonzeroY : y ≠ 0) (offDiagonal : x ≠ y) :
    ‖logarithmicKernel x y * v y‖ ≤
      (8 / |x|) * (powerProfile (|y|/|x|) * ‖v y‖) := by
  have denominator := abs_ne_zero.mpr (sub_ne_zero.mpr offDiagonal)
  have positive := abs_pos.mpr nonzeroX
  have factor : 0 ≤ 8 * powerProfile (|y|/|x|) / |x| :=
    div_nonneg (mul_nonneg (by norm_num) (profile_nonnegative (div_nonneg (abs_nonneg y) positive.le))) positive.le
  have bound := mul_le_mul (log_difference_budget x y nonzeroX nonzeroY)
    (quarter_sinc_kernel_bound offDiagonal) (norm_nonneg _)
    (mul_nonneg factor (abs_nonneg _))
  rw [logarithmicKernel, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have cancel : (8 * powerProfile (|y|/|x|) / |x|) * |x-y| * |x-y|⁻¹ =
      8 * powerProfile (|y|/|x|) / |x| := by
    rw [mul_assoc, mul_inv_cancel₀ denominator, mul_one]
  calc
    _ ≤ ((8 * powerProfile (|y|/|x|) / |x|) * |x-y| * |x-y|⁻¹) * ‖v y‖ :=
      mul_le_mul_of_nonneg_right bound (norm_nonneg _)
    _ = _ := by rw [cancel]; ring

private theorem logarithmic_integrand_measurable (v : BurnolL2) :
    Measurable (fun xy : ℝ × ℝ => logarithmicKernel xy.1 xy.2 * v xy.2) :=
  logarithmic_kernel_measurable.mul ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)

private theorem logarithmic_row_integrable (v : BurnolL2) (x : ℝ) (nonzero : x ≠ 0) :
    Integrable (fun y : ℝ => logarithmicKernel x y * v y) := by
  apply ((ratio_budget_integrable v x nonzero).const_mul (8/|x|)).mono'
    ((logarithmic_integrand_measurable v).comp (by fun_prop :
      Measurable (fun y : ℝ => (x, y)))).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne x] with y ny diagonal
  exact logarithmic_integrand_bound v x y nonzero ny (Ne.symm diagonal)

private theorem logarithmic_read_memLp (v : BurnolL2) :
    MemLp (logarithmicRead v) 2 volume := by
  apply (Lp.memLp (quarterLogClockBudget v)).of_le_mul (c := 8)
    (logarithmic_integrand_measurable v).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  filter_upwards [quarter_log_clock_read v, volume.ae_ne (0 : ℝ)] with x read nonzero
  have positive := abs_pos.mpr nonzero
  have integralNonnegative : 0 ≤ ∫ y : ℝ, powerProfile (|y|/|x|) * ‖v y‖ :=
    integral_nonneg fun y => mul_nonneg
      (profile_nonnegative (div_nonneg (abs_nonneg y) positive.le)) (norm_nonneg _)
  have budget := (ratio_budget_integrable v x nonzero).const_mul (8/|x|)
  have bound : ∀ᵐ y : ℝ ∂volume, ‖logarithmicKernel x y * v y‖ ≤
      (8 / |x|) * (powerProfile (|y|/|x|) * ‖v y‖) := by
    filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne x] with y ny diagonal
    exact logarithmic_integrand_bound v x y nonzero ny (Ne.symm diagonal)
  rw [read, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg integralNonnegative positive.le)]
  calc
    ‖logarithmicRead v x‖ ≤ ∫ y : ℝ, ‖logarithmicKernel x y * v y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (8/|x|) * (powerProfile (|y|/|x|) * ‖v y‖) :=
      integral_mono_ae (logarithmic_row_integrable v x nonzero).norm budget bound
    _ = _ := by rw [integral_const_mul]; ring

/-- The actual sharp-window logarithmic commutator is generated on the whole L² carrier. -/
def quarterLogCommutator (v : BurnolL2) : BurnolL2 :=
  (logarithmic_read_memLp v).toLp (logarithmicRead v)

def quarterFourierCutLog (v logged : BurnolL2) : BurnolL2 :=
  quarterFourierCut logged + quarterLogCommutator v

theorem quarter_fourier_cut_log_pair (v logged : BurnolL2) (source : LogPair v logged) :
    LogPair (quarterFourierCut v) (quarterFourierCutLog v logged) := by
  filter_upwards [quarter_cut_raw v, quarter_cut_raw logged,
    (logarithmic_read_memLp v).coeFn_toLp,
    Lp.coeFn_add (quarterFourierCut logged) (quarterLogCommutator v), volume.ae_ne (0 : ℝ)]
    with x cut logCut comm add nonzero
  change (quarterFourierCut logged + quarterLogCommutator v) x =
    (Real.log (|x|) : ℂ) * quarterFourierCut v x
  change (quarterFourierCut logged + quarterLogCommutator v) x =
    quarterFourierCut logged x + quarterLogCommutator v x at add
  change quarterLogCommutator v x = logarithmicRead v x at comm
  rw [add, logCut, comm, cut, logarithmicRead,
    ← integral_add (quarter_sinc_integrable_row logged x) (logarithmic_row_integrable v x nonzero),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [source] with y loggedRead
  rw [loggedRead, logarithmicKernel, Complex.ofReal_sub]
  ring

end OriginalGamma.Source.WindowLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
