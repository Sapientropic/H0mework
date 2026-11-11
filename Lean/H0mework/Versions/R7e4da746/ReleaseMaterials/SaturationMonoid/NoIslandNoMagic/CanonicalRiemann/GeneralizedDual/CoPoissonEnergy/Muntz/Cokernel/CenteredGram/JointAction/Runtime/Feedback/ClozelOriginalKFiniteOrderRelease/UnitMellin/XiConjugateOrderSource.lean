import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.BareRiemannZeroLocalizedAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann
namespace OriginalUnitXiConjugateOrderSource
open Complex Filter Set
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped Topology
local notation "owner" => ActualAnalyticOwner
local notation "order" => generatedRiemannXiZeroOrder owner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum owner

private theorem gamma_analytic (w : ℂ) (positive : 0 < w.re) : AnalyticAt ℂ Gammaℝ w := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(continuous_re.tendsto w).eventually (Ioi_mem_nhds positive)] with z inside
  have gamma : DifferentiableAt ℂ Gamma (z / 2) :=
    Complex.differentiableAt_Gamma _ (by
      intro n equal
      have part : z.re / 2 = -(n : ℝ) := by simpa using congrArg Complex.re equal
      have nonnegative : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  unfold Gammaℝ
  exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      (gamma.comp z (differentiableAt_id.div_const (2 : ℂ)))

private theorem below_ne_one (c : BurnolCompletedMellinCoordinate) : c.value ≠ 1 := by
  intro same
  have below := c.belowOne
  rw [same] at below
  norm_num at below

private theorem above_ne_zero (c : BurnolCompletedMellinCoordinate) : c.value ≠ 0 := by
  intro same
  have above := c.rightHalf
  rw [same] at above
  norm_num at above

private theorem bare_analytic (c : BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ (bare c.value) c.value := by
  have numerator := ((generatedRiemannXi_hasFPowerSeriesAt owner c.value
    ).has_fpower_series_iterate_dslope_fslope (order c.value)).analyticAt
  have denominator : AnalyticAt ℂ (fun z : ℂ => z * (1 - z) * Gammaℝ z) c.value :=
    (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).mul
      (gamma_analytic c.value (by linarith [c.rightHalf]))
  exact numerator.div denominator
    (mul_ne_zero (mul_ne_zero (above_ne_zero c) (sub_ne_zero.mpr (below_ne_one c).symm))
      (Gammaℝ_ne_zero_of_re_pos (by linarith [c.rightHalf])))

private theorem bare_nonzero (c : BurnolCompletedMellinCoordinate) : bare c.value c.value ≠ 0 := by
  apply div_ne_zero
  · exact generatedRiemannXiZeroLocalization_at_ne_zero owner c.value
  · exact mul_ne_zero (mul_ne_zero (above_ne_zero c) (sub_ne_zero.mpr (below_ne_one c).symm))
      (Gammaℝ_ne_zero_of_re_pos (by linarith [c.rightHalf]))

private theorem bare_factor (c : BurnolCompletedMellinCoordinate) :
    riemannZeta =ᶠ[𝓝 c.value] fun z => (z - c.value) ^ order c.value • bare c.value z := by
  have near : ∀ᶠ z : ℂ in 𝓝 c.value, 0 < z.re ∧ z.re < 1 :=
    ((continuous_re.tendsto c.value).eventually
      (Ioi_mem_nhds (by linarith [c.rightHalf]))).and
      ((continuous_re.tendsto c.value).eventually (Iio_mem_nhds c.belowOne))
  filter_upwards [near] with z inside
  have nonzero : z ≠ 0 := by
    intro same
    simpa only [same, Complex.zero_re, lt_self_iff_false] using inside.1
  have notOne : z ≠ 1 := by
    intro same
    simpa only [same, Complex.one_re, lt_self_iff_false] using inside.2
  have source := generatedRiemannZeta_zero_factorization owner c.value z nonzero notOne
    (Gammaℝ_ne_zero_of_re_pos inside.1)
  rw [generatedRiemannZeta_eq_mathlib] at source
  exact source

private theorem analytic_conjugate {f : ℂ → ℂ} {coordinate : ℂ}
    (source : AnalyticAt ℂ f coordinate) :
    AnalyticAt ℂ (fun z => star (f (star z))) (star coordinate) := by
  rw [analyticAt_iff_eventually_differentiableAt] at source ⊢
  have native : Tendsto (fun z : ℂ => star z) (𝓝 (star coordinate)) (𝓝 coordinate) := by
    simpa only [star_star] using continuous_star.tendsto (star coordinate)
  filter_upwards [native.eventually source] with z paid
  simpa only [Function.comp_def, starRingEnd_apply, star_star] using paid.conj_conj

/-- Both multiplicities belong to the original theta--Mellin owner and its exact Xi factorization. -/
theorem actual_original_Xi_order_conjugate (c : BurnolCompletedMellinCoordinate) :
    order (star c.value) = order c.value := by
  let conjugate : BurnolCompletedMellinCoordinate :=
    ⟨star c.value, by simpa only [Complex.star_def, Complex.conj_re] using c.rightHalf,
      by simpa only [Complex.star_def, Complex.conj_re] using c.belowOne⟩
  let coefficient : ℂ → ℂ := fun z => star (bare c.value (star z))
  have analytic : AnalyticAt ℂ coefficient (star c.value) := analytic_conjugate (bare_analytic c)
  have nonzero : coefficient (star c.value) ≠ 0 := by
    simpa only [coefficient, star_star] using star_ne_zero.mpr (bare_nonzero c)
  have native : Tendsto (fun z : ℂ => star z) (𝓝 (star c.value)) (𝓝 c.value) := by
    simpa only [star_star] using continuous_star.tendsto (star c.value)
  have generated : riemannZeta =ᶠ[𝓝 (star c.value)]
      fun z => (z - star c.value) ^ order c.value • coefficient z := by
    filter_upwards [native.eventually (bare_factor c)] with z field
    have source := congrArg (starRingEnd ℂ) field
    rw [show riemannZeta (star z) = star (riemannZeta z) from riemannZeta_conj z] at source
    simpa only [starRingEnd_apply, star_star, star_mul, star_pow, star_sub, smul_eq_mul,
      coefficient, mul_comm] using source
  exact (AnalyticAt.unique_eventuallyEq_pow_smul_nonzero
    ⟨coefficient, analytic, nonzero, generated⟩
    ⟨bare conjugate.value, bare_analytic conjugate, bare_nonzero conjugate,
      bare_factor conjugate⟩).symm

end OriginalUnitXiConjugateOrderSource
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
