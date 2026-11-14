import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePointClock
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.ActionBand

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear

open BurnolPhysicalState BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory.FinitePointClock
open Filter MeasureTheory Set
open scoped InnerProductSpace Topology

open private orbit_has_derivative from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePointClock

local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "width" => (2 * Real.log 2)

private theorem width_pos : 0 < width := by positivity
private theorem window_order : -width ≤ width := by linarith [width_pos]

/-- The scalar test is supported in the actual local Pa dilation window of the comb. -/
def WithinWindow (test : SchwartzMap ℝ ℂ) : Prop :=
  tsupport (test : ℝ → ℂ) ⊆ Ioo (-width) width

private def orbit (h : ℝ) : BurnolL2 := D (h/2) seed

private theorem orbit_continuous : Continuous orbit :=
  (burnolMultiplicativeDilation_stronglyContinuous seed).comp (continuous_id.div_const 2)

private theorem orbit_mem {h : ℝ} (inside : h ∈ Ioc (-width) width) :
    orbit h ∈ burnolOriginalPaInL2 := by
  have small : |-(h/2)| ≤ Real.log 2 := by
    rw [abs_neg, abs_le]
    exact ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have band := burnolPaInteriorBand_dilation_mem (1 + burnolPaCombSourceWidth 0) (-(h/2))
    (by linarith [(burnolPaCombSourceWidth_bounds 0).1])
    (by linarith [(burnolPaCombSourceWidth_bounds 0).2]) small
  have fourier := burnolOriginalPaInL2_fourier band
  rw [fourierL2_burnolMultiplicativeDilation, neg_neg] at fourier
  unfold orbit
  rw [burnolPaCombApproximation_raw, map_smul]
  exact burnolOriginalPaInL2.smul_mem _ fourier

private def integrand (test : SchwartzMap ℝ ℂ) (h : ℝ) : BurnolL2 :=
  (star (test h)) • orbit h

private theorem integrand_integrable (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (integrand test) (Ioc (-width) width) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le window_order).mp
    (((Complex.continuous_conj.comp test.continuous).smul orbit_continuous).intervalIntegrable _ _)

/-- The original infinite Pa vector is synthesized from the actual local comb band. -/
def smear (test : SchwartzMap ℝ ℂ) : BurnolL2 :=
  ∫ h in Ioc (-width) width, integrand test h

theorem smear_mem (test : SchwartzMap ℝ ℂ) : smear test ∈ burnolOriginalPaInL2 := by
  apply integral_mem_closedSubmodule
    {toSubmodule := burnolOriginalPaInL2, isClosed' := burnolOriginalPaInL2_closed}
  · exact integrand_integrable test
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h inside
    exact burnolOriginalPaInL2.smul_mem _ (orbit_mem inside)

private def response (v : BurnolL2) (h : ℝ) : ℂ :=
  inner ℂ seed (D (-h/2) v)

private theorem response_continuous (v : BurnolL2) : Continuous (response v) :=
  (innerSL ℂ seed).continuous.comp ((burnolMultiplicativeDilation_stronglyContinuous v).comp
    (continuous_id.neg.div_const 2))

private theorem orbit_pair (v : BurnolL2) (h : ℝ) : inner ℂ (orbit h) v = response v h := by
  have forward : D (h/2) (D (-h/2) v) = v := by
    rw [burnolMultiplicativeDilation_add, show h/2 + -h/2 = 0 by ring,
      burnolMultiplicativeDilation_zero]
  simpa only [orbit, response, forward] using
    (D (h/2)).inner_map_map seed (D (-h/2) v)

private theorem smear_pair (test : SchwartzMap ℝ ℂ) (v : BurnolL2) :
    inner ℂ (smear test) v = ∫ h in (-width)..width, test h * response v h := by
  rw [← inner_conj_symm, smear, ← integral_inner (integrand_integrable test),
    ← integral_conj, intervalIntegral.integral_of_le window_order]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro h _
  change (starRingEnd ℂ) (inner ℂ v (star (test h) • orbit h)) = _
  rw [inner_conj_symm, inner_smul_left]
  simp only [starRingEnd_apply, star_star, orbit_pair]

/-- The genuine dual clock update associated with the original inward R equation. -/
def dualStep (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -SchwartzMap.derivCLM ℂ ℂ test - (c.value/2-1/4) • test

theorem dualStep_within (c : BurnolCompletedMellinCoordinate) {test : SchwartzMap ℝ ℂ}
    (locality : WithinWindow test) : WithinWindow (dualStep c test) := by
  apply Set.Subset.trans _ locality
  apply closure_minimal _ isClosed_closure
  intro h live
  by_contra outside
  have empty : test h = 0 := image_eq_zero_of_notMem_tsupport outside
  have flat : deriv (test : ℝ → ℂ) h = 0 := deriv_of_notMem_tsupport outside
  apply live
  simp [dualStep, SchwartzMap.derivCLM_apply, flat, empty]

private theorem response_derivative (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (h : ℝ) :
    HasDerivAt (response (R c v))
      ((c.value/2-1/4) * response (R c v) h + response v h) h := by
  have actual := ((innerSL ℂ seed).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt h
    (orbit_has_derivative c v h)
  change HasDerivAt (response (R c v))
    ((innerSL ℂ seed) (D (-h/2) (generatorWrite c v))) h at actual
  rw [generatorWrite, map_add, map_smul, map_add, map_smul] at actual
  exact actual

/-- One original R write and one generated Pa cotest write preserve the pairing on the entire L² source. -/
theorem smear_pays_actual_R (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ)
    (locality : WithinWindow test) (v : BurnolL2) :
    inner ℂ (smear (dualStep c test)) (R c v) = inner ℂ (smear test) v := by
  let f := response v
  let g := response (R c v)
  let a := c.value/2-1/4
  let slope (h : ℝ) : ℂ := deriv (test : ℝ → ℂ) h * g h + test h * (a * g h + f h)
  have first : test (-width) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx => (lt_irrefl _) (locality hx).1
  have last : test width = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx => (lt_irrefl _) (locality hx).2
  have slopeContinuous : Continuous slope := by
    exact (((SchwartzMap.derivCLM ℂ ℂ test).continuous).mul (response_continuous _)).add
      (test.continuous.mul ((continuous_const.mul (response_continuous _)).add (response_continuous _)))
  have boundary : (∫ h in (-width)..width, slope h) = 0 := by
    have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun h _ => (test.differentiableAt.hasDerivAt).mul (response_derivative c v h))
      (slopeContinuous.intervalIntegrable (-width) width)
    simpa only [Pi.mul_apply, first, last, zero_mul, sub_zero] using ftc
  rw [smear_pair, smear_pair]
  apply sub_eq_zero.mp
  have dualIntegrable : IntervalIntegrable (fun h => dualStep c test h * g h) volume (-width) width :=
    ((dualStep c test).continuous.mul (response_continuous _)).intervalIntegrable _ _
  have originalIntegrable : IntervalIntegrable (fun h => test h * f h) volume (-width) width :=
    (test.continuous.mul (response_continuous _)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub dualIntegrable originalIntegrable]
  calc
    _ = ∫ h in (-width)..width, -slope h := by
      apply intervalIntegral.integral_congr
      intro h _
      simp only [dualStep, sub_apply, neg_apply, smul_apply,
        SchwartzMap.derivCLM_apply, smul_eq_mul, slope, f, g, a]
      ring
    _ = 0 := by rw [intervalIntegral.integral_neg, boundary, neg_zero]

end OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
