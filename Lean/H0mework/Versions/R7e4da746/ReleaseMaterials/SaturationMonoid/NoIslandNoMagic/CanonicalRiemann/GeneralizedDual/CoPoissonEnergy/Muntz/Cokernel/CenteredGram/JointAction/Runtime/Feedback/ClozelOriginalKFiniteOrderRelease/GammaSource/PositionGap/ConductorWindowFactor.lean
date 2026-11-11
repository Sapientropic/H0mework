import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.WeightedRadialKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Fourier

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WeightedRadialKernel

open MeasureTheory Set Filter
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.FiniteLogCounting

open private seed_log_domain from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FirstConductorSource

local notation "q" => (1/4 : ℝ)
local notation "F" => fourierL2
local notation "D" => burnolMultiplicativeDilation

theorem window_mass : IntegrableKernel ConstantDual.seedRaw := by
  apply (kernel_of_log _ _ seed_log_domain).congr
  filter_upwards [ae_restrict_of_ae (s := Ioi (0:ℝ)) ConstantDual.seed_coeFn] with x actual
  rw [actual]

/-- The source is the literal original constant window and its weighted radial clock. -/
def windowKernel : BurnolL2 →L[ℂ] BurnolL2 :=
  action ConstantDual.seedRaw ConstantDual.seedRaw_measurable window_mass

private theorem window_integral (v : BurnolL2) :
    windowKernel v = ∫ t in Ioo 0 (q/4), (t : ℂ)⁻¹ • radialOrbit t v := by
  unfold windowKernel
  rw [action_value, ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (q/4)] with t edge
  by_cases positive : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from positive)]
    have abs : |4*t| = 4*t := abs_of_pos (by positivity)
    by_cases inside : t < q/4
    · rw [indicator_of_mem (show t ∈ Ioo 0 (q/4) from ⟨positive,inside⟩),
        coefficient, ConstantDual.seedRaw, abs, if_pos (by linarith : 4*t ≤ q), one_div]
    · have outside : ¬ 4*t ≤ q := by
        intro under
        exact edge (le_antisymm (by linarith) (le_of_not_gt inside))
      rw [indicator_of_notMem (show t ∉ Ioo 0 (q/4) from fun h => inside h.2),
        coefficient, ConstantDual.seedRaw, abs, if_neg outside, zero_div, zero_smul]
  · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from positive),
      indicator_of_notMem (show t ∉ Ioo 0 (q/4) from fun h => positive h.1)]

private def clock (h : ℝ) : ℝ := (q/4) * Real.exp (-h/2)

private theorem clock_pos (h : ℝ) : 0 < clock h := by
  unfold clock
  positivity

private theorem clock_derivative (h : ℝ) : HasDerivAt clock (-clock h/2) h := by
  have move := ((Real.hasDerivAt_exp (-h/2)).comp h ((hasDerivAt_id h).neg.div_const 2)).const_mul (q/4)
  convert move using 1 <;> first | rfl | (unfold clock; ring)

private theorem clock_injective : Set.InjOn clock (Ioi 0) := by
  intro h _ k _ same
  have expEq := mul_left_cancel₀ (by norm_num : q/4 ≠ 0) same
  have equal := Real.exp_injective expEq
  linarith

private theorem clock_image : clock '' Ioi (0:ℝ) = Ioo 0 (q/4) := by
  ext t
  constructor
  · rintro ⟨h, positive, rfl⟩
    have hpos : 0 < h := positive
    refine ⟨clock_pos h, ?_⟩
    unfold clock
    exact mul_lt_of_lt_one_right (by norm_num) (Real.exp_lt_one_iff.mpr (by linarith))
  · intro inside
    let h := -2*Real.log (t/(q/4))
    have domain : 0 < t/(q/4) := div_pos inside.1 (by norm_num)
    have upper : t/(q/4) < 1 := (div_lt_one (by norm_num)).mpr inside.2
    have negative := Real.log_neg domain upper
    refine ⟨h, show 0 < h by dsimp [h]; linarith, ?_⟩
    rw [clock, show -h/2 = Real.log (t/(q/4)) by dsimp [h]; ring, Real.exp_log domain]
    ring

private theorem clock_log (h : ℝ) : Real.log (4*clock h) = Real.log q - h/2 := by
  rw [show 4*clock h = q * Real.exp (-h/2) by unfold clock; ring,
    Real.log_mul (by norm_num : q ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  ring

private theorem quarter_exp : Real.exp (Real.log q / 2) = 1/2 := by
  have square : Real.exp (Real.log q / 2)^2 = q := by
    rw [← Real.exp_nat_mul, show (↑(2:Nat) : ℝ) * (Real.log q / 2) = Real.log q by push_cast; ring,
      Real.exp_log (by norm_num : 0 < q)]
  nlinarith [Real.exp_pos (Real.log q/2)]

private theorem clock_integrand (v : BurnolL2) (h : ℝ) :
    |-clock h/2| • ((clock h : ℂ)⁻¹ • radialOrbit (clock h) v) =
      (1/4 : ℂ) • D (-Real.log q)
        (F (burnolDirectRightResolventIntegrand (1/2) (fourierL2.symm v) h)) := by
  have positive := clock_pos h
  have weight : (Real.exp (-h/4) : ℂ) = positiveMellinQuarterRightResolventWeight (1/2) h := by
    rw [positiveMellinQuarterRightResolventWeight, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have shifted : -Real.log (4*clock h) = -Real.log q + h/2 := by rw [clock_log]; ring
  have clockScalar : (Real.exp (Real.log (4*clock h)/2) : ℂ) =
      (1/2 : ℂ) * (Real.exp (-h/4) : ℂ) := by
    rw [clock_log, show (Real.log q - h/2)/2 = Real.log q/2 + (-h/4) by ring,
      Real.exp_add, quarter_exp, Complex.ofReal_mul]
    norm_num
  rw [abs_of_neg (by linarith : -clock h/2 < 0),
    RCLike.real_smul_eq_coe_smul (K := ℂ), radialOrbit, shifted, clockScalar,
    burnolDirectRightResolventIntegrand, map_smul, fourierL2_burnolMultiplicativeDilation,
    LinearIsometryEquiv.apply_symm_apply, show -(-h/2) = h/2 by ring,
    show -(-clock h/2) = clock h/2 by ring, map_smul, burnolMultiplicativeDilation_add, ← weight]
  simp only [smul_smul]
  have hne : (clock h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  congr 1
  push_cast
  field_simp [hne]
  norm_num only [show (2:ℂ)^2 = 4 by norm_num]
  exact mul_comm _ _

/-- The original window kernel is the outward half-resolvent with the exact source scale. -/
theorem window_factor (v : BurnolL2) :
    (-4 : ℂ) • D (Real.log q) (windowKernel v) =
      F (burnolDirectRightResolvent (1/2) (fourierL2.symm v)) := by
  let input := fourierL2.symm v
  let integrand := burnolDirectRightResolventIntegrand (1/2) input
  let scaled := (D (-Real.log q)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    fourierL2.toContinuousLinearEquiv.toContinuousLinearMap
  have chart := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := clock) (f' := fun h => -clock h/2) measurableSet_Ioi
    (fun h _ => (clock_derivative h).hasDerivWithinAt) clock_injective
    (fun t => (t : ℂ)⁻¹ • radialOrbit t v)
  rw [clock_image] at chart
  have kernel : windowKernel v = (1/4 : ℂ) • scaled (∫ h in Ioi 0, integrand h) := by
    rw [window_integral, chart, ← scaled.integral_comp_comm
      (burnolDirectRightResolventIntegrand_integrableOn (1/2) (by norm_num) input), ← integral_smul]
    exact integral_congr_ae (Eventually.of_forall (clock_integrand v))
  rw [kernel]
  change (-4 : ℂ) • D (Real.log q) ((1/4 : ℂ) • D (-Real.log q) (F (∫ h in Ioi 0, integrand h))) = _
  rw [map_smul, smul_smul, burnolMultiplicativeDilation_add, add_neg_cancel,
    burnolMultiplicativeDilation_zero, burnolDirectRightResolvent, map_neg]
  norm_num [integrand, input]

end OriginalGamma.Source.WeightedRadialKernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
