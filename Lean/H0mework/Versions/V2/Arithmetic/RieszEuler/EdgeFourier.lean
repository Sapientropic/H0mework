import H0mework.Versions.V2.Arithmetic.RieszEuler.Even
import H0mework.Versions.V2.Arithmetic.RieszEuler.EdgeRaw

/-!
The Fourier transform of the original endpoint distribution has a continuous
raw representative in Schwartz pairings. Only its finite quarter restriction
enters the existing interval L² carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Edge

open Complex FourierTransform MeasureTheory
open scoped ENNReal FourierTransform InnerProductSpace Topology
open Constructor

noncomputable section

private theorem phase_test_integrable (point : ℝ) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => test x * phase point x) := by
  apply test.integrable.mul_bdd (phaseContinuous point).aestronglyMeasurable
  filter_upwards with x
  exact (Circle.norm_coe (𝐞 (-(point * x)))).le

private theorem truncated_test_integrable
    (radius : ℝ) (positive : 0 < radius) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ =>
      test x * burnolRadiusTruncatedFourierRaw radius (intervalConstant radius) x) := by
  apply test.integrable.mul_bdd
    (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant radius)).aestronglyMeasurable
  exact Filter.Eventually.of_forall
    (burnolRadiusTruncatedFourierRaw_norm_le positive (intervalConstant radius))

private theorem test_raw_split (radius : ℝ) (test : SchwartzMap ℝ ℂ) :
    (fun x : ℝ => test x * raw radius x) =
      (fun x : ℝ => (radius : ℂ) * (test x * phase radius x + test x * phase (-radius) x)) -
        (fun x : ℝ =>
          test x * burnolRadiusTruncatedFourierRaw radius (intervalConstant radius) x) := by
  funext x
  dsimp only [raw, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem test_integrable (radius : ℝ) (positive : 0 < radius) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => test x * raw radius x) := by
  rw [test_raw_split]
  exact (((phase_test_integrable radius test).add
    (phase_test_integrable (-radius) test)).const_mul (radius : ℂ)).sub
      (truncated_test_integrable radius positive test)

private theorem fourier_delta_pairing (point : ℝ) (test : SchwartzMap ℝ ℂ) :
    (𝓕 (TemperedDistribution.delta point)) test =
      ∫ x : ℝ, test x * phase point x := by
  rw [TemperedDistribution.fourier_apply, TemperedDistribution.delta_apply,
    SchwartzMap.fourier_coe, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp only [phase, Circle.smul_def, smul_eq_mul, mul_comm]

private theorem scaled_gap_eq_constantWindow (radius : ℝ) (positive : 0 < radius) :
    ((2 * radius : ℝ) : ℂ) • burnolAmbientGapRieszVector radius =
      burnolRadiusZeroExtension radius (intervalConstant radius) := by
  have normEq : (‖intervalConstant radius‖ ^ 2 : ℂ) = ((2 * radius : ℝ) : ℂ) := by
    exact_mod_cast burnolIntervalConstant_norm_sq positive
  have nonzero : ((2 * radius : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) positive.ne')
  have inverse : star (((2 * radius : ℝ) : ℂ)⁻¹) = ((2 * radius : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
  unfold burnolAmbientGapRieszVector
  rw [normEq, inverse, smul_smul, mul_inv_cancel₀ nonzero, one_smul]
  rfl

private theorem fourier_scaled_gap_pairing
    (radius : ℝ) (positive : 0 < radius) (test : SchwartzMap ℝ ℂ) :
    (𝓕 (((2 * radius : ℝ) : ℂ) •
      (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ))) test =
      ∫ x : ℝ,
        test x * burnolRadiusTruncatedFourierRaw radius (intervalConstant radius) x := by
  have actual := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2)
    (scaled_gap_eq_constantWindow radius positive)
  rw [map_smul] at actual
  change ((2 * radius : ℝ) : ℂ) •
    (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ) =
      (burnolRadiusZeroExtension radius (intervalConstant radius) :
        TemperedDistribution ℝ ℂ) at actual
  rw [actual, Lp.fourier_toTemperedDistribution_eq, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [burnolRadiusFourierL2_zeroExtension_ae_eq_raw (intervalConstant radius)]
    with x read
  simp only [smul_eq_mul]
  change test x * fourierL2 (burnolRadiusZeroExtension radius (intervalConstant radius)) x = _
  rw [read]

/-- The actual Fourier edge is read globally through Schwartz tests, without a global L² claim. -/
theorem fourier_edge_pairing
    (radius : ℝ) (positive : 0 < radius) (test : SchwartzMap ℝ ℂ) :
    (𝓕 (GapEuler.edge radius)) test = ∫ x : ℝ, test x * raw radius x := by
  unfold GapEuler.edge
  change ((fourierCLM ℂ (TemperedDistribution ℝ ℂ))
    ((radius : ℂ) • (TemperedDistribution.delta radius + TemperedDistribution.delta (-radius)) -
      ((2 * radius : ℝ) : ℂ) •
        (burnolAmbientGapRieszVector radius : TemperedDistribution ℝ ℂ))) test = _
  rw [map_sub, map_smul, map_add]
  simp only [fourierCLM_apply, sub_apply, smul_apply, add_apply, smul_eq_mul]
  rw [fourier_delta_pairing, fourier_delta_pairing, fourier_scaled_gap_pairing radius positive]
  rw [test_raw_split]
  change (radius : ℂ) * ((∫ x : ℝ, test x * phase radius x) +
    ∫ x : ℝ, test x * phase (-radius) x) -
      (∫ x : ℝ, test x * burnolRadiusTruncatedFourierRaw radius (intervalConstant radius) x) =
        ∫ x : ℝ, (radius : ℂ) * (test x * phase radius x + test x * phase (-radius) x) -
          test x * burnolRadiusTruncatedFourierRaw radius (intervalConstant radius) x
  have plusIntegrable : Integrable (fun x : ℝ =>
      (radius : ℂ) * (test x * phase radius x + test x * phase (-radius) x)) := by
    simpa only [Pi.add_apply] using (((phase_test_integrable radius test).add
      (phase_test_integrable (-radius) test)).const_mul (radius : ℂ))
  rw [integral_sub plusIntegrable (truncated_test_integrable radius positive test),
    integral_const_mul, integral_add (phase_test_integrable radius test)
      (phase_test_integrable (-radius) test)]

end
end OriginalRieszSource.Edge
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
