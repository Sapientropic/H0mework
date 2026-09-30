import H0mework.Versions.Y.Arithmetic.RieszForcing.ForcingMeanZero

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.ForcingCutoff

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology InnerProductSpace
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

theorem zeroExtension_pairing (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw) (test : SchwartzMap ℝ ℂ) :
    (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) test =
      ∫ x : ℝ in Ioc (-q) q, raw x * test x := by
  rw [Lp.toTemperedDistribution_apply]
  have source := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp read
  calc
    _ = ∫ x : ℝ, (symmetricInterval q).indicator (fun x : ℝ => raw x * test x) x := by
      apply integral_congr_ae
      filter_upwards [burnolQuarterZeroExtension_coe state, source] with x extended actual
      simp only [smul_eq_mul]
      rw [extended]
      by_cases inside : x ∈ symmetricInterval q
      · rw [indicator_of_mem inside, indicator_of_mem inside, actual inside, mul_comm]
      · rw [indicator_of_notMem inside, indicator_of_notMem inside, mul_zero]
    _ = _ := by
      rw [integral_indicator (measurableSet_symmetricInterval q)]
      exact integral_Icc_eq_integral_Ioc

theorem euler_zeroExtension_pairing (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) test =
      -(∫ x : ℝ in Ioc (-q) q, ((x : ℂ) * raw x) * deriv test x) -
        (1 / 2 : ℂ) * (∫ x : ℝ in Ioc (-q) q, raw x * test x) := by
  let value := (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ)
  have split : GapEuler.euler value =
      TemperedDistribution.derivCLM ℂ (GapEuler.position value) - (1 / 2 : ℂ) • value := by
    rw [GapEuler.derivative_position]
    unfold GapEuler.euler
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
    module
  change GapEuler.euler value test = _
  rw [split]
  simp only [sub_apply, smul_apply, smul_eq_mul, TemperedDistribution.derivCLM_apply_apply,
    GapEuler.position, TemperedDistribution.smulLeftCLM_apply_apply]
  rw [zeroExtension_pairing state raw read, zeroExtension_pairing state raw read]
  congr 1
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.smulLeftCLM_apply growth]
  simp only [smul_eq_mul, neg_apply, SchwartzMap.derivCLM_apply]
  ring

theorem edge_pairing (test : SchwartzMap ℝ ℂ) :
    GapEuler.edge q test = (q : ℂ) * (test q + test (-q)) -
      ∫ x : ℝ in Ioc (-q) q, test x := by
  unfold GapEuler.edge
  simp only [sub_apply, smul_apply, add_apply, TemperedDistribution.delta_apply, smul_eq_mul]
  rw [burnolGapRiesz_tempered_apply q (by norm_num),
    intervalIntegral.integral_of_le (by norm_num : -q ≤ q)]
  simp only [Complex.real_smul]
  push_cast
  ring

end
end OriginalRieszSource.Translator.ForcingCutoff
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
