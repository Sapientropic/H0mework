import H0mework.Versions.Y.Arithmetic.SonineProjection.ConstructorCompact
import H0mework.Versions.Y.Arithmetic.RieszEuler.Even
import H0mework.Versions.Y.Arithmetic.RieszForcing.ForcingCutoffPairing

/-! The shared window pairing generates compact smooth Euler distributions with both endpoints. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler

open Complex Filter MeasureTheory Set Constructor
open scoped ENNReal SchwartzMap Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

private theorem extension_pairing (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw) (test : SchwartzMap ℝ ℂ) :
    (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) test =
      ∫ x : ℝ in (-q)..q, test x * raw x := by
  rw [Translator.ForcingCutoff.zeroExtension_pairing state raw read,
    intervalIntegral.integral_of_le (by norm_num : -q ≤ q)]
  apply integral_congr_ae
  filter_upwards with x
  exact mul_comm _ _

private theorem extension_derivative (state : BurnolQuarterIntervalL2) (raw derivative : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (continuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (generated : ∀ x : ℝ, HasDerivAt raw (derivative x) x) :
    TemperedDistribution.derivCLM ℂ
        (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (compact derivative derivativeContinuous) : TemperedDistribution ℝ ℂ) +
        raw (-q) • TemperedDistribution.delta (-q) - raw q • TemperedDistribution.delta q := by
  ext test
  rw [TemperedDistribution.derivCLM_apply_apply, extension_pairing state raw read]
  simp only [sub_apply, add_apply, smul_apply, TemperedDistribution.delta_apply,
    neg_apply, SchwartzMap.derivCLM_apply, smul_eq_mul]
  rw [extension_pairing _ _ (compact_read derivative derivativeContinuous)]
  simp only [neg_mul, intervalIntegral.integral_neg]
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := test) (u' := deriv test) (v := raw) (v' := derivative)
    (a := -q) (b := q) test.continuous.continuousOn continuous.continuousOn
    (fun x _ => test.hasDerivAt x) (fun x _ => generated x)
    ((SchwartzMap.derivCLM ℂ ℂ test).continuous.intervalIntegrable _ _)
    (derivativeContinuous.intervalIntegrable _ _)
  rw [ibp]
  ring

def smoothEuler (raw derivative : ℝ → ℂ)
    (continuous : Continuous raw) (derivativeContinuous : Continuous derivative) :
    BurnolQuarterIntervalL2 :=
  compact (fun x : ℝ => (x : ℂ) * derivative x + (1 / 2 : ℂ) * raw x) (by fun_prop)

private theorem extension_euler (state : BurnolQuarterIntervalL2) (raw derivative : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (continuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (generated : ∀ x : ℝ, HasDerivAt raw (derivative x) x) :
    GapEuler.euler (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (smoothEuler raw derivative continuous derivativeContinuous) :
        TemperedDistribution ℝ ℂ) -
      ((q : ℂ) * raw (-q)) • TemperedDistribution.delta (-q) -
      ((q : ℂ) * raw q) • TemperedDistribution.delta q := by
  have interior : GapEuler.position
        (burnolQuarterZeroExtension (compact derivative derivativeContinuous) : TemperedDistribution ℝ ℂ) +
      (1 / 2 : ℂ) • (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (smoothEuler raw derivative continuous derivativeContinuous) :
        TemperedDistribution ℝ ℂ) := by
    ext test
    have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [GapEuler.position, TemperedDistribution.smulLeftCLM_apply_apply,
      extension_pairing _ _ (compact_read derivative derivativeContinuous),
      extension_pairing state raw read, smoothEuler,
      extension_pairing _ _ (compact_read _ _)]
    simp only [SchwartzMap.smulLeftCLM_apply growth, smul_eq_mul]
    have split : (fun x : ℝ => test x * ((x : ℂ) * derivative x + (1 / 2 : ℂ) * raw x)) =
        fun x : ℝ => ((x : ℂ) * test x) * derivative x + (1 / 2 : ℂ) * (test x * raw x) := by
      funext x
      ring
    have leftIntegrable : IntervalIntegrable
        (fun x : ℝ => ((x : ℂ) * test x) * derivative x) volume (-q) q :=
      (by fun_prop : Continuous (fun x : ℝ => ((x : ℂ) * test x) * derivative x)).intervalIntegrable _ _
    have rightIntegrable : IntervalIntegrable
        (fun x : ℝ => (1 / 2 : ℂ) * (test x * raw x)) volume (-q) q :=
      (by fun_prop : Continuous (fun x : ℝ => (1 / 2 : ℂ) * (test x * raw x))).intervalIntegrable _ _
    rw [split, intervalIntegral.integral_add leftIntegrable rightIntegrable,
      intervalIntegral.integral_const_mul]
  unfold GapEuler.euler
  simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
  rw [extension_derivative state raw derivative read continuous derivativeContinuous generated,
    map_sub, map_add, map_smul, map_smul, GapEuler.position_delta, GapEuler.position_delta]
  rw [← interior]
  push_cast
  module

theorem smoothEuler_mean (state : BurnolQuarterMeanZeroCarrier) (raw derivative : ℝ → ℂ)
    (read : ((state : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq] raw)
    (continuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (generated : ∀ x : ℝ, HasDerivAt raw (derivative x) x) :
    burnolQuarterMeanCoefficient (smoothEuler raw derivative continuous derivativeContinuous) =
      (raw q + raw (-q)) / 2 := by
  have zeroIntegral : (∫ x : ℝ in (-q)..q, raw x) = 0 := by
    have source := mean_zero state
    rw [mean_integral, integral_congr_ae read] at source
    rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
    exact (mul_eq_zero.mp source).resolve_left (by norm_num)
  have differentiated : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) * raw y)
      (raw x + (x : ℂ) * derivative x) x := by
    intro x
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using!
      (Complex.ofRealCLM.hasDerivAt (x := x)).mul (generated x)
  have sumContinuous : Continuous (fun x : ℝ => raw x + (x : ℂ) * derivative x) := by fun_prop
  have primitive := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => differentiated x) (sumContinuous.intervalIntegrable (-q) q)
  unfold smoothEuler
  rw [mean_compact]
  have split : (fun x : ℝ => (x : ℂ) * derivative x + (1 / 2 : ℂ) * raw x) =
      fun x : ℝ => (raw x + (x : ℂ) * derivative x) - (1 / 2 : ℂ) * raw x := by
    funext x
    ring
  rw [split, intervalIntegral.integral_sub (sumContinuous.intervalIntegrable _ _)
    ((continuous.const_mul (1 / 2 : ℂ)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, zeroIntegral, mul_zero, sub_zero, primitive]
  norm_num
  ring

theorem even_extension_euler (state : BurnolQuarterIntervalL2) (raw derivative : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw)
    (continuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (generated : ∀ x : ℝ, HasDerivAt raw (derivative x) x)
    (mean : burnolQuarterMeanCoefficient (smoothEuler raw derivative continuous derivativeContinuous) =
      (raw q + raw (-q)) / 2) (endpoints : raw (-q) = raw q) :
    GapEuler.euler (burnolQuarterZeroExtension state : TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension
        (zeroMean (smoothEuler raw derivative continuous derivativeContinuous) : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) - raw q • GapEuler.edge q := by
  have actual := extension_euler state raw derivative read continuous derivativeContinuous generated
  rw [endpoints] at actual mean
  have meanValue : burnolQuarterMeanCoefficient
      (smoothEuler raw derivative continuous derivativeContinuous) = raw q := mean.trans (by ring)
  have gapConstant : ((2 * q : ℝ) : ℂ) •
      (burnolAmbientGapRieszVector q : TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (intervalConstant q) : TemperedDistribution ℝ ℂ) := by
    ext test
    simp only [smul_apply]
    rw [burnolGapRiesz_tempered_apply q (by norm_num),
      extension_pairing _ _ (intervalConstant_coeFn q)]
    simp only [mul_one, Complex.real_smul]
    norm_num
    ring
  have projected :
      (burnolQuarterZeroExtension
        (zeroMean (smoothEuler raw derivative continuous derivativeContinuous) : BurnolQuarterIntervalL2) :
          TemperedDistribution ℝ ℂ) =
      (burnolQuarterZeroExtension (smoothEuler raw derivative continuous derivativeContinuous) :
        TemperedDistribution ℝ ℂ) - raw q •
      (burnolQuarterZeroExtension (intervalConstant q) : TemperedDistribution ℝ ℂ) := by
    rw [zeroMean_read, meanValue, map_sub, map_smul]
    change Lp.toTemperedDistributionCLM ℂ volume 2 (_ - _) = _
    rw [map_sub, map_smul]
    rfl
  rw [actual, projected, GapEuler.edge, gapConstant]
  module

end
end OriginalRieszSource.Euler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
