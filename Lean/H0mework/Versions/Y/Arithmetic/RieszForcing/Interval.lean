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

private theorem interval_integrable_of_local {value : ℝ → ℂ}
    (source : LocallyIntegrable value) : IntegrableOn value (Ioc (-q) q) :=
  (source.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem forcingRaw_local (coordinate : BurnolCompletedMellinCoordinate) :
    LocallyIntegrable (burnolRieszFourierForcingRaw coordinate) := by
  have source := (ForcingWhole.raw_local coordinate).sub
    (continuous_const.locallyIntegrable (f := fun _ : ℝ => ForcingMeanZero.mean coordinate))
  exact source

private theorem position_test_integral (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ in Ioc (-q) q, (x : ℂ) * deriv test x + test x) =
      (q : ℂ) * (test q + test (-q)) := by
  let positioned := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) test
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  have positionedDerivative (x : ℝ) : deriv positioned x =
      (x : ℂ) * deriv test x + test x := by
    have generated := (Complex.ofRealCLM.hasDerivAt (x := x)).mul (test.hasDerivAt x)
    change deriv (fun y : ℝ => (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ)) test) y) x = _
    simp only [SchwartzMap.smulLeftCLM_apply growth, smul_eq_mul]
    exact (by simpa only [Pi.mul_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul,
      add_comm] using generated.deriv)
  have continuous : Continuous (fun x : ℝ => (x : ℂ) * deriv test x + test x) :=
    (Complex.continuous_ofReal.mul (SchwartzMap.derivCLM ℂ ℂ test).continuous).add test.continuous
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_hx : x ∈ uIcc (-q) q) =>
      (positioned.hasDerivAt x).congr_deriv (positionedDerivative x))
    (continuous.intervalIntegrable (-q) q)
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q)] at source
  exact source.trans (by
    dsimp only [positioned]
    rw [SchwartzMap.smulLeftCLM_apply growth]
    simp only [smul_eq_mul]
    push_cast
    ring)

theorem forcingRaw_interval_ibp (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ in Ioc (-q) q,
      ((x : ℂ) * burnolRieszFourierForcingRaw coordinate x) * deriv test x +
        (star coordinate.value * burnolRieszFourierForcingRaw coordinate x +
          ForcingWhole.coefficient coordinate * (Edge.raw q x - ForcingMeanZero.edgeMean) +
          burnolRieszFourierForcingRaw coordinate q) * test x) =
      (q : ℂ) * burnolRieszFourierForcingRaw coordinate q * (test q + test (-q)) := by
  let old := fun x : ℝ =>
    ((x : ℂ) * ForcingWhole.raw coordinate x) * deriv test x +
      (star coordinate.value * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x) * test x
  let moment := fun x : ℝ => (x : ℂ) * deriv test x + test x
  have derivativeContinuous : Continuous (fun x : ℝ => deriv test x) :=
    (SchwartzMap.derivCLM ℂ ℂ test).continuous
  have oldLocal : LocallyIntegrable old := by
    dsimp only [old]
    exact (LocallyIntegrable.mul_continuous derivativeContinuous
      (LocallyIntegrable.continuous_mul Complex.continuous_ofReal (ForcingWhole.raw_local coordinate))).add
      (LocallyIntegrable.mul_continuous test.continuous
        ((LocallyIntegrable.continuous_mul continuous_const (ForcingWhole.raw_local coordinate)).add
          ((Edge.raw_continuous q).const_mul (ForcingWhole.coefficient coordinate)).locallyIntegrable))
  have momentContinuous : Continuous moment :=
    (Complex.continuous_ofReal.mul derivativeContinuous).add test.continuous
  have actual : (∫ x : ℝ in Ioc (-q) q,
      ((x : ℂ) * burnolRieszFourierForcingRaw coordinate x) * deriv test x +
        (star coordinate.value * burnolRieszFourierForcingRaw coordinate x +
          ForcingWhole.coefficient coordinate * (Edge.raw q x - ForcingMeanZero.edgeMean) +
          burnolRieszFourierForcingRaw coordinate q) * test x) =
      (∫ x : ℝ in Ioc (-q) q, old x) -
        ForcingMeanZero.mean coordinate * (∫ x : ℝ in Ioc (-q) q, moment x) := by
    rw [← integral_const_mul,
      ← integral_sub (interval_integrable_of_local oldLocal)
        (interval_integrable_of_local (momentContinuous.const_mul (ForcingMeanZero.mean coordinate)).locallyIntegrable)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ForcingMeanZero.forcingRaw_eq, ForcingMeanZero.forcing_mean_boundary]
    dsimp only [old, moment]
    ring
  rw [actual]
  change (∫ x : ℝ in Ioc (-q) q,
    ((x : ℂ) * ForcingWhole.raw coordinate x) * deriv test x +
      (star coordinate.value * ForcingWhole.raw coordinate x +
        ForcingWhole.coefficient coordinate * Edge.raw q x) * test x) -
    ForcingMeanZero.mean coordinate * (∫ x : ℝ in Ioc (-q) q, (x : ℂ) * deriv test x + test x) = _
  rw [ForcingWhole.raw_interval_ibp, position_test_integral, ForcingMeanZero.forcingRaw_eq]
  ring

theorem forcing_scalar_equation (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ in Ioc (-q) q, ((x : ℂ) * burnolRieszFourierForcingRaw coordinate x) * deriv test x) +
      star coordinate.value * (∫ x : ℝ in Ioc (-q) q, burnolRieszFourierForcingRaw coordinate x * test x) +
      ForcingWhole.coefficient coordinate *
        (∫ x : ℝ in Ioc (-q) q, (Edge.raw q x - ForcingMeanZero.edgeMean) * test x) +
      burnolRieszFourierForcingRaw coordinate q * (∫ x : ℝ in Ioc (-q) q, test x) =
      (q : ℂ) * burnolRieszFourierForcingRaw coordinate q * (test q + test (-q)) := by
  let first := fun x : ℝ => ((x : ℂ) * burnolRieszFourierForcingRaw coordinate x) * deriv test x
  let second := fun x : ℝ => star coordinate.value * (burnolRieszFourierForcingRaw coordinate x * test x)
  let third := fun x : ℝ => ForcingWhole.coefficient coordinate *
    ((Edge.raw q x - ForcingMeanZero.edgeMean) * test x)
  let fourth := fun x : ℝ => burnolRieszFourierForcingRaw coordinate q * test x
  have firstI : IntegrableOn first (Ioc (-q) q) :=
    interval_integrable_of_local (LocallyIntegrable.mul_continuous
      (SchwartzMap.derivCLM ℂ ℂ test).continuous
      (LocallyIntegrable.continuous_mul Complex.continuous_ofReal (forcingRaw_local coordinate)))
  have secondI : IntegrableOn second (Ioc (-q) q) :=
    interval_integrable_of_local (LocallyIntegrable.continuous_mul continuous_const
      (LocallyIntegrable.mul_continuous test.continuous (forcingRaw_local coordinate)))
  have thirdContinuous : Continuous third :=
    ((((Edge.raw_continuous q).sub continuous_const).mul test.continuous).const_mul _)
  have thirdI : IntegrableOn third (Ioc (-q) q) :=
    interval_integrable_of_local thirdContinuous.locallyIntegrable
  have fourthI : IntegrableOn fourth (Ioc (-q) q) :=
    interval_integrable_of_local (test.continuous.const_mul _).locallyIntegrable
  have source := forcingRaw_interval_ibp coordinate test
  have read : (∫ x : ℝ in Ioc (-q) q,
      ((x : ℂ) * burnolRieszFourierForcingRaw coordinate x) * deriv test x +
        (star coordinate.value * burnolRieszFourierForcingRaw coordinate x +
          ForcingWhole.coefficient coordinate * (Edge.raw q x - ForcingMeanZero.edgeMean) +
          burnolRieszFourierForcingRaw coordinate q) * test x) =
      ((∫ x : ℝ in Ioc (-q) q, first x) + (∫ x : ℝ in Ioc (-q) q, second x)) +
        (∫ x : ℝ in Ioc (-q) q, third x) + (∫ x : ℝ in Ioc (-q) q, fourth x) := by
    rw [← integral_add firstI secondI,
      ← integral_add (f := fun x => first x + second x) (g := third) (firstI.add secondI) thirdI,
      ← integral_add (f := fun x => (first x + second x) + third x) (g := fourth)
        ((firstI.add secondI).add thirdI) fourthI]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [first, second, third, fourth]
    ring
  rw [read] at source
  simpa only [first, second, third, fourth, integral_const_mul] using source

end
end OriginalRieszSource.Translator.ForcingCutoff
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
