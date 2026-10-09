import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.GeneratorSource

/-! The same remainder map transports the reciprocal/box resolvent identity to
its actual integer-counting wave and Fourier sibling, generating their strong derivative. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem primitive_realizes (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead burnolUnitReciprocalPrimitiveL2 test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 burnolUnitCountingPrimitiveL2) test := by
  have actual := burnolSourceScalePrimitive_realizes 1 (by norm_num) (by norm_num) test
  simpa only [burnolSourceScalePrimitive, Real.sqrt_one, Real.log_one,
    burnolMultiplicativeDilation_zero, one_smul] using actual

private theorem resolvent_realizes (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (source value : BurnolL2)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolDirectRightResolvent z source) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolDirectRightResolvent z value)) test := by
  have integrated := burnolRemainderSourceRead_bochner (volume.restrict (Ioi (0 : ℝ)))
    (burnolDirectRightResolventIntegrand z source) (burnolDirectRightResolventIntegrand z value)
    (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter source)
    (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value) (by
      filter_upwards with h test
      unfold burnolDirectRightResolventIntegrand
      rw [← burnolRemainderSourceReadCLM_apply, map_smul, burnolRemainderSourceReadCLM_apply,
        burnolRemainderRealization_dilation source value realizes]
      simp only [map_smul, smul_apply]) test
  unfold burnolDirectRightResolvent
  rw [← burnolRemainderSourceReadCLM_apply, map_neg,
    burnolRemainderSourceReadCLM_apply, integrated]
  simp only [map_neg, neg_apply]

theorem burnolCountingPrimitiveFourierPair_eq_resolvent :
    burnolUnitCountingPrimitiveL2 + fourierL2 burnolUnitCountingPrimitiveL2 =
      (-1 / 2 : ℂ) • burnolDirectRightResolvent (1 / 2)
        (fourierL2 burnolUnitCountingPrimitiveL2) := by
  let G := burnolUnitReciprocalPrimitiveL2
  let H := burnolUnitCountingPrimitiveL2
  have dual := burnolRemainderRealization_fourier G H primitive_realizes
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  have source := congrArg (fun source => burnolRemainderSourceRead source test) burnolReciprocalPrimitivePair_eq_boxResolvent
  simp only [← burnolRemainderSourceReadCLM_apply] at source
  rw [map_add, map_smul,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolRemainderSourceReadCLM_apply, primitive_realizes, dual,
    resolvent_realizes (1 / 2) (by norm_num) _ _ dual] at source
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (H + fourierL2 H)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2 ((-1 / 2 : ℂ) •
      burnolDirectRightResolvent (1 / 2) (fourierL2 H))) test
  simpa only [map_add, add_apply, map_smul, smul_apply] using source

theorem burnolCountingPrimitiveFourierPair_hasDerivAt :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2)
      (burnolUnitCountingPrimitiveL2 + fourierL2 burnolUnitCountingPrimitiveL2))
      ((1 / 4 : ℂ) • (burnolUnitCountingPrimitiveL2 - fourierL2 burnolUnitCountingPrimitiveL2)) 0 := by
  have actual := (burnolDirectRightResolventOrbit_hasDerivAt (1 / 2) (by norm_num)
    (fourierL2 burnolUnitCountingPrimitiveL2)).const_smul (-1 / 2 : ℂ)
  convert! actual using 1
  · funext h
    rw [burnolCountingPrimitiveFourierPair_eq_resolvent, map_smul]
    rfl
  · have same := burnolCountingPrimitiveFourierPair_eq_resolvent
    calc
      _ = (1 / 4 : ℂ) • (burnolUnitCountingPrimitiveL2 + fourierL2 burnolUnitCountingPrimitiveL2) -
          (1 / 2 : ℂ) • fourierL2 burnolUnitCountingPrimitiveL2 := by module
      _ = _ := by rw [same]; module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
