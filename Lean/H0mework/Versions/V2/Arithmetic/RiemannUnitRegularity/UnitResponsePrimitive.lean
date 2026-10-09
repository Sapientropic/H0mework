import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.PowerLanding

/-! The original counting/reciprocal source pair survives the zero-scale limit through its actual L² norm. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem burnolSourceScalePrimitive_zero (value : BurnolL2) : burnolSourceScalePrimitive value 0 = 0 := by
  simp [burnolSourceScalePrimitive]

theorem burnolSourceScalePrimitive_norm (value : BurnolL2) (scale : ℝ) :
    ‖burnolSourceScalePrimitive value scale‖ = Real.sqrt scale * ‖value‖ := by
  rw [burnolSourceScalePrimitive, norm_smul, (burnolMultiplicativeDilation (Real.log scale)).norm_map,
    Real.norm_of_nonneg (Real.sqrt_nonneg scale)]

theorem burnolSourceScalePrimitive_continuous_zero (value : BurnolL2) :
    ContinuousAt (burnolSourceScalePrimitive value) 0 := by
  change Filter.Tendsto (burnolSourceScalePrimitive value) (𝓝 0) (𝓝 (burnolSourceScalePrimitive value 0))
  rw [burnolSourceScalePrimitive_zero, tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [burnolSourceScalePrimitive_norm]
  simpa only [Real.sqrt_zero, zero_mul] using (Real.continuous_sqrt.tendsto 0).mul_const ‖value‖

theorem burnolSourceScalePrimitive_realizes (scale : ℝ) (positive : 0 < scale) (bounded : scale ≤ 4)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 scale) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 scale)) test := by
  let readSource := burnolRemainderSourceReadCLM test
  let readValue : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  let pair : ℝ → BurnolL2 × BurnolL2 := fun a =>
    (burnolReciprocalStepNativeSource a scale, burnolReciprocalStepNativeWave a scale)
  have closed : IsClosed {p : BurnolL2 × BurnolL2 | readSource p.1 = readValue p.2} :=
    isClosed_eq (readSource.continuous.comp continuous_fst) (readValue.continuous.comp continuous_snd)
  have actual : MapsTo pair (Ioo 0 scale) {p | readSource p.1 = readValue p.2} := by
    intro a inside
    change burnolRemainderSourceReadCLM test (burnolReciprocalStepNativeSource a scale) =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolReciprocalStepNativeWave a scale)) test
    rw [burnolRemainderSourceReadCLM_apply,
      burnolReciprocalStepNativeSource_eq a scale inside.1 inside.2.le,
      burnolReciprocalStepNativeWave_eq a scale inside.1 inside.2.le]
    exact burnolReciprocalStepSource_realizes a scale inside.1 inside.2.le bounded test
  have pairContinuous : ContinuousAt pair 0 :=
    (continuousAt_const.sub (burnolSourceScalePrimitive_continuous_zero burnolUnitReciprocalPrimitiveL2)).prodMk
      (continuousAt_const.sub (burnolSourceScalePrimitive_continuous_zero burnolUnitCountingPrimitiveL2))
  have origin : (0 : ℝ) ∈ closure (Ioo 0 scale) := by
    rw [closure_Ioo positive.ne]
    exact ⟨le_rfl, positive.le⟩
  have landed := pairContinuous.continuousWithinAt.mem_closure origin actual
  rw [closed.closure_eq] at landed
  change readSource (burnolReciprocalStepNativeSource 0 scale) =
    readValue (burnolReciprocalStepNativeWave 0 scale) at landed
  simp only [burnolReciprocalStepNativeSource, burnolReciprocalStepNativeWave,
    burnolSourceScalePrimitive_zero, sub_zero] at landed
  rw [← burnolRemainderSourceReadCLM_apply]
  exact landed

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
