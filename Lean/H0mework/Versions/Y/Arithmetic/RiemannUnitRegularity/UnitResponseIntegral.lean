import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.UnitResponsePrimitive

/-! Source-generated scale energy pays the full unit-tail integral, with no zeta estimate or spectral premise. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

def burnolUnitTailSlope (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : ℂ :=
  -(coordinate.value - 1) * (u : ℂ) ^ (coordinate.value - 2)

theorem burnolUnitTailSlope_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (burnolUnitTailSlope coordinate) (Ioi 0) :=
  continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.cpow_const
    (fun _ positive => Complex.ofReal_mem_slitPlane.mpr positive))

theorem burnolUnitTailSlope_norm (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (u : ℝ) (positive : 0 < u) :
    ‖burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive value u‖ =
      ‖coordinate.value - 1‖ * u ^ (coordinate.value.re - 3 / 2) * ‖value‖ := by
  rw [norm_smul, burnolUnitTailSlope, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos positive, burnolSourceScalePrimitive_norm]
  change ‖coordinate.value - 1‖ * u ^ (coordinate.value.re - 2) *
    (Real.sqrt u * ‖value‖) = _
  rw [Real.sqrt_eq_rpow]
  calc
    _ = ‖coordinate.value - 1‖ *
        (u ^ (coordinate.value.re - 2) * u ^ (1 / 2 : ℝ)) * ‖value‖ := by ring
    _ = _ := by
      rw [← Real.rpow_add positive,
        show coordinate.value.re - 2 + 1 / 2 = coordinate.value.re - 3 / 2 by ring]

theorem burnolUnitTailSlope_integrable (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (upper : ℝ) :
    IntegrableOn (fun u : ℝ => burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive value u) (Ioc 0 upper) := by
  have regular := (burnolUnitTailSlope_continuous coordinate).smul (burnolSourceScalePrimitive_continuous value)
  have exponent : -1 < coordinate.value.re - 3 / 2 := by linarith [coordinate.rightHalf]
  have decay := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := upper) exponent).1
  have measured : AEStronglyMeasurable
      (fun u : ℝ => burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive value u)
        (volume.restrict (Ioc 0 upper)) :=
    (regular.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  apply ((decay.const_mul ‖coordinate.value - 1‖).mul_const ‖value‖).mono' measured
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
  rw [burnolUnitTailSlope_norm coordinate value u inside.1]

def burnolUnitTailPrimitiveValue (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (upper : ℝ) : BurnolL2 :=
  burnolUnitPowerWeight coordinate upper • burnolSourceScalePrimitive value upper -
    ∫ u : ℝ in Ioc 0 upper, burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive value u

theorem burnolUnitTailPrimitive_realizes (coordinate : BurnolCompletedMellinCoordinate) (upper : ℝ)
    (positive : 0 < upper) (bounded : upper ≤ 4) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolUnitTailPrimitiveValue coordinate burnolUnitReciprocalPrimitiveL2 upper) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolUnitTailPrimitiveValue coordinate burnolUnitCountingPrimitiveL2 upper)) test := by
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc 0 upper), ∀ ψ : SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead
        (burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 u) ψ =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 u)) ψ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    intro ψ
    rw [← burnolRemainderSourceReadCLM_apply, map_smul, burnolRemainderSourceReadCLM_apply,
      burnolSourceScalePrimitive_realizes u inside.1 (inside.2.trans bounded)]
    simp only [map_smul, smul_apply, smul_eq_mul]
  have integrated := burnolRemainderSourceRead_bochner (volume.restrict (Ioc 0 upper)) _ _
    (burnolUnitTailSlope_integrable coordinate burnolUnitReciprocalPrimitiveL2 upper)
    (burnolUnitTailSlope_integrable coordinate burnolUnitCountingPrimitiveL2 upper) familyRead test
  rw [burnolUnitTailPrimitiveValue, ← burnolRemainderSourceReadCLM_apply, map_sub, map_smul,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolSourceScalePrimitive_realizes upper positive bounded, integrated]
  simp only [burnolUnitTailPrimitiveValue, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
