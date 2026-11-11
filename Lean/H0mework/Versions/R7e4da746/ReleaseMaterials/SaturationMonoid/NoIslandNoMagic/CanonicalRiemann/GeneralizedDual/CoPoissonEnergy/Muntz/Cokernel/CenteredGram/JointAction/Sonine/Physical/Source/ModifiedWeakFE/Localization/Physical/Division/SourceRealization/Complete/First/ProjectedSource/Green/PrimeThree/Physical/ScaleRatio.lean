import H0mework.Versions.R7e4da746.Arithmetic.RiemannSourceGreen.ProbeCutoffValue

/-! Exact cutoff Gram entries of the actual source-scale primitive in the original physical L². -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem originalPhysicalCutoff_dilation (source : BurnolL2) (h X : ℝ) :
    originalPhysicalCutoff X (burnolMultiplicativeDilation h source) =
      burnolMultiplicativeDilation h (originalPhysicalCutoff (Real.exp h * X) source) := by
  have positive := Real.exp_pos h
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) positive.ne')
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn X (burnolMultiplicativeDilation h source),
    burnolMultiplicativeDilation_coeFn h source,
    burnolMultiplicativeDilation_coeFn h (originalPhysicalCutoff (Real.exp h * X) source),
    qmp.ae (originalPhysicalCutoff_coeFn (Real.exp h * X) source)]
      with x leftCut sourceDilation rightDilation rightCut
  have sameWindow : Real.exp h * x ∈ symmetricInterval (Real.exp h * X) ↔
      x ∈ symmetricInterval X := by
    simp only [symmetricInterval, mem_Icc, show -(Real.exp h * X) = Real.exp h * (-X) by ring,
      mul_le_mul_iff_right₀ positive]
  rw [leftCut, rightDilation]
  unfold burnolL2RawNormalizedDilation
  rw [rightCut]
  by_cases inside : x ∈ symmetricInterval X
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem (sameWindow.mpr inside)]
    exact sourceDilation
  · rw [Set.indicator_of_notMem inside,
      Set.indicator_of_notMem (fun moved => inside (sameWindow.mp moved)), mul_zero]

private theorem originalPhysicalCutoff_smul (source : BurnolL2) (c : ℂ) (X : ℝ) :
    originalPhysicalCutoff X (c • source) = c • originalPhysicalCutoff X source := by
  unfold originalPhysicalCutoff
  rw [map_smul, map_smul]

/-- Both entries retain the original physical inner product; only their common dilation is removed. -/
theorem sourceScalePrimitive_cutoff_gram_ratio (source : BurnolL2) (r t X : ℝ)
    (rPositive : 0 < r) (tPositive : 0 < t) :
    inner ℂ (originalPhysicalCutoff X (burnolSourceScalePrimitive source r))
      (burnolSourceScalePrimitive source t) =
        (Real.sqrt (r * t) : ℂ) * inner ℂ (originalPhysicalCutoff (r * X) source)
          (burnolMultiplicativeDilation (Real.log (t / r)) source) := by
  have common : burnolMultiplicativeDilation (Real.log t) source =
      burnolMultiplicativeDilation (Real.log r)
        (burnolMultiplicativeDilation (Real.log (t / r)) source) := by
    rw [burnolMultiplicativeDilation_add, Real.log_div tPositive.ne' rPositive.ne']
    rw [show Real.log r + (Real.log t - Real.log r) = Real.log t by ring]
  unfold burnolSourceScalePrimitive
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [originalPhysicalCutoff_smul, originalPhysicalCutoff_dilation,
    Real.exp_log rPositive, common, inner_smul_left, inner_smul_right,
    (burnolMultiplicativeDilation (Real.log r)).inner_map_map]
  rw [RCLike.conj_ofReal]
  rw [← mul_assoc, ← RCLike.ofReal_mul, ← Real.sqrt_mul rPositive.le]
  rfl

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
