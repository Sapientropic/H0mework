import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.PhysicalPairing

/-! A finite physical cutoff supplies its own integrability and sampling moment. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def originalPhysicalCutoff (radius : ℝ) (value : BurnolL2) : BurnolL2 :=
  burnolRadiusZeroExtension radius (burnolRadiusRestriction radius value)

theorem originalPhysicalCutoff_coeFn (radius : ℝ) (value : BurnolL2) :
    (originalPhysicalCutoff radius value : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval radius).indicator (value : ℝ → ℂ) := by
  have restricted := (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) value)
  filter_upwards [burnolRadiusZeroExtension_coe (burnolRadiusRestriction radius value),
    restricted] with x extension restriction
  change originalPhysicalCutoff radius value x = _ at extension
  rw [extension]
  by_cases inside : x ∈ symmetricInterval radius
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
    exact restriction inside
  · rw [Set.indicator_of_notMem inside, Set.indicator_of_notMem inside]

theorem originalPhysicalCutoff_integrable (radius : ℝ) (value : BurnolL2) :
    Integrable (originalPhysicalCutoff radius value : ℝ → ℂ) volume :=
  (burnolRadiusZeroExtensionRaw_integrable (burnolRadiusRestriction radius value)).congr
    (burnolRadiusZeroExtension_coe (burnolRadiusRestriction radius value)).symm

theorem originalPhysicalCutoff_firstMoment (radius : ℝ) (value : BurnolL2) :
    MemLp (fun x : ℝ => (x : ℂ) * originalPhysicalCutoff radius value x) 2 volume := by
  apply (Lp.memLp (originalPhysicalCutoff radius value)).of_le_mul (c := radius)
    (Complex.continuous_ofReal.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (originalPhysicalCutoff radius value)))
  filter_upwards [originalPhysicalCutoff_coeFn radius value] with x read
  dsimp only [Pi.mul_apply]
  by_cases inside : x ∈ symmetricInterval radius
  · have bound : |x| ≤ radius := abs_le.mpr (by simpa only [symmetricInterval, mem_Icc] using inside)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right bound (norm_nonneg _)
  · simp only [read, Set.indicator_of_notMem inside, mul_zero, norm_zero]
    exact le_rfl

theorem originalPhysicalCutoff_sample_zero (radius : ℝ) (value : BurnolL2) (n : ℕ)
    (beyond : 4 * radius ≤ n) :
    burnolAnnulusSamplingL2 (originalPhysicalCutoff radius value) n = 0 := by
  have positive : 0 < (n : ℝ) + 1 := by positivity
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => ((n : ℝ) + 1) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (n : ℝ) + 1) positive.ne')
  apply Lp.ext
  filter_upwards [burnolAnnulusSamplingL2_coeFn (originalPhysicalCutoff radius value) n,
    qmp.ae (originalPhysicalCutoff_coeFn radius value), Lp.coeFn_zero ℂ 2 volume]
      with x sampleRead cutoffRead zeroRead
  rw [sampleRead, zeroRead]
  simp only [Pi.zero_apply]
  by_cases inside : x ∈ burnolSamplingAnnulus
  · have lower : (1 / 4 : ℝ) < |x| := inside.1
    have outside : ((n : ℝ) + 1) * x ∉ symmetricInterval radius := by
      intro atRadius
      have bound : |((n : ℝ) + 1) * x| ≤ radius :=
        abs_le.mpr (by simpa only [symmetricInterval, mem_Icc] using atRadius)
      rw [abs_mul, abs_of_pos positive] at bound
      nlinarith
    simp only [burnolAnnulusSamplingRaw, Set.indicator_of_mem inside]
    rw [cutoffRead, Set.indicator_of_notMem outside]
  · simp only [burnolAnnulusSamplingRaw, Set.indicator_of_notMem inside]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
