import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.TransposeKernel
import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.ProbeCutoffValue

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory Set
open OriginalPaPhysicalGreen
noncomputable section

private theorem cutoff_sample_zero (radius : ℝ) (value : BurnolL2) (n : ℕ)
    (beyond : 4 * radius ≤ (n : ℝ) + 1) :
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
      with x sampled cutoff zero
  rw [sampled, zero]
  simp only [Pi.zero_apply]
  by_cases inside : x ∈ burnolSamplingAnnulus
  · have lower : (1 / 4 : ℝ) < |x| := inside.1
    have outside : ((n : ℝ) + 1) * x ∉ symmetricInterval radius := by
      intro membership
      have bound : |((n : ℝ) + 1) * x| ≤ radius := abs_le.mpr membership
      rw [abs_mul, abs_of_pos positive] at bound
      have strict := mul_lt_mul_of_pos_left lower positive
      nlinarith
    simp only [burnolAnnulusSamplingRaw, Set.indicator_of_mem inside]
    rw [cutoff, Set.indicator_of_notMem outside]
  · simp only [burnolAnnulusSamplingRaw, Set.indicator_of_notMem inside]

theorem samplingKernel_eq_first_of_half_cutoff (value : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2 : ℝ) value = value) :
    burnolPaSamplingKernel value = burnolAnnulusSamplingL2 value 0 := by
  unfold burnolPaSamplingKernel
  apply tsum_eq_single (0 : ℕ)
  intro n different
  have lower : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr different)
  have beyond : 4 * (1 / 2 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  simpa only [supported] using cutoff_sample_zero (1 / 2 : ℝ) value n beyond

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
