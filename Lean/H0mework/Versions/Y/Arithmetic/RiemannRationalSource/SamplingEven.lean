import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.EvenWindow

/-! The original even source and annular samples retain their full support and pairing. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem annulus_sampling_even (value : BurnolL2) (even : reflectL2 value = value) (n : ℕ) :
    reflectL2 (burnolAnnulusSamplingL2 value n) = burnolAnnulusSamplingL2 value n := by
  let raw := burnolEvenStrongRepresentative value
  let sample : ℝ → ℂ := burnolSamplingAnnulus.indicator (fun x => raw (((n : ℝ) + 1) * x))
  have rawEven (x : ℝ) : raw (-x) = raw x := by
    unfold raw burnolEvenStrongRepresentative
    simp only [neg_neg, add_comm]
  have sampleEven (x : ℝ) : sample (-x) = sample x := by
    simp only [sample, Set.indicator_apply, burnolSamplingAnnulus, Set.mem_ofPred_eq, abs_neg,
      mul_neg, rawEven]
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => ((n : ℝ) + 1) * x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := (n : ℝ) + 1) (by positivity : (n : ℝ) + 1 ≠ 0)
  have rawRead := burnolEvenStrongRepresentative_ae_eq value even
  have sampleRead : (burnolAnnulusSamplingL2 value n : ℝ → ℂ) =ᵐ[volume] sample := by
    filter_upwards [burnolAnnulusSamplingL2_coeFn value n, qmp.ae rawRead] with x actual read
    rw [actual]
    change burnolSamplingAnnulus.indicator (fun x => value (((n : ℝ) + 1) * x)) x = sample x
    by_cases inside : x ∈ burnolSamplingAnnulus
    · simp only [Set.indicator_of_mem inside, sample]
      exact read.symm
    · simp only [sample, Set.indicator_of_notMem inside]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (burnolAnnulusSamplingL2 value n) negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae sampleRead, sampleRead] with x reflection negative positive
  change reflectL2 (burnolAnnulusSamplingL2 value n) x =
    burnolAnnulusSamplingL2 value n (-x) at reflection
  rw [reflection, negative, positive, sampleEven]

theorem pa_sampling_kernel_even (value : BurnolL2) (even : reflectL2 value = value)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume) :
    reflectL2 (burnolPaSamplingKernel value) = burnolPaSamplingKernel value := by
  have summed := reflectL2.toContinuousLinearMap.map_tsum
    (burnolAnnulusSamplingL2_summable value moment)
  change reflectL2 (burnolPaSamplingKernel value) =
    ∑' n : ℕ, reflectL2 (burnolAnnulusSamplingL2 value n) at summed
  rw [summed]
  exact tsum_congr (annulus_sampling_even value even)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
