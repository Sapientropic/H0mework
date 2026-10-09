import H0mework.Versions.V2.Arithmetic.RiemannRationalSource.ReciprocalCells
import H0mework.Versions.V2.Arithmetic.RiemannBandKernel.Sampling

/-! Original W, annular sampling and Tate reciprocity share the actual rational raw profile. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def originalReciprocalSampleWave (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * (burnolUnitTailDirichletRaw s 1 ((n : ℝ) / t) -
    burnolUnitTailDirichletRaw (1 - s) 1 ((n : ℝ) / t))

theorem original_reciprocal_sample_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : ℕ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    (burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioo (1 / 4 : ℝ) 4)]
        originalReciprocalSampleWave observation.coordinate (n + 1) := by
  intro one W
  let profile : ℝ → ℂ := fun x =>
    burnolUnitTailDirichletRaw observation.coordinate 1 x -
      burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 x
  let sampled : ℝ → ℂ := burnolSamplingAnnulus.indicator
    (fun t => profile (((n : ℝ) + 1) * t))
  have positive : 0 < (n : ℝ) + 1 := by positivity
  have qmp : Measure.QuasiMeasurePreserving
      (fun t : ℝ => ((n : ℝ) + 1) * t) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (n : ℝ) + 1) positive.ne')
  have sampleRead : burnolAnnulusSamplingRaw W n =ᵐ[volume] sampled := by
    filter_upwards [qmp.ae
      (burnolZeroOwnedUnitOnePair_dirichlet_coeFn observation nontrivial rightHalf)]
        with t read
    by_cases inside : t ∈ burnolSamplingAnnulus
    · simpa only [burnolAnnulusSamplingRaw, sampled, Set.indicator_of_mem inside] using read
    · simp only [burnolAnnulusSamplingRaw, sampled, Set.indicator_of_notMem inside]
  have sourceRead := (burnolAnnulusSamplingL2_coeFn W n).trans sampleRead
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolAnnulusSamplingL2 W n))
    ((memLp_congr_ae sampleRead).mp (burnolAnnulusSamplingRaw_memLp W n)) sourceRead
  filter_upwards [ae_restrict_of_ae
    (burnolTateReciprocalL2_coeFn (burnolAnnulusSamplingL2 W n)),
    ae_restrict_of_ae pulled, ae_restrict_mem measurableSet_Ioo]
      with t read pull inside
  rw [read, pull]
  have tp : 0 < t := lt_trans (by norm_num) inside.1
  have inverseInside : t⁻¹ ∈ burnolSamplingAnnulus := by
    change (1 / 4 : ℝ) < |t⁻¹| ∧ |t⁻¹| ≤ 4
    rw [abs_of_pos (inv_pos.mpr tp)]
    constructor
    · exact (lt_inv_comm₀ (by norm_num) tp).mpr (by simpa using inside.2)
    · exact le_of_lt ((inv_lt_comm₀ tp (by norm_num)).mpr (by simpa using inside.1))
  simp only [burnolTateReciprocalRaw, sampled, Set.indicator_of_mem inverseInside,
    abs_of_pos tp, profile, originalReciprocalSampleWave, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv]

theorem original_reciprocal_sample_cell (s : ℂ) (n k : ℕ) {t : ℝ}
    (inside : (n : ℝ) / t ∈ Ioc (k : ℝ) (k + 1 : ℝ)) :
    originalReciprocalSampleWave s n t = reciprocalSampleWave s n k t := by
  unfold originalReciprocalSampleWave reciprocalSampleWave
  rw [OriginalPaGreenContact.cell_wave_read s k inside]

theorem original_reciprocal_sample_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (n : ℕ)
    {a b : ℝ} (lower : (1 / 4 : ℝ) ≤ a) (ordered : a ≤ b) (upper : b ≤ 4) :
    IntervalIntegrable (fun t : ℝ => source.1 t *
      originalReciprocalSampleWave observation.coordinate (n + 1) t) volume a b := by
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  let sampled := burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n)
  have integrable : Integrable (fun t : ℝ => source.1 t * sampled t) volume :=
    (source.1.memLp 2 volume).integrable_mul (Lp.memLp sampled)
  have actual := (ae_restrict_iff' measurableSet_Ioo).mp
    (original_reciprocal_sample_coeFn observation nontrivial rightHalf n)
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ordered).mpr
  apply integrable.integrableOn.congr
  filter_upwards [ae_restrict_of_ae actual, ae_restrict_mem measurableSet_Ioo]
      with t read inside
  have annulus : t ∈ Ioo (1 / 4 : ℝ) 4 :=
    ⟨lt_of_le_of_lt lower inside.1, lt_of_lt_of_le inside.2 upper⟩
  exact congrArg (fun z : ℂ => source.1 t * z) (read annulus)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
