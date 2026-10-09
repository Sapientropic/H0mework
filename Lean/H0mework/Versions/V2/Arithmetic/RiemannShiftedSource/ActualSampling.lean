import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.Cells
import H0mework.Versions.V2.Arithmetic.RiemannRationalSource.ActualSampling

/-! Actual half-density dilation, annular sampling and Tate have one source-generated profile. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def originalShiftedReciprocalSampleWave (s : ℂ) (h : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) * (t : ℂ)⁻¹ *
    (burnolUnitTailDirichletRaw s 1 (Real.exp h * n / t) -
      burnolUnitTailDirichletRaw (1 - s) 1 (Real.exp h * n / t))

theorem original_shifted_wave_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    (burnolMultiplicativeDilation h W : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (h / 2) : ℂ) *
        (burnolUnitTailDirichletRaw observation.coordinate 1 (Real.exp h * x) -
          burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 (Real.exp h * x)) := by
  intro one W
  have qmp : Measure.QuasiMeasurePreserving
      (fun t : ℝ => Real.exp h * t) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [burnolMultiplicativeDilation_coeFn h W, qmp.ae
    (burnolZeroOwnedUnitOnePair_dirichlet_coeFn observation nontrivial rightHalf)]
      with x read original
  rw [read]
  change (Real.exp (h / 2) : ℂ) * W (Real.exp h * x) = _
  rw [original]

theorem original_shifted_reciprocal_sample_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ) (n : ℕ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    (burnolTateReciprocalL2
      (burnolAnnulusSamplingL2 (burnolMultiplicativeDilation h W) n) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioo (1 / 4 : ℝ) 4)]
        originalShiftedReciprocalSampleWave observation.coordinate h (n + 1) := by
  intro one W
  let shifted := burnolMultiplicativeDilation h W
  let profile : ℝ → ℂ := fun x => (Real.exp (h / 2) : ℂ) *
    (burnolUnitTailDirichletRaw observation.coordinate 1 (Real.exp h * x) -
      burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 (Real.exp h * x))
  let sampled : ℝ → ℂ := burnolSamplingAnnulus.indicator
    (fun t => profile (((n : ℝ) + 1) * t))
  have positive : 0 < (n : ℝ) + 1 := by positivity
  have qmp : Measure.QuasiMeasurePreserving
      (fun t : ℝ => ((n : ℝ) + 1) * t) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (n : ℝ) + 1) positive.ne')
  have sampleRead : burnolAnnulusSamplingRaw shifted n =ᵐ[volume] sampled := by
    filter_upwards [qmp.ae
      (original_shifted_wave_coeFn observation nontrivial rightHalf h)] with t read
    by_cases inside : t ∈ burnolSamplingAnnulus
    · simpa only [burnolAnnulusSamplingRaw, sampled, Set.indicator_of_mem inside] using read
    · simp only [burnolAnnulusSamplingRaw, sampled, Set.indicator_of_notMem inside]
  have sourceRead := (burnolAnnulusSamplingL2_coeFn shifted n).trans sampleRead
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolAnnulusSamplingL2 shifted n))
    ((memLp_congr_ae sampleRead).mp (burnolAnnulusSamplingRaw_memLp shifted n)) sourceRead
  filter_upwards [ae_restrict_of_ae
    (burnolTateReciprocalL2_coeFn (burnolAnnulusSamplingL2 shifted n)),
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
    abs_of_pos tp, profile, originalShiftedReciprocalSampleWave, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv, mul_assoc]
  ring

theorem original_shifted_reciprocal_sample_cell (s : ℂ) (h : ℝ) (n k : ℕ) {t : ℝ}
    (inside : Real.exp h * n / t ∈ Ioc (k : ℝ) (k + 1 : ℝ)) :
    originalShiftedReciprocalSampleWave s h n t = shiftedReciprocalWave s h n k t := by
  unfold originalShiftedReciprocalSampleWave shiftedReciprocalWave
  rw [OriginalPaGreenContact.cell_wave_read s k inside]

theorem original_shifted_reciprocal_sample_integrable {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (h : ℝ) (n : ℕ)
    {a b : ℝ} (lower : (1 / 4 : ℝ) ≤ a) (ordered : a ≤ b) (upper : b ≤ 4) :
    IntervalIntegrable (fun t : ℝ => source.1 t *
      originalShiftedReciprocalSampleWave observation.coordinate h (n + 1) t) volume a b := by
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let W : BurnolL2 := (one +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
  let sampled := burnolTateReciprocalL2
    (burnolAnnulusSamplingL2 (burnolMultiplicativeDilation h W) n)
  have integrable : Integrable (fun t : ℝ => source.1 t * sampled t) volume :=
    (source.1.memLp 2 volume).integrable_mul (Lp.memLp sampled)
  have actual := (ae_restrict_iff' measurableSet_Ioo).mp
    (original_shifted_reciprocal_sample_coeFn observation nontrivial rightHalf h n)
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
