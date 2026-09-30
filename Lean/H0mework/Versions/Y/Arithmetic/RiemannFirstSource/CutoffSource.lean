import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.Coefficient

/-! The actual first coefficient generates a weighted step source and an original Pa wave together. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem burnolFirstSourceWeightedRaw_memLp (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    MemLp (fun x : ℝ => burnolFirstSourceCoefficient coordinate source (|x|⁻¹) *
      burnolReciprocalStepSourceRaw (1 / 4) 4 x) 2 volume := by
  have regular := burnolFirstSourceCoefficient_continuous coordinate source
  obtain ⟨bound, bounded⟩ := (isCompact_Icc : IsCompact (Icc (1 / 4 : ℝ) 4)).exists_bound_of_continuousOn
    regular.continuousOn
  apply (burnolReciprocalStepSource_memLp (1 / 4) 4 (by norm_num) (by norm_num)).of_le_mul (c := bound)
    (((regular.measurable.comp (by fun_prop)).mul (burnolReciprocalStepSource_measurable (1 / 4) 4)).aestronglyMeasurable)
  filter_upwards with x
  change ‖burnolFirstSourceCoefficient coordinate source (|x|⁻¹) * burnolReciprocalStepSourceRaw (1 / 4) 4 x‖ ≤ _
  rw [norm_mul]
  by_cases active : (1 / 4 : ℝ) ≤ |x|⁻¹ ∧ |x|⁻¹ < 4
  · exact mul_le_mul_of_nonneg_right (bounded _ ⟨active.1, active.2.le⟩) (norm_nonneg _)
  · simp only [burnolReciprocalStepSourceRaw, if_neg active, norm_zero, mul_zero, le_refl]

theorem burnolFirstSourceWeightedSource_coe (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    (burnolWeightedReciprocalStepSource (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
      (burnolFirstSourceCoefficientSlope coordinate source) : ℝ → ℂ) =ᵐ[volume]
        fun x => burnolFirstSourceCoefficient coordinate source (|x|⁻¹) * burnolReciprocalStepSourceRaw (1 / 4) 4 x := by
  let raw := fun x => burnolFirstSourceCoefficient coordinate source (|x|⁻¹) * burnolReciprocalStepSourceRaw (1 / 4) 4 x
  let bounded := burnolFirstSourceWeightedRaw_memLp coordinate source
  have same : burnolWeightedReciprocalStepSource (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
      (burnolFirstSourceCoefficientSlope coordinate source) = bounded.toLp raw := by
    apply ext_inner_left ℂ
    intro test
    rw [burnolWeightedReciprocalStepSource_pairing (1 / 4) 4 _ _ (by norm_num) (by norm_num)
      (fun t ht => burnolFirstSourceCoefficient_hasDerivAt coordinate source ht)
      (burnolFirstSourceCoefficientSlope_continuous coordinate source).continuousOn
      (burnolFirstSourceCoefficientSlope_continuous coordinate source).measurable, L2.inner_def]
    exact integral_congr_ae ((bounded.coeFn_toLp).symm.mono fun x hx => congrArg (inner ℂ (test x)) hx)
  rw [same]
  exact bounded.coeFn_toLp

theorem burnolFirstSourceTateWeighted_coe (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    (burnolTateReciprocalL2 (burnolWeightedReciprocalStepSource (1 / 4) 4
      (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source)) : ℝ → ℂ) =ᵐ[volume]
      fun x => if (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4 then burnolFirstSourceCoefficient coordinate source |x| else 0 := by
  let value := burnolWeightedReciprocalStepSource (1 / 4) 4
    (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source)
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp value)
    (burnolFirstSourceWeightedRaw_memLp coordinate source) (burnolFirstSourceWeightedSource_coe coordinate source)
  filter_upwards [burnolTateReciprocalL2_coeFn value, pulled, volume.ae_ne (0 : ℝ)] with x hread hpull nonzero
  change burnolTateReciprocalL2 value x = _
  rw [hread, hpull]
  simp only [burnolTateReciprocalRaw, burnolReciprocalStepSourceRaw, abs_inv, inv_inv, Complex.ofReal_inv]
  by_cases active : (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4
  · rw [if_pos active, if_pos active]
    field_simp [Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)]
  · rw [if_neg active, if_neg active, mul_zero, mul_zero]

theorem burnolFirstSourceWeightedWave_inPa (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolWeightedReciprocalStepWave (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
      (burnolFirstSourceCoefficientSlope coordinate source) ∈ burnolOriginalPaInL2 :=
  burnolWeightedReciprocalStepWave_inPa (1 / 4) 4 _ _ (by norm_num) (by norm_num)
    (burnolFirstSourceCoefficientSlope_continuous coordinate source).continuousOn

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
