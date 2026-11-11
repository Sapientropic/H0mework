import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Commutator

/-! The whole source update realizes the actual shifted physical correction on all Schwartz tests. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem original_tate_source_shift_realizes (h : ℝ)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
        (burnolMultiplicativeDilation h (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation h (fourierL2 (p : BurnolL2)))) test := by
  rw [← burnolMobiusSource_fourier p inside]
  simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
  exact burnolRemainderSourceRead_Pa_action h
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius p)
    (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside) test

theorem original_tate_source_realizes
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 (p : BurnolL2))) test := by
  rw [← burnolMobiusSource_fourier p inside]
  simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
  exact burnolRemainderSourceRead_Pa (evenFaceFourierEquiv burnolUnscaledCommonGapRadius p)
    (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside) test

/-- The collar update is the same actual physical action; the exterior source is included. -/
theorem original_source_volterra_whole_realizes
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (sourceVolterraWindow coordinate (sourceAnnulusCut (burnolMultiplicativeDilation (-h)
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) +
        sourceExteriorCollar h (burnolTateReciprocalL2 (burnolMobiusSourceL2
          (burnolPaSourceCorrection coordinate ⟨p, inside⟩)))) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation (-h)
          (fourierL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩ : BurnolL2)) +
        fourierL2 (sourceCollarPhysicalState coordinate h p admitted : BurnolL2))) test := by
  have actual := original_source_volterra_whole_update coordinate h forward admitted p inside
  have total := (sub_eq_sub_iff_add_eq_add.mp actual)
  rw [total, ← burnolRemainderSourceReadCLM_apply, map_add,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    original_tate_source_realizes _ (sourceCollarPhysicalState_mem coordinate h p admitted),
    original_tate_source_shift_realizes _ _ (burnolPaSourceCorrection_mem coordinate ⟨p, inside⟩),
    map_add, add_apply]
  ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
