import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Synthesis.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Commutator
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Physical.Action

/-! Actual source action generates its finite physical Pa landing and retains the exterior wave. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem original_pa_tate_source_injective
    (left right : BurnolPaAmbientCarrier)
    (leftPa : left ∈ burnolCompactCoPoissonClosedRange)
    (rightPa : right ∈ burnolCompactCoPoissonClosedRange)
    (same : burnolTateReciprocalL2 (burnolMobiusSourceL2 left) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2 right)) : left = right := by
  have source := congrArg burnolTateReciprocalL2 same
  simp only [burnolTateReciprocalL2_involutive] at source
  apply Subtype.ext
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (left : BurnolL2)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2 (right : BurnolL2)) test
  simp only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
  rw [← burnolRemainderSourceRead_Pa left leftPa test,
    ← burnolRemainderSourceRead_Pa right rightPa test, source]

theorem sourceVolterraPhysical_original_correction
    (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    sourceVolterraPhysical coordinate (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
      burnolPaSourceCorrection coordinate ⟨p, inside⟩ := by
  apply original_pa_tate_source_injective _ _ (sourceVolterraPhysical_mem coordinate _)
    (burnolPaSourceCorrection_mem coordinate ⟨p, inside⟩)
  rw [sourceVolterraPhysical_source coordinate _ (original_tate_source_even p)
    (sourceAnnulusCut_original_pa p inside), sourceVolterraWindow_original_pa coordinate p inside]

/-- The finite physical action is synthesized from the moved source and its generated collar. -/
def sourceTruncatedPhysicalAction
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) : BurnolPaAmbientCarrier :=
  sourceVolterraPhysical coordinate (sourceAnnulusCut (burnolMultiplicativeDilation (-h)
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) -
      sourceCollarPhysicalState coordinate h p admitted

theorem sourceTruncatedPhysicalAction_mem
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) :
    sourceTruncatedPhysicalAction coordinate h p admitted ∈ burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem
    (sourceVolterraPhysical_mem coordinate _) (sourceCollarPhysicalState_mem coordinate h p admitted)

/-- The physical landing reads back the finite observation of the actual evolved corrected source. -/
theorem sourceTruncatedPhysicalAction_source
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2
      (sourceTruncatedPhysicalAction coordinate h p admitted)) =
      sourceAnnulusCut (burnolMultiplicativeDilation (-h)
        (burnolTateReciprocalL2 (burnolMobiusSourceL2
          (burnolPaSourceCorrection coordinate ⟨p, inside⟩)))) := by
  have movedEven : reflectL2 (burnolMultiplicativeDilation (-h)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) =
      burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) := by
    rw [reflectL2_burnolMultiplicativeDilation, original_tate_source_even]
  rw [sourceTruncatedPhysicalAction, map_sub, map_sub,
    sourceVolterraPhysical_source coordinate _ (sourceAnnulusCut_even _ movedEven)
      (sourceAnnulusCut_idempotent _)]
  have actual := original_source_volterra_commutator coordinate h forward admitted p inside
  rw [sourceVolterraWindow_original_pa coordinate p inside] at actual
  rw [← actual]
  abel

/-- The exterior source realizes exactly what the generated finite Pa face did not retain. -/
theorem sourceExteriorCollar_realizes
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (sourceExteriorCollar h
      (burnolTateReciprocalL2 (burnolMobiusSourceL2
        (burnolPaSourceCorrection coordinate ⟨p, inside⟩)))) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation (-h)
          (fourierL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩ : BurnolL2)) -
        fourierL2 (sourceTruncatedPhysicalAction coordinate h p admitted : BurnolL2))) test := by
  rw [sourceExteriorCollar, ← sourceTruncatedPhysicalAction_source coordinate h forward admitted p inside,
    ← burnolRemainderSourceReadCLM_apply, map_sub,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    original_tate_source_shift_realizes _ _ (burnolPaSourceCorrection_mem coordinate ⟨p, inside⟩),
    original_tate_source_realizes _ (sourceTruncatedPhysicalAction_mem coordinate h p admitted),
    map_sub, sub_apply]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
