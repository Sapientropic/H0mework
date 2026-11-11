import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.ShiftedProfile
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Physical.Bands
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.AnnulusExt

/-! The finite source action has an actual Pa collar, while the exterior shifted source is retained. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

/-- The same-source finite commutator is the recovered source of a generated physical Pa state. -/
theorem original_source_volterra_commutator
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    sourceVolterraWindow coordinate (sourceAnnulusCut (burnolMultiplicativeDilation (-h)
        (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) -
      sourceAnnulusCut (burnolMultiplicativeDilation (-h)
        (sourceVolterraWindow coordinate (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2
        (sourceCollarPhysicalState coordinate h p admitted)) := by
  let sigma := burnolTateReciprocalL2 (burnolMobiusSourceL2 p)
  let shifted := burnolMultiplicativeDilation (-h) sigma
  let window := sourceVolterraWindow coordinate sigma
  let collar := sourceCollarPhysicalState coordinate h p admitted
  have sigmaEven : reflectL2 sigma = sigma := original_tate_source_even p
  have shiftedEven : reflectL2 shifted = shifted := by
    change reflectL2 (burnolMultiplicativeDilation (-h) sigma) = _
    rw [reflectL2_burnolMultiplicativeDilation, sigmaEven]
  have windowEven : reflectL2 window = window := sourceVolterraWindow_even coordinate sigma sigmaEven
  have shiftedWindowEven : reflectL2 (burnolMultiplicativeDilation (-h) window) =
      burnolMultiplicativeDilation (-h) window := by
    rw [reflectL2_burnolMultiplicativeDilation, windowEven]
  apply source_even_annulus_ext
  · rw [map_sub, sourceVolterraWindow_even coordinate (sourceAnnulusCut shifted)
      (sourceAnnulusCut_even shifted shiftedEven),
      sourceAnnulusCut_even (burnolMultiplicativeDilation (-h) window) shiftedWindowEven]
  · exact original_tate_source_even collar
  · rw [map_sub]
    change sourceAnnulusCut (sourceAnnulusCut (sourceVolterraResolvent coordinate
      (sourceAnnulusCut shifted))) -
        sourceAnnulusCut (sourceAnnulusCut (burnolMultiplicativeDilation (-h) window)) = _
    rw [sourceAnnulusCut_idempotent, sourceAnnulusCut_idempotent]
    rfl
  · exact sourceAnnulusCut_original_pa collar (sourceCollarPhysicalState_mem coordinate h p admitted)
  · have localRead := original_source_shifted_window_contact coordinate h forward p inside
    rw [← sourceAnnulusCut_dilation_original p h forward] at localRead
    have physicalRead := (ae_restrict_iff' measurableSet_Ico).mp
      (sourceCollarPhysicalState_source_contact_band coordinate h p admitted)
    filter_upwards [localRead, physicalRead] with t original physical member
    exact (original member).trans (physical ⟨member.1.le, member.2⟩).symm

/-- The uncut shifted source is not silently replaced by its finite observation. -/
def sourceExteriorCollar (h : ℝ) (value : BurnolL2) : BurnolL2 :=
  burnolMultiplicativeDilation (-h) value -
    sourceAnnulusCut (burnolMultiplicativeDilation (-h) value)

/-- The whole-source action retains its exterior collar beside the generated Pa correction. -/
theorem original_source_volterra_whole_update
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    sourceVolterraWindow coordinate (sourceAnnulusCut (burnolMultiplicativeDilation (-h)
        (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) -
      burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2
        (burnolPaSourceCorrection coordinate ⟨p, inside⟩))) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2
        (sourceCollarPhysicalState coordinate h p admitted)) -
      sourceExteriorCollar h (burnolTateReciprocalL2 (burnolMobiusSourceL2
        (burnolPaSourceCorrection coordinate ⟨p, inside⟩))) := by
  have actual := original_source_volterra_commutator coordinate h forward admitted p inside
  rw [sourceVolterraWindow_original_pa coordinate p inside] at actual
  unfold sourceExteriorCollar
  rw [← actual]
  abel

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
