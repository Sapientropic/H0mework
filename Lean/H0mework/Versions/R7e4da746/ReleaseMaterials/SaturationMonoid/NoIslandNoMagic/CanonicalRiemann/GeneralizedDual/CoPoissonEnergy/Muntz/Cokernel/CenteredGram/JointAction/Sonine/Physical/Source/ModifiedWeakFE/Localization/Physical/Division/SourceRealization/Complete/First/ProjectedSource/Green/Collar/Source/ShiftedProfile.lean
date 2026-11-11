import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Contact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Window

/-! The finite collar identity reads actual shifted L² vectors of the original Pa source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem original_shifted_contact_profile (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    (burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2
      (burnolPaSourceCorrection coordinate ⟨p, inside⟩))) : ℝ → ℂ) =ᵐ[volume]
      fun t => (Real.exp (-h / 2) : ℂ) * firstContactRead coordinate (t * Real.exp (-h)) p := by
  have qmp : Measure.QuasiMeasurePreserving
      (fun t : ℝ => Real.exp (-h) * t) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (-h)) (Real.exp_ne_zero (-h)))
  filter_upwards [burnolMultiplicativeDilation_coeFn (-h)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2
        (burnolPaSourceCorrection coordinate ⟨p, inside⟩))),
    qmp.ae (pa_correction_contact_profile coordinate p inside)] with t native source
  rw [native]
  unfold burnolL2RawNormalizedDilation
  rw [source, mul_comm (Real.exp (-h)) t]

theorem sourceVolterraWindow_outer_cut_profile
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ∀ᵐ t ∂volume, ∀ inside : t ∈ Ioo (1 / 4 : ℝ) 4,
      sourceVolterraWindow coordinate (originalPhysicalCutoff 4 value) t =
        finiteSourceContact coordinate t (by linarith [inside.1])
          (originalPhysicalCutoff 4 value) := by
  filter_upwards [sourceVolterraWindow_positive_profile coordinate
    (originalPhysicalCutoff 4 value)] with t source inside
  rw [source inside, finiteSourceContact,
    source_tail_cutoff_outside coordinate 4 (by norm_num) 4 le_rfl]
  simp only [sub_zero]

/-- Both sides are values of the original L² operators, with no shifted Pa hypothesis. -/
theorem original_source_shifted_window_contact
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (p : BurnolPaAmbientCarrier) (insidePa : p ∈ burnolCompactCoPoissonClosedRange) :
    ∀ᵐ t ∂volume, ∀ _inside : t ∈ Ioo (1 / 4 : ℝ) 4,
      (sourceVolterraWindow coordinate (originalPhysicalCutoff 4
        (burnolMultiplicativeDilation (-h)
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) -
       sourceAnnulusCut (burnolMultiplicativeDilation (-h)
         (sourceVolterraWindow coordinate
           (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) : BurnolL2) t =
        fullMellinTranslationCharacter coordinate.value h * (t : ℂ) ^ (coordinate.value - 1) *
          (sourceOuterCollarCoefficient coordinate h
              (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) -
            if t * Real.exp (-h) < (1 / 4 : ℝ) then
              burnolPaResolventSourceCoefficient coordinate p else 0) := by
  let left := sourceVolterraWindow coordinate (originalPhysicalCutoff 4
    (burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))))
  let shifted := burnolMultiplicativeDilation (-h)
    (sourceVolterraWindow coordinate (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))
  have profile : (shifted : ℝ → ℂ) =ᵐ[volume]
      fun t => (Real.exp (-h / 2) : ℂ) * firstContactRead coordinate (t * Real.exp (-h)) p := by
    dsimp only [shifted]
    rw [sourceVolterraWindow_original_pa coordinate p insidePa]
    exact original_shifted_contact_profile coordinate h p insidePa
  filter_upwards [Lp.coeFn_sub left (sourceAnnulusCut shifted),
    sourceVolterraWindow_outer_cut_profile coordinate (burnolMultiplicativeDilation (-h)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))),
    sourceAnnulusCut_coeFn shifted, profile] with t difference leftRead rightRead shiftedRead inside
  have positive : 0 < t := by linarith [inside.1]
  change (left - sourceAnnulusCut shifted : BurnolL2) t = _
  rw [difference, Pi.sub_apply, rightRead,
    if_pos (by simpa only [abs_of_pos positive] using ⟨inside.1, inside.2.le⟩), shiftedRead]
  change left t - _ = _
  rw [leftRead inside]
  exact original_source_contact_reverse_commutator coordinate h forward p insidePa t
    ⟨inside.1.le, inside.2⟩

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
