import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Cutoff.Limit

/-! One finite physical cutoff reads the original free-probe boundary and its quadratic current. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def finitePhysicalSourceRead (value : BurnolL2) (p : BurnolPaAmbientCarrier) (N : ℕ) : ℂ :=
  inner ℂ (∑ n ∈ Finset.range (4 * (N + 1)),
    burnolAnnulusSamplingL2 (originalPhysicalCutoff (N + 1 : ℝ) value) n)
      (burnolMobiusSourceL2 p) +
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius p *
      star (∫ x : ℝ, originalPhysicalCutoff (N + 1 : ℝ) value x)

theorem finitePhysicalSourceRead_eq_pairing (value : BurnolL2) (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) (N : ℕ) :
    finitePhysicalSourceRead value p N =
      inner ℂ (originalPhysicalCutoff (N + 1 : ℝ) value) (p : BurnolL2) :=
  (originalPhysicalCutoff_fullPa_transpose (N + 1 : ℝ) value (4 * (N + 1))
    (by norm_num) p inside).symm

theorem finitePhysicalSourceRead_tendsto (value : BurnolL2) (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    Tendsto (finitePhysicalSourceRead value p) atTop (𝓝 (inner ℂ value (p : BurnolL2))) :=
  (originalPhysicalCutoff_pairing_tendsto value (p : BurnolL2)).congr
    (fun N => (finitePhysicalSourceRead_eq_pairing value p inside N).symm)

theorem sourceWindowBoundary_finiteSource_tendsto
    (coordinate : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (p : BurnolPaAmbientCarrier) = p) :
    Tendsto (fun N => star (finitePhysicalSourceRead
      (burnolUnitTailResponse coordinate (1 / 4) + burnolUnitTailResponse coordinate 4) p N)) atTop
      (𝓝 (inner ℂ (p : BurnolL2)
        (burnolUnitTailResponse coordinate (1 / 4) + fourierL2 (burnolUnitTailResponse coordinate 4)))) := by
  have pf : fourierL2 (p : BurnolL2) = p := congrArg Subtype.val fixed
  have same := fourierL2.inner_map_map (p : BurnolL2) (burnolUnitTailResponse coordinate 4)
  rw [pf] at same
  have finiteLimit := (finitePhysicalSourceRead_tendsto
    (burnolUnitTailResponse coordinate (1 / 4) + burnolUnitTailResponse coordinate 4)
      p p.property).star
  simpa only [Complex.star_def, inner_conj_symm, inner_add_right, same] using finiteLimit

theorem physicalWindow_threeQuarter_source_tendsto
    (p : burnolCompactCoPoissonClosedRange.toSubmodule)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (p : BurnolPaAmbientCarrier) = p) :
    let z : BurnolCompletedMellinCoordinate := ⟨(3 / 4 : ℂ), by norm_num, by norm_num⟩
    let v := burnolUnitTailResponse z (1 / 4) + burnolUnitTailResponse z 4
    Tendsto (fun N => -(‖burnolDirectRightResolvent (3 / 8) (p : BurnolL2)‖ : ℂ) ^ 2 -
      4 * burnolPaResolventSourceCoefficient z p * star (finitePhysicalSourceRead v p N)) atTop
        (𝓝 (inner ℂ (p : BurnolL2) (secondWindowPhysical z p : BurnolL2))) := by
  intro z v
  have generated := (tendsto_const_nhds (x :=
    -(‖burnolDirectRightResolvent (3 / 8) (p : BurnolL2)‖ : ℂ) ^ 2)).sub
    ((sourceWindowBoundary_finiteSource_tendsto z p fixed).const_mul
      (4 * burnolPaResolventSourceCoefficient z p))
  have actual : inner ℂ (p : BurnolL2) (secondWindowPhysical z p : BurnolL2) =
      -(‖burnolDirectRightResolvent (3 / 8) (p : BurnolL2)‖ : ℂ) ^ 2 -
        4 * burnolPaResolventSourceCoefficient z p * inner ℂ (p : BurnolL2)
          (burnolUnitTailResponse z (1 / 4) + fourierL2 (burnolUnitTailResponse z 4)) :=
    secondWindowPhysical_three_quarter_pairing p fixed
  rw [actual]
  exact generated

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
