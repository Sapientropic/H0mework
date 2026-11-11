import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Pairing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Cutoff.Transpose

/-! The original projected head generates its free-probe source balance through one actual Pa test. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def originalHeadWindowSourceRead {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) : ℂ :=
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  let J := sourceSecondWindow probe ⟨p, Submodule.starProjection_apply_mem _ _⟩
  inner ℂ (burnolPaSamplingKernel (B : BurnolL2)) J +
    ((-1 / 2 : ℂ) * burnolSourceWindowIntegral (burnolTateReciprocalL2 J)) *
      star (∫ x : ℝ, (B : BurnolL2) x)

theorem original_head_window_source_normal {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    inner ℂ p (secondWindowPhysical probe ⟨p, Submodule.starProjection_apply_mem _ _⟩) =
      originalHeadWindowSourceRead observation nontrivial rightHalf probe := by
  intro B p
  let input : burnolCompactCoPoissonClosedRange.toSubmodule :=
    ⟨p, Submodule.starProjection_apply_mem _ _⟩
  let actual := secondWindowPhysical probe input
  have inside := secondWindowPhysical_mem probe input
  have generated := burnolPaSamplingKernel_fullPa (B : BurnolL2)
    (burnolPaCombPairedPhysicalResponse_integrable observation nontrivial rightHalf 0)
    (burnolPaCombPairedPhysicalResponse_firstMoment observation nontrivial rightHalf 0) actual inside
  rw [burnolPaPositionMean_from_source actual inside, secondWindowPhysical_source probe input] at generated
  have normal := original_head_window_normalEquation observation nontrivial rightHalf probe
  change inner ℂ B actual = inner ℂ p actual at normal
  change inner ℂ B actual = _ at generated
  exact normal.symm.trans generated

theorem original_head_freeProbe_source_balance {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let z : BurnolCompletedMellinCoordinate := ⟨(3 / 4 : ℂ), by norm_num, by norm_num⟩
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let v := burnolUnitTailResponse z (1 / 4) + burnolUnitTailResponse z 4
    Tendsto (fun N => (‖burnolDirectRightResolvent (3 / 8) (p : BurnolL2)‖ : ℂ) ^ 2 +
      4 * burnolPaResolventSourceCoefficient z p * star (finitePhysicalSourceRead v p N) +
        originalHeadWindowSourceRead observation nontrivial rightHalf z) atTop (𝓝 0) := by
  intro z B p v
  let input : burnolCompactCoPoissonClosedRange.toSubmodule :=
    ⟨p, Submodule.starProjection_apply_mem _ _⟩
  have fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius (input : BurnolPaAmbientCarrier) = input :=
    burnolPaProjectedHead_fourier_fixed observation nontrivial rightHalf
  have current := physicalWindow_threeQuarter_source_tendsto input fixed
  have normal := original_head_window_source_normal observation nontrivial rightHalf z
  change inner ℂ (input : BurnolL2) (secondWindowPhysical z input : BurnolL2) =
    originalHeadWindowSourceRead observation nontrivial rightHalf z at normal
  change Tendsto (fun N => -(‖burnolDirectRightResolvent (3 / 8) (p : BurnolL2)‖ : ℂ) ^ 2 -
      4 * burnolPaResolventSourceCoefficient z p * star (finitePhysicalSourceRead v p N)) atTop
    (𝓝 (inner ℂ (input : BurnolL2) (secondWindowPhysical z input : BurnolL2))) at current
  rw [normal] at current
  have generated := current.neg.add_const (originalHeadWindowSourceRead observation nontrivial rightHalf z)
  simp only [neg_add_cancel] at generated
  convert! generated using 1
  funext N
  ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
