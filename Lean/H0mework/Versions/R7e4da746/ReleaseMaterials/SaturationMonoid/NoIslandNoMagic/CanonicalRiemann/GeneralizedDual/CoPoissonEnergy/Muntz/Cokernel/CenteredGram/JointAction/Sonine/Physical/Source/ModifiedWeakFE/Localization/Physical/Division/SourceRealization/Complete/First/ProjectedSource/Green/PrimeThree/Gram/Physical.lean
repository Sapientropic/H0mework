import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.Residue
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.OriginalHead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Cutoff.Transpose

/-! The residue calculation is tested in the original physical Gram, including the actual projected residual. -/

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

def originalPrimeThreeResidualGram {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) : ℂ :=
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  inner ℂ (originalPhysicalCutoff (N + 1 : ℝ) ((B : BurnolL2) - (p : BurnolL2)))
    (primeThreePhysicalResidue (p : BurnolL2))

theorem originalPrimeThreeResidualGram_integral {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    originalPrimeThreeResidualGram observation nontrivial rightHalf N =
      ∫ x : ℝ in symmetricInterval (N + 1 : ℝ),
        star ((B : BurnolL2) x - (p : BurnolL2) x) * primeThreePhysicalResidue (p : BurnolL2) x := by
  intro B p
  rw [originalPrimeThreeResidualGram, originalPhysicalCutoff_pairing]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (B : BurnolL2) (p : BurnolL2))]
    with x difference
  rw [difference, Pi.sub_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

theorem originalPrimeThreeResidualGram_tendsto {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    let c : ℂ := (Real.sqrt (Real.sqrt 3) : ℝ)
    Tendsto (originalPrimeThreeResidualGram observation nontrivial rightHalf) atTop
      (𝓝 (star (burnolPaCombResponseCoefficient observation.coordinate 0) * (c - c⁻¹) *
        inner ℂ (Z : BurnolPaAmbientCarrier)
          (burnolPairedAmbientCompression (Real.log (Real.sqrt 3)) p))) := by
  intro B p Z c
  have generated := originalPhysicalCutoff_pairing_tendsto
    ((B : BurnolL2) - (p : BurnolL2)) (primeThreePhysicalResidue (p : BurnolL2))
  have original := burnolPaCombPairedPhysicalResponse_Q observation nontrivial rightHalf 0
  rw [Submodule.starProjection_orthogonal_val] at original
  change B - p = burnolPaCombResponseCoefficient observation.coordinate 0 •
    (Z : BurnolPaAmbientCarrier) at original
  have physical : (B : BurnolL2) - (p : BurnolL2) =
      burnolPaCombResponseCoefficient observation.coordinate 0 • (Z : BurnolL2) :=
    congrArg Subtype.val original
  have current := original_head_residue_channel_readout observation nontrivial rightHalf
  change inner ℂ (Z : BurnolL2) (primeThreePhysicalResidue (p : BurnolL2)) =
    (c - c⁻¹) * inner ℂ (Z : BurnolPaAmbientCarrier)
      (burnolPairedAmbientCompression (Real.log (Real.sqrt 3)) p) at current
  have pairing : inner ℂ ((B : BurnolL2) - (p : BurnolL2))
      (primeThreePhysicalResidue (p : BurnolL2)) =
      star (burnolPaCombResponseCoefficient observation.coordinate 0) * (c - c⁻¹) *
        inner ℂ (Z : BurnolPaAmbientCarrier)
          (burnolPairedAmbientCompression (Real.log (Real.sqrt 3)) p) := by
    rw [physical, inner_smul_left, current]
    change star _ * ((c - c⁻¹) * _) = _
    ring
  rw [pairing] at generated
  exact generated

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
