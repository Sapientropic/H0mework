import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.PrimeThree.Physical.Residue
import H0mework.Versions.R7e4da746.Arithmetic.RiemannNativeCurrent.Laplace

/-! The same original head reads the physical prime-three residue through its paired compression. -/

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

theorem original_head_residue_channel_readout {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    let h := Real.log (Real.sqrt 3)
    let c : ℂ := (Real.sqrt (Real.sqrt 3) : ℝ)
    inner ℂ (Z : BurnolL2)
      (c • burnolMultiplicativeDilation h (p : BurnolL2) -
        c⁻¹ • burnolMultiplicativeDilation (-h) (p : BurnolL2)) =
      (c - c⁻¹) * inner ℂ (Z : BurnolPaAmbientCarrier)
        (burnolPairedAmbientCompression h p) := by
  intro B p Z h c
  have negative := burnolPairedAmbientCompression_inner_fixed h
    (Z : BurnolPaAmbientCarrier) p
    (burnolZeroOwnedUnitFourierPaState_fixed observation nontrivial rightHalf)
    (burnolPaProjectedHead_fourier_fixed observation nontrivial rightHalf)
  have positive := burnolPairedAmbientCompression_inner_fixed (-h)
    (Z : BurnolPaAmbientCarrier) p
    (burnolZeroOwnedUnitFourierPaState_fixed observation nontrivial rightHalf)
    (burnolPaProjectedHead_fourier_fixed observation nontrivial rightHalf)
  have same : burnolPairedAmbientCompression (-h) = burnolPairedAmbientCompression h := by
    unfold burnolPairedAmbientCompression
    rw [neg_neg, add_comm]
  rw [same, neg_neg] at positive
  rw [inner_sub_right, inner_smul_right, inner_smul_right]
  rw [← positive, ← negative]
  ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
