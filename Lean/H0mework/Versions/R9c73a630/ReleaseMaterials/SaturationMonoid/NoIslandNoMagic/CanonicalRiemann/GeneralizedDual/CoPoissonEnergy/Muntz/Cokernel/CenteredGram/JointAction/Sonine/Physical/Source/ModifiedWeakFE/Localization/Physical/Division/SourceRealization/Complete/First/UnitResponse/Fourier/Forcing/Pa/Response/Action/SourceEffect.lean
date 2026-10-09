import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Fourier.Forcing.Pa.Response.Action.SourceEquation
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Class
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Correction
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Fourier
import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPhysicalRead

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Exact finite-time source update; both oriented forcing boundaries remain visible. -/
theorem comb_source_update {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) (time : ℝ) :
    let z := observation.coordinate / 2
    let q := (burnolPaCombApproximation n : BurnolL2)
    let r := (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let row := fun h => positiveMellinQuarterRightResolventCharacter z h •
      (r + burnolDirectRightResolventSignedBoundary z q h)
    burnolMultiplicativeDilation (-time / 2) (B : BurnolL2) =
      (1 / 2 : ℂ) • (row time + fourierL2 (row (-time))) := by
  intro z q r B row
  have right : 1 / 4 < z.re := by
    dsimp only [z]; rw [Complex.div_re]; norm_num; linarith
  have forward : burnolMultiplicativeDilation (-time / 2) r = row time := by
    have generated := eq_add_of_sub_eq (burnolDirectRightResolvent_sourceBoundary z right q time)
    change burnolMultiplicativeDilation (-time / 2) r =
      positiveMellinQuarterRightResolventCharacter z time •
        burnolDirectRightResolventSignedBoundary z q time +
      positiveMellinQuarterRightResolventCharacter z time • r at generated
    exact generated.trans (by dsimp only [row]; module)
  have backward : burnolMultiplicativeDilation (-time / 2) (fourierL2 r) =
      fourierL2 (row (-time)) := by
    have generated := congrArg fourierL2
      (eq_add_of_sub_eq (burnolDirectRightResolvent_sourceBoundary z right q (-time)))
    rw [fourierL2_burnolMultiplicativeDilation] at generated
    have sign : -(-(-time) / 2) = -time / 2 := by ring
    rw [sign] at generated
    change burnolMultiplicativeDilation (-time / 2) (fourierL2 r) = fourierL2
      (positiveMellinQuarterRightResolventCharacter z (-time) •
        burnolDirectRightResolventSignedBoundary z q (-time) +
        positiveMellinQuarterRightResolventCharacter z (-time) • r) at generated
    exact generated.trans (by
      dsimp only [row]
      apply congrArg fourierL2
      module)
  change burnolMultiplicativeDilation (-time / 2)
    ((1 / 2 : ℂ) • (r + fourierL2 r)) = _
  rw [map_smul, map_add, forward, backward]

/-- The original Bh acts on the original B, through the same full forcing rows. -/
theorem comb_physical_effect {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) (shift : ℝ) :
    let z := observation.coordinate / 2
    let q := (burnolPaCombApproximation n : BurnolL2)
    let r := (burnolPaCombPhysicalResponse observation nontrivial rightHalf n : BurnolL2)
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let row := fun h => positiveMellinQuarterRightResolventCharacter z h •
      (r + burnolDirectRightResolventSignedBoundary z q h)
    burnolPairedAmbientCompression shift B = (1 / 4 : ℂ) • burnolEvenAmbientProjection
      (row (-2 * shift) + fourierL2 (row (2 * shift)) +
        row (2 * shift) + fourierL2 (row (-2 * shift))) := by
  intro z q r B row
  have forward := comb_source_update observation nontrivial rightHalf n (-2 * shift)
  have backward := comb_source_update observation nontrivial rightHalf n (2 * shift)
  have negative : -(-2 * shift) / 2 = shift := by ring
  have positive : -(2 * shift) / 2 = -shift := by ring
  have negneg : -(-2 * shift) = 2 * shift := by ring
  rw [negative, negneg] at forward
  rw [positive, show -(2 * shift) = -2 * shift by ring] at backward
  change burnolMultiplicativeDilation shift (B : BurnolL2) =
    (1 / 2 : ℂ) • (row (-2 * shift) + fourierL2 (row (2 * shift))) at forward
  change burnolMultiplicativeDilation (-shift) (B : BurnolL2) =
    (1 / 2 : ℂ) • (row (2 * shift) + fourierL2 (row (-2 * shift))) at backward
  have action : burnolPairedAmbientCompression shift B = (1 / 2 : ℂ) •
      (burnolEvenAmbientProjection (burnolMultiplicativeDilation shift (B : BurnolL2)) +
        burnolEvenAmbientProjection (burnolMultiplicativeDilation (-shift) (B : BurnolL2))) := rfl
  rw [action, forward, backward]
  simp only [map_smul, map_add]
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
