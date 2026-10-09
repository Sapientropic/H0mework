import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Fourier.Forcing.Pa.Response.Action.SourceEffect
import H0mework.Realization.ObservationActions.HilbertSymmetric

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedActionObservationHistory
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Both original observers are fixed before the Model is formed. -/
def originalObserver {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    BurnolPaAmbientCarrier →L[ℂ] ℂ × ℂ :=
  let coordinate := burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf
  let K := burnolCompletedMellinRieszVector coordinate
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  (burnolCompletedMellinEvaluator coordinate).prod (innerSL ℂ (F.symm K))

/-- Computed from the original q0 and both signed resolvent boundaries. -/
def sourceNext {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) : BurnolPaAmbientCarrier :=
  let z := observation.coordinate / 2
  let q := (burnolPaCombApproximation 0 : BurnolL2)
  let r := (burnolPaCombPhysicalResponse observation nontrivial rightHalf 0 : BurnolL2)
  let row := fun h => positiveMellinQuarterRightResolventCharacter z h •
    (r + burnolDirectRightResolventSignedBoundary z q h)
  (1 / 4 : ℂ) • burnolEvenAmbientProjection
    (row (-2 * shift) + fourierL2 (row (2 * shift)) +
      row (2 * shift) + fourierL2 (row (-2 * shift)))

theorem sourceNext_actual {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) :
    sourceNext observation nontrivial rightHalf shift = burnolPairedAmbientCompression shift
      (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0) :=
  (comb_physical_effect observation nontrivial rightHalf 0 shift).symm

theorem sourceNext_model {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) :
    let A := burnolPairedAmbientCompression shift
    let R := originalObserver observation rightHalf
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    modelAction A.toLinearMap R.toLinearMap
      (projection A.toLinearMap R.toLinearMap B) =
      projection A.toLinearMap R.toLinearMap (sourceNext observation nontrivial rightHalf shift) := by
  intro A R B
  exact (modelAction_source A.toLinearMap R.toLinearMap B).trans
    (congrArg (projection A.toLinearMap R.toLinearMap)
      (sourceNext_actual observation nontrivial rightHalf shift).symm)

/-- Recovery and the full future-invisible residual follow the same original Bh. -/
theorem sourceNext_full {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) :
    let A := burnolPairedAmbientCompression shift
    let R := originalObserver observation rightHalf
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let V := sourceNext observation nontrivial rightHalf shift
    Hilbert.recover A R (projection A.toLinearMap R.toLinearMap V) =
      A (Hilbert.recover A R (projection A.toLinearMap R.toLinearMap B)) ∧
    Hilbert.residual A R V = A (Hilbert.residual A R B) ∧
    Hilbert.residual A R V + Hilbert.recover A R
      (projection A.toLinearMap R.toLinearMap V) = V := by
  intro A R B V
  have symmetric : A.toLinearMap.IsSymmetric := burnolPairedAmbientCompression_symmetric shift
  have source := sourceNext_model observation nontrivial rightHalf shift
  refine ⟨?_, ?_, Hilbert.recover_residual A R V⟩
  · exact (congrArg (Hilbert.recover A R) source.symm).trans
      (Hilbert.recover_symmetric_action A R symmetric _)
  · change Hilbert.residual A R (sourceNext observation nontrivial rightHalf shift) = _
    rw [sourceNext_actual]
    exact Hilbert.residual_symmetric_action A R symmetric B

theorem sourceNext_all_future {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) (stage : Nat) :
    let A := burnolPairedAmbientCompression shift
    let R := originalObserver observation rightHalf
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let V := sourceNext observation nontrivial rightHalf shift
    R ((A.toLinearMap ^ stage)
      (Hilbert.recover A R (projection A.toLinearMap R.toLinearMap V))) =
      R ((A.toLinearMap ^ (stage + 1)) B) := by
  intro A R B V
  calc
    _ = R ((A.toLinearMap ^ stage) V) := Hilbert.recover_complete_history A R V stage
    _ = R ((A.toLinearMap ^ stage) (A B)) :=
      congrArg (fun value => R ((A.toLinearMap ^ stage) value))
        (sourceNext_actual observation nontrivial rightHalf shift)
    _ = _ := by rw [pow_succ]; rfl

theorem actual_observer_inventory {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re) (value : BurnolPaAmbientCarrier) :
    let coordinate := burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf
    let K := burnolCompletedMellinRieszVector coordinate
    let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    originalObserver observation rightHalf value = (inner ℂ K value, inner ℂ (F.symm K) value) := by
  intro coordinate K F
  apply Prod.ext
  · exact (burnolCompletedMellinRieszVector_readback coordinate value).symm
  · rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
