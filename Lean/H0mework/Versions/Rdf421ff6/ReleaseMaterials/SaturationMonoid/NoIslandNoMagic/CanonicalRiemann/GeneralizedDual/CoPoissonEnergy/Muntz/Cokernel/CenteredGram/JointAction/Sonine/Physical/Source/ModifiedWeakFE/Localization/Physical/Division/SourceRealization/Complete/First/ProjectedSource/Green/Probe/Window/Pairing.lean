import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.Window.Recovery
import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.PhysicalPairing

/-! A free-probe window is an actual original-Pa test of the same projected head. -/

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

theorem secondWindowPhysical_kernel_pairing {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (h : ℝ)
    (probe : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    2 * inner ℂ (originalShiftedContactKernel observation nontrivial rightHalf h)
      (contactRestriction (sourceSecondWindow probe p)) =
        inner ℂ (burnolMultiplicativeDilation h W)
          (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (secondWindowPhysical probe p) : BurnolL2) := by
  intro one W
  let actual := secondWindowPhysical probe p
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  have inside : actual ∈ burnolCompactCoPoissonClosedRange := secondWindowPhysical_mem probe p
  have fInside : F actual ∈ burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside
  have same : burnolTateReciprocalL2 (burnolMobiusSourceL2 (F actual)) = sourceSecondWindow probe p := by
    rw [burnolMobiusSource_fourier actual inside, burnolTateReciprocalL2_involutive]
    exact secondWindowPhysical_source probe p
  have generated := originalShiftedContactKernel_physical_pairing
    observation nontrivial rightHalf h (F actual) fInside
  rw [same] at generated
  exact generated

theorem original_head_window_normalEquation {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) :
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
    let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
    let tested := secondWindowPhysical probe ⟨p, Submodule.starProjection_apply_mem _ _⟩
    inner ℂ B tested = inner ℂ p tested := by
  intro B p tested
  have generated := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_inner_eq_zero B tested
    (secondWindowPhysical_mem probe ⟨p, Submodule.starProjection_apply_mem _ _⟩)
  rw [inner_sub_left] at generated
  exact sub_eq_zero.mp generated

theorem original_zero_window_annihilation {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate)
    (p : burnolCompactCoPoissonClosedRange.toSubmodule) :
    inner ℂ (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier)
      (secondWindowPhysical probe p) = 0 :=
  (Submodule.mem_orthogonal' _ _).mp
    (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf).property _
      (secondWindowPhysical_mem probe p)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
