import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ExpandedGap
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalAction
import H0mework.Realization.ObservationActions.HilbertCore

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.Faithful

open CenteredGram.IntegralGraphJointAction
open scoped InnerProductSpace

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

private theorem frequency_gap_of_outside_zero (v : BurnolL2) (zero : O v = 0) :
    fourierL2 v ∈ locallyConstantFace (1/4) := by
  let S := evenBurnolClosedFace burnolUnscaledCommonGapRadius
  have sum := Submodule.starProjection_add_starProjection_orthogonal (K := S.toSubmodule) v
  change S.toSubmoduleᗮ.starProjection v = 0 at zero
  rw [zero, add_zero] at sum
  have physical : v ∈ S := S.toSubmodule.starProjection_eq_self_iff.mp sum
  exact (fourierL2_mem_evenBurnolClosedFace physical).1.1

private theorem zero_of_future_zero (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (silent : ∀ n : ℕ, O ((R c ^ (n+1)) v) = 0) : v = 0 := by
  apply ExpandedGap.zero_of_all_inward_frequency_gap v
  intro h positive
  exact frequency_gap_of_outside_zero _
    (DilationFromPowers.observed_inward_zero O c v silent h positive)

/-- The literal original successor slots separate all ambient raw fields. -/
theorem eq_of_same_successors (c : BurnolCompletedMellinCoordinate) {x y : BurnolL2}
    (same : ∀ n : ℕ, O ((R c ^ (n+1)) x) = O ((R c ^ (n+1)) y)) : x = y := by
  apply sub_eq_zero.mp
  apply zero_of_future_zero c
  intro n
  simpa only [map_sub, sub_eq_zero] using same n

namespace Observed

open SourceGeneratedActionObservationHistory

/-- The existing complete cofinal observer has no inverse-fibre ambiguity on the full raw carrier. -/
theorem sourceMap_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (sourceMap (R c).toLinearMap (O).toLinearMap) := by
  intro x y same
  apply eq_of_same_successors c
  intro n
  have read := (source_fibre_iff (R c).toLinearMap (O).toLinearMap x y).mp same (n+1)
  rwa [← ContinuousLinearMap.toLinearMap_pow] at read

/-- Consume the existing Hilbert inverse on this same original source and outside observer. -/
theorem recover_source (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    Hilbert.recover (R c) O (projection (R c).toLinearMap (O).toLinearMap v) = v := by
  have residualZero : Hilbert.residual (R c) O v = 0 := by
    apply zero_of_future_zero c
    intro n
    have silent := Hilbert.residual_invisible (R c) O v (n+1)
    rwa [← ContinuousLinearMap.toLinearMap_pow] at silent
  simpa only [residualZero, zero_add] using Hilbert.recover_residual (R c) O v

end Observed

end OriginalRSourceJointContact.OutsideHistory.Faithful
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
