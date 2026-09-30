import H0mework.Versions.X.Fock.PrimeFieldJoint.ClockGraphDecoderConsumer
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.ContinuousInverse

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointDecoderCofinal

open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev image (bound : Nat) : Submodule ℂ SourceJointClockGraph.Carrier := (SourceJointFiniteDecoder.action bound).range

abbrev images (round : Nat) (future : Nat) : Submodule ℂ SourceJointClockGraph.Carrier :=
  image (inventoryBound (roundRuntime (round + future)))

theorem image_mono : Monotone image := by
  intro old fresh prior value present
  rcases present with ⟨source, rfl⟩
  exact ⟨SourceHistoryGrowth.normalizedInclusion prior source,
    SourceJointFiniteDecoder.action_normalized prior source⟩

theorem images_mono (round : Nat) : Monotone (images round) := by
  intro left right ordered
  exact image_mono (inventory_strictMono.monotone (Nat.add_le_add_left ordered round))

theorem action_closed_range : IsClosed (Set.range SourceJointClockGraph.action) := by
  have inverse : SourceJointClockGraph.action.HasLeftInverse :=
    ⟨SourceJointClockGraph.recover, SourceJointClockGraph.recover_action⟩
  exact inverse.isClosed_range

private theorem image_in_action (bound : Nat) : image bound ≤ SourceJointClockGraph.action.range := by
  rintro _ ⟨source, rfl⟩
  exact ⟨SourceJointFiniteDecoder.read bound source, rfl⟩

theorem whole_image (round : Nat) :
    (⨆ future : Nat, images round future).topologicalClosure = SourceJointClockGraph.action.range := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ (iSup_le fun future => image_in_action _) action_closed_range
  · let completed := (⨆ future : Nat, images round future).topologicalClosure
    have actualIncluded :
        (⨆ future : Nat, LinearMap.range (SourceGeneratedJointClockGraph.fieldRead
          (depth (roundRuntime (round + future))) (inventoryBound (roundRuntime (round + future))))) ≤
        completed.comap SourceJointClockGraph.action.toLinearMap := by
      apply iSup_le
      intro future
      rintro _ ⟨value, rfl⟩
      change SourceJointClockGraph.action (SourceGeneratedJointClockGraph.fieldRead _ _ value) ∈ completed
      apply (⨆ future : Nat, images round future).le_topologicalClosure
      apply (le_iSup (images round) future)
      refine ⟨Actor.currentPullback _ _ value, ?_⟩
      exact (SourceGeneratedJointFiniteDecoder.actor_action _ _ value).trans
        (SourceGeneratedJointClockGraph.original_time_square _ _ value)
    have closure := Submodule.topologicalClosure_minimal _ actualIncluded
      ((⨆ future : Nat, images round future).isClosed_topologicalClosure.preimage SourceJointClockGraph.action.continuous)
    rw [SourceGeneratedJointClockGraph.whole_graph_closure] at closure
    rintro _ ⟨value, rfl⟩
    exact closure (show value ∈ (⊤ : Submodule ℂ SourceJointClockGraph.Carrier) from trivial)

end
end SourceJointDecoderCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
