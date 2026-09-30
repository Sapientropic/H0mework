import H0mework.Versions.X.Fock.CopyGraph.RecordedEvolutionObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCofinal

open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
noncomputable section

def image (depth : Nat) (index : Index depth) (bound : Nat) : Submodule ℂ SourceJointClockGraph.Carrier :=
  ((SourceCopyGraph.action depth index).comp (SourceJointFiniteDecoder.read bound)).range

abbrev images (depth : Nat) (index : Index depth) (round future : Nat) : Submodule ℂ SourceJointClockGraph.Carrier :=
  image depth index (inventoryBound (roundRuntime (round + future)))

theorem image_mono (depth : Nat) (index : Index depth) : Monotone (image depth index) := by
  intro old fresh prior value present
  rcases present with ⟨source, rfl⟩
  refine ⟨SourceHistoryGrowth.normalizedInclusion prior source, ?_⟩
  change SourceCopyGraph.action depth index (SourceJointFiniteDecoder.read fresh _) =
    SourceCopyGraph.action depth index (SourceJointFiniteDecoder.read old _)
  rw [SourceJointFiniteDecoder.read_source, SourceJointFiniteDecoder.read_source, SourceHistoryWord.normalized_word]

theorem images_mono (depth : Nat) (index : Index depth) (round : Nat) : Monotone (images depth index round) := by
  intro left right ordered
  exact image_mono depth index (inventory_strictMono.monotone (Nat.add_le_add_left ordered round))

theorem action_closed_range (depth : Nat) (index : Index depth) : IsClosed (Set.range (SourceCopyGraph.action depth index)) := by
  have inverse : (SourceCopyGraph.action depth index).HasLeftInverse :=
    ⟨SourceCopyGraph.recover depth index, SourceCopyGraph.recover_action depth index⟩
  exact inverse.isClosed_range

theorem image_in_action (depth : Nat) (index : Index depth) (bound : Nat) :
    image depth index bound ≤ (SourceCopyGraph.action depth index).range := by
  rintro _ ⟨source, rfl⟩
  exact ⟨SourceJointFiniteDecoder.read bound source, rfl⟩

theorem whole_image (sourceDepth : Nat) (index : Index sourceDepth) (round : Nat) :
    (⨆ future : Nat, images sourceDepth index round future).topologicalClosure =
      (SourceCopyGraph.action sourceDepth index).range := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (iSup_le fun future => image_in_action _ _ _)
      (action_closed_range sourceDepth index)
  · let completed := (⨆ future : Nat, images sourceDepth index round future).topologicalClosure
    have actualIncluded :
        (⨆ future : Nat, LinearMap.range (fieldRead
          (depth (roundRuntime (round + future))) (inventoryBound (roundRuntime (round + future))))) ≤
        completed.comap (SourceCopyGraph.action sourceDepth index).toLinearMap := by
      apply iSup_le
      intro future
      rintro _ ⟨value, rfl⟩
      change SourceCopyGraph.action sourceDepth index (fieldRead _ _ value) ∈ completed
      apply (⨆ future : Nat, images sourceDepth index round future).le_topologicalClosure
      apply (le_iSup (images sourceDepth index round) future)
      refine ⟨Actor.currentPullback _ _ value, ?_⟩
      change SourceCopyGraph.action sourceDepth index (SourceJointFiniteDecoder.read _ (Actor.currentPullback _ _ value)) = _
      rw [SourceJointFiniteDecoder.read_source]
      rfl
    have closure := Submodule.topologicalClosure_minimal _ actualIncluded
      ((⨆ future : Nat, images sourceDepth index round future).isClosed_topologicalClosure.preimage
        (SourceCopyGraph.action sourceDepth index).continuous)
    rw [SourceGeneratedJointClockGraph.whole_graph_closure] at closure
    rintro _ ⟨value, rfl⟩
    exact closure (show value ∈ (⊤ : Submodule ℂ SourceJointClockGraph.Carrier) from trivial)

end
end SourceCopyCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
