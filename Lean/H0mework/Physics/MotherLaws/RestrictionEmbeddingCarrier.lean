import H0mework.Physics.MotherLaws.RestrictionEmbeddingClosedGraph
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Logic.Equiv.Nat

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedEmbedding

open Set Topology TopologicalSpace
open scoped Topology
open MotherStreamLaws

noncomputable section

/-- Both complete coordinate streams are reindexed into the already fixed mother carrier. -/
def interleave : (Stream × Stream) ≃ₜ Stream :=
  (Homeomorph.sumArrowHomeomorphProdArrow (X := ℝ)).symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ : ℕ => ℝ) Equiv.natSumNatEquivNat)

theorem exists_closedEmbedding (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X] :
    ∃ embedding : X → Stream, IsClosedEmbedding embedding := by
  cases isEmpty_or_nonempty X with
  | inl empty =>
      let embedding : X → Stream := fun _ => 0
      have faithful : IsEmbedding embedding :=
        IsEmbedding.mk' embedding (fun x => isEmptyElim x) (fun x => isEmptyElim x)
      have emptyRange : Set.range embedding = ∅ := by
        ext y
        simp
      exact ⟨embedding, faithful, emptyRange ▸ isClosed_empty⟩
  | inr inhabited =>
      exact ⟨interleave ∘ graph X, interleave.isClosedEmbedding.comp (graph_isClosedEmbedding X)⟩

def embed (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X] : X → Stream :=
  Classical.choose (exists_closedEmbedding X)

theorem embed_isClosedEmbedding (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X] :
    IsClosedEmbedding (embed X) :=
  Classical.choose_spec (exists_closedEmbedding X)

/-- Complete recovery is the canonical homeomorphism onto the generated closed image. -/
def ontoRange (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X] :
    X ≃ₜ Set.range (embed X) :=
  (embed_isClosedEmbedding X).isEmbedding.toHomeomorph

theorem ontoRange_apply (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X] (x : X) :
    (ontoRange X x).val = embed X x := rfl

theorem recover_embed (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X] (x : X) :
    (ontoRange X).symm ⟨embed X x, ⟨x, rfl⟩⟩ = x :=
  (ontoRange X).symm_apply_apply x

theorem embed_recover (X : Type*) [MetricSpace X] [SeparableSpace X] [CompleteSpace X]
    (value : Set.range (embed X)) : embed X ((ontoRange X).symm value) = value.val :=
  congrArg Subtype.val ((ontoRange X).apply_symm_apply value)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedEmbedding
