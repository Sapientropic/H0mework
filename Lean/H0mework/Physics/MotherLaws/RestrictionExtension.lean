import H0mework.Physics.MotherLaws.StreamCompletion
import Mathlib.Topology.TietzeExtension

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedRestrictions

open MotherStreamLaws Topology

noncomputable section

universe u

/-- A single source law restores the entire actual map on the closed
embedded carrier. The carrier may be empty and need not be compact. -/
theorem exists_law_on_closed_embedding {X : Type u} [TopologicalSpace X]
    (embedding : X → Stream) (closed : IsClosedEmbedding embedding) (actual : C(X, Stream)) :
    ∃ law : Law, ∀ input : X, eval law (embedding input) = actual input := by
  obtain ⟨extension, extension_eq⟩ := actual.exists_extension closed
  obtain ⟨law, generated, _⟩ := every_continuous_law extension
  refine ⟨law, fun input => ?_⟩
  rw [eval_eq, generated]
  exact congrArg (fun map : C(X, Stream) => map input) extension_eq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedRestrictions
