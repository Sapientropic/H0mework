import H0mework.Physics.MotherLaws.PointwiseCompletion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws

noncomputable section

universe u

/-- The entire actual map is formed by one law on its faithful input image.
The extension and target occur only in this coverage proof. -/
theorem every_restriction {X : Type u} (encode : X → MotherStreamLaws.Stream)
    (faithful : Function.Injective encode) (actual : X → MotherStreamLaws.Stream) :
    ∃ law : Law, ∀ input : X, eval law (encode input) = actual input := by
  obtain ⟨law, generated, _⟩ := every_law (Function.extend encode actual (fun _ => 0))
  refine ⟨law, fun input => ?_⟩
  rw [generated]
  exact faithful.extend_apply actual (fun _ => 0) input

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws
