import H0mework.Versions.R2.Physics.MotherLaws.JointSourceInput
import H0mework.Versions.R2.Physics.MotherLaws.PointwiseCompletion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointSourceLaws

open StageNineEnrichedProofFreeSource StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Reduction MotherStreamLaws MotherClosedRestrictions

noncomputable section

/-- One completed law consumes every original source/state/center input.
The complete key is retained even when distinct parameters have the same written field. -/
theorem all_sources_writer : ∃ law : MotherPointwiseLaws.Law,
    (∀ (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source) (center : BasePoint),
      let input : Input := ⟨source, state, center⟩
      let after : Input := ⟨source, p286CartanStateNext center state, center⟩
      let value := MotherPointwiseLaws.eval law (MotherStreamFormation.read (encode input))
      value = pairStream (samples input) (samples after) ∧
      recoverSamples (firstStream value) = input ∧
      recoverSamples (lastStream value) = after ∧
      readSource (firstStream (firstStream value)) = source ∧
      (recoverSamples (lastStream value)).2.1.current =
        p286CartanNext source state.current state.smooth state.nondegenerate center ∧
      actualRelativeAction (readSource (firstStream (firstStream value)))
          (recoverSamples (firstStream value)).2.1.current
          (recoverSamples (lastStream value)).2.1.current =
        actualRelativeAction source state.current (p286CartanStateNext center state).current) ∧
    Function.Injective (fun input : Input =>
      MotherPointwiseLaws.eval law (MotherStreamFormation.read (encode input))) := by
  let target (input : Input) : Stream := pairStream (samples input)
    (samples ⟨input.1, p286CartanStateNext input.2.2 input.2.1, input.2.2⟩)
  obtain ⟨law, generated, _⟩ := MotherPointwiseLaws.every_law
    (Function.extend samples target (fun _ => 0))
  have evaluated (input : Input) :
      MotherPointwiseLaws.eval law (MotherStreamFormation.read (encode input)) = target input := by
    rw [read_encode, generated]
    exact samples_injective.extend_apply target (fun _ => 0) input
  refine ⟨law, ?_, ?_⟩
  · intro source state center
    dsimp only
    rw [evaluated]
    have before : recoverSamples (firstStream (target ⟨source, state, center⟩)) =
        (⟨source, state, center⟩ : Input) := by
      dsimp only [target]
      rw [first_pair, recover_samples]
    have after : recoverSamples (lastStream (target ⟨source, state, center⟩)) =
        (⟨source, p286CartanStateNext center state, center⟩ : Input) := by
      dsimp only [target]
      rw [last_pair, recover_samples]
    have restoredSource : readSource (firstStream (firstStream (target ⟨source, state, center⟩))) =
        source := by
      dsimp only [target]
      rw [first_pair, samples, first_pair, source_recovered]
    exact ⟨rfl, before, after, restoredSource, by rw [after]; rfl,
      by rw [restoredSource, before, after]⟩
  · intro first last same
    apply samples_injective
    have firstRead (input : Input) : firstStream
        (MotherPointwiseLaws.eval law (MotherStreamFormation.read (encode input))) = samples input := by
      rw [evaluated]
      dsimp only [target]
      rw [first_pair]
    exact (firstRead first).symm.trans ((congrArg firstStream same).trans (firstRead last))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointSourceLaws
