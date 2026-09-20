import H0mework.Physics.MotherSource.Consumer
import H0mework.Physics.MotherProgrammesFormation.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FormationConsumer

open ContactSource ContactFlow StageNineEnrichedProofFreeSource
open StageNineCClassicalWorldAcceptance Stage9C.Revision

noncomputable section

/-- Conditional consumption of the newly formed source. The parent equality
belongs to this local interface and is not a complete-reality admission rule. -/
theorem candidate_contact_formation_consumed (candidate : SmoothUnifiedSource)
    (parent : candidate.stageEight = Runtime.source.stageEight)
    (law : Primitive (normalizedFlow candidate)) :
    ClassicalWorldAcceptance candidate Runtime.configuration ∧
    Runtime.SameOccurrenceActivation ∧
    Runtime.tick.next.node.erase = ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  have source : candidate = Runtime.source := by
    rw [source_formed candidate law, parent]
    exact original_formed
  refine ⟨?_, Runtime.sameOccurrenceActivation, ?_⟩
  · rw [source]
    exact Recovery.stageOneThroughTenClosure.final.classical
  · rw [← Runtime.sameOccurrenceActivation.answerNext]
    exact Runtime.sameOccurrenceActivation.macroAnswerNext

theorem original_contact_formation_consumed :
    Primitive (normalizedFlow Runtime.source) ∧
    ClassicalWorldAcceptance (formedSource Runtime.source.stageEight) Runtime.configuration ∧
    Runtime.SameOccurrenceActivation ∧
    Runtime.tick.next.node.erase = ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  exact ⟨original_primitive,
    candidate_contact_formation_consumed (formedSource Runtime.source.stageEight) rfl (formed_primitive _)⟩

theorem original_contact_physical_clock (time : ℝ) :
    (generatedUnitaryFlow Runtime.source).evolve time = generatedFlow.evolve time := by
  have formed := congrArg (fun flow => flow.evolve time)
    (primitive_flow (normalizedFlow Runtime.source) original_primitive)
  convert formed using 1
  change Circle.exp (Runtime.source.continuousContactRate * time) =
    Circle.exp (Runtime.source.continuousContactRate * (time / (2 * Runtime.source.legacy.sigma)))
  have sigma : Runtime.source.legacy.sigma = (1 / 2 : ℝ) := by
    rw [Runtime.source_eq]
    norm_num [StageNineEnrichedProofFreeSource.SmoothUnifiedSource.legacy,
      SmoothUnifiedSource.forget, positiveSmoothUnifiedSource, StageEightProofFreeSource.canonicalSource,
      StageEightProofFreeSource.Source.toPhysicalSource, ProofFreeRicherAnholonomicSource.Source.sigma]
  rw [sigma]
  norm_num

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FormationConsumer
