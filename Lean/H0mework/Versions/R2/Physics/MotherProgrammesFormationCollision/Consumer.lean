import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Consumer
import H0mework.Physics.MotherProgrammesFormationCollision.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointContactConsumer

open JointContactSource ContactCollision CollisionHistory
open StageNineEnrichedProofFreeSource StageNineCClassicalWorldAcceptance Stage9C.Revision

noncomputable section

/-- The finite collision history realizes the source keep/trace algebra. Its
calculation depth is not identified with the original macro-runtime visit. -/
theorem original_keep_trace_history (r : ℝ) (depth : ℕ) :
    r * Complex.normSq (formed depth 0) =
      (Runtime.source.continuousKeep : ℝ → ℝ)^[depth] r ∧
    r * emittedEnergy (formed depth) = r - (Runtime.source.continuousKeep : ℝ → ℝ)^[depth] r ∧
    (currentAt a b 1 depth).next a b = currentAt a b 1 (depth + 1) ∧
    (∀ index : Fin depth,
      formed (depth + 1) index.castSucc.succ = formed depth index.succ) := by
  have generated : r * Complex.normSq (formed depth 0) =
      (Runtime.source.continuousKeep : ℝ → ℝ)^[depth] r := by
    have result := generated_recurrence StageEightProofFreeSource.canonicalSource r depth
    rw [JointContactSource.original_formed] at result
    exact result
  refine ⟨generated, ?_, currentAt_next a b 1 depth, ?_⟩
  · have balance := signed_residual_balance r depth
    rw [generated] at balance
    linarith
  · intro index
    exact step_old_emitted a b (formed depth) index

theorem same_operator_generates_original_parameters :
    Runtime.source.legacy.sigma = Complex.normSq b ∧
    Runtime.source.continuousContactResidual = 2 * Complex.arg (primitive : ℂ) ∧
    contrastPhase ^ 2 = (primitive : ℂ) := by
  have fraction := source_fraction StageEightProofFreeSource.canonicalSource
  rw [JointContactSource.original_formed] at fraction
  refine ⟨fraction, ?_, phase_same_origin.2⟩
  change positiveSmoothUnifiedSource.continuousContactResidual = generatedResidual
  rw [residual_normalForm]
  rfl

theorem joint_source_consumed :
    ClassicalWorldAcceptance (JointContactSource.formedSource StageEightProofFreeSource.canonicalSource)
      Runtime.configuration ∧
    Runtime.SameOccurrenceActivation ∧
    Runtime.tick.next.node.erase = ⟨MaterialN, SpinPair.livingRoot.generatedNextCurrentAt Runtime.visit⟩ := by
  apply FormationConsumer.candidate_contact_formation_consumed
  · have same : JointContactSource.formedSource StageEightProofFreeSource.canonicalSource = Runtime.source :=
      JointContactSource.original_formed
    exact congrArg SmoothUnifiedSource.stageEight same
  · exact source_primitive _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointContactConsumer
