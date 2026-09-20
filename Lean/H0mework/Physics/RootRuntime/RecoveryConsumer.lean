import H0mework.Physics.RootRuntime.RecoveryMatter
import H0mework.Physics.RootRuntime.RuntimeConsumer

/-! One consumer joins the earlier source-generated stages to the current
Stage-10 closure and its actual successor. Stages 1--3 retain their roles as
contract formation and subordinate mathematics; no retired gate is promoted.
The earlier one-loop receipt retains its stated Weyl-only scalar inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Recovery

open SU7GravityGaugeMatterJointCredential SU7ExteriorMatterAnomalyRunning

noncomputable section

structure StageOneThroughTenClosure where
  private mk ::
  final : StageTenPhysicalRootClosure
  earlier : StageEightGravityGaugeMatterCredential Runtime.source.stageEight stageSix
  earlierGenerated : earlier = stageEight
  currentMatter : MatterRecovery Runtime.configuration earlier
  nextMatter : MatterRecovery Runtime.nextConfiguration earlier

def stageOneThroughTenClosure : StageOneThroughTenClosure := by
  have same : Runtime.nextConfiguration = Runtime.configuration :=
    (Stage9DEF.Runtime.configurationAt_eq_actual 10).trans Runtime.configuration_eq.symm
  exact
    { final := stageTenPhysicalRootClosure
      earlier := stageEight
      earlierGenerated := rfl
      currentMatter := currentMatter
      nextMatter := same ▸ currentMatter }

/-- The complete earlier receipt and actual matter readbacks are consumed
together with the same original ledger activation, prediction and next. -/
theorem stageOneThroughTenClosed :
    Nonempty StageOneThroughTenClosure ∧
    Nonempty SU7ExteriorMatterStageSevenComputationReceipt ∧
    MatterRecovery Runtime.configuration stageEight ∧
    MatterRecovery Runtime.nextConfiguration stageEight ∧
    Runtime.SameOccurrenceActivation ∧ Prediction.JointPrediction := by
  let closure := stageOneThroughTenClosure
  refine ⟨⟨closure⟩, ⟨closure.earlier.stageSeven⟩, ?_, ?_,
    closure.final.activation, closure.final.predictionLock⟩
  · rw [← closure.earlierGenerated]
    exact closure.currentMatter
  · rw [← closure.earlierGenerated]
    exact closure.nextMatter

end
end SaturationMonoid.PhysicsCore.Stage10.Recovery
