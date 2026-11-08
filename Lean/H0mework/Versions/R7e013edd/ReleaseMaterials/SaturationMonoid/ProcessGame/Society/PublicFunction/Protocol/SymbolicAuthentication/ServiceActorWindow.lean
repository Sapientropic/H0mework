import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorEnvelope

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorWindow
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
abbrev width := SourceClockTermination.width model start
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law

-- The budget and communication gates concern the same actual window. No worker,
-- raw admission, service receipt, completed inventory or decision is supplied.
def Available (blocks : Nat) (past : JointResponse.Stages model) : Prop :=
  ∀ block < blocks,
    ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past ((block + 1) * width model start)) →
    (ServiceActorEnvelope.affected model start vocabulary encoding law past
      (block * width model start) (width model start)).card <
      (ServiceActorEnvelope.candidates model start vocabulary encoding law past (block * width model start)).card ∧
    ∀ offset < width model start,
      ¬ JointResponse.Clear model start vocabulary encoding law
        (atCut model start vocabulary encoding law past (block * width model start + offset)) →
      UnifiedResponse.Clear model start vocabulary encoding law
        (atCut model start vocabulary encoding law past (block * width model start + offset)) ∧
      JointResponse.queueClear model start
        (atCut model start vocabulary encoding law past (block * width model start + offset)) = true

theorem the_actual_identity_budget_generates_the_original_persistent_service_window
    (blocks : Nat) (past : JointResponse.Stages model)
    (available : Available model start vocabulary encoding law blocks past) :
    SourceServiceWindow.Persistent model start vocabulary encoding law blocks past := by
  intro block inside unfinished
  obtain ⟨surplus,communication⟩ := available block inside unfinished
  obtain ⟨survivor,generated⟩ := ServiceActorEnvelope.source_identity_surplus_forces_the_retained_branch
    model start vocabulary encoding law past (block * width model start) (width model start) surplus
  refine ⟨survivor.worker,?_⟩
  intro offset bounded openCut
  exact ⟨(communication offset bounded openCut).1,(communication offset bounded openCut).2,
    ServiceActorEnvelope.the_generated_survivor_has_an_actual_offer_at_every_unfinished_cut
      model start vocabulary encoding law past _ _ survivor offset bounded openCut⟩

theorem source_generated_identity_availability_forces_the_original_joint_completion
    (past : JointResponse.Stages model) (delay : Nat) (positive : 0 < width model start)
    (reserve : SourceClockTermination.deadline model start past * CommunicationWorkBudget.slotAllowance model start <
      JointResponse.fuel model start past)
    (available : Available model start vocabulary encoding law (SourceClockTermination.blocks model start past) past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (SourceClockTermination.deadline model start past) past).stages) :
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete ∧
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages.length ≤
      past.length + SourceClockTermination.deadline model start past * CommunicationWorkBudget.slotAllowance model start :=
  SourceClockTermination.the_original_source_sized_producer_has_the_generated_physical_deadline model start vocabulary encoding law
    past delay positive reserve
    (the_actual_identity_budget_generates_the_original_persistent_service_window model start vocabulary encoding law _ past available) compliant

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorWindow
