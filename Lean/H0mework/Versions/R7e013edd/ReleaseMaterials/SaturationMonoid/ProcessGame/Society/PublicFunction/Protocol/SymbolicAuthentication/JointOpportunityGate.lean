import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunity

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointOpportunityGate
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
  (past : JointResponse.Stages model)

structure Attempt where
  private mk ::
  action : JointResponse.Action model start vocabulary encoding law past
  selected : JointResponse.step model start vocabulary encoding law past = .advance action
  kind : JointResponse.kind model start vocabulary encoding law action = .withdrawal
  native : NativeOpportunity.Attempt model start past
  actual : NativeOpportunity.full model start past native.ready = JointResponse.after model start vocabulary encoding law past action

def probe : Option (Attempt model start vocabulary encoding law past) :=
  match observed : JointResponse.step model start vocabulary encoding law past with
  | .advance (.withdrawal ready accepted selected) =>
    match candidate : NativeOpportunity.probe model start past with
    | none => none
    | some native =>
      have same : native.ready = ready := NativeReview.Plan.paid.inj (native.selected.symm.trans selected)
      some ⟨.withdrawal ready accepted selected, observed, rfl, native, by cases same; rfl⟩
  | _ => none

abbrev full (answer : Attempt model start vocabulary encoding law past) :=
  NativeOpportunity.full model start past answer.native.ready

theorem every_generated_opportunity_is_the_actual_original_joint_successor
    (answer : Attempt model start vocabulary encoding law past) :
    JointResponse.step model start vocabulary encoding law past = .advance answer.action ∧
    JointResponse.kind model start vocabulary encoding law answer.action = .withdrawal ∧
    full model start vocabulary encoding law past answer = JointResponse.after model start vocabulary encoding law past answer.action :=
  ⟨answer.selected, answer.kind, answer.actual⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointOpportunityGate
