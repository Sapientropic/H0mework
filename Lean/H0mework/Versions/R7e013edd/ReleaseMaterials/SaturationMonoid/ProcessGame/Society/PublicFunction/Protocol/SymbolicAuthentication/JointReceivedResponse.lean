import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedStatementAuthentication

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedResponse

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
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
  (observedAt : Nat)

abbrev Stages := LocalJointResponse.Stages model
abbrev fuel := LocalJointResponse.fuel model start
abbrev protocol (past : Stages model) := ReceivedStatementAuthentication.protocol vocabulary encoding law start (past.map Prod.fst) observedAt
  (ReceivedStatementAuthentication.remembered start past observedAt)
abbrev row (past : Stages model) := StageTrace.material (EventHistory.execute start past)
  (protocol model start vocabulary encoding law observedAt past) (OriginQueue.environment start)

def responsesClosed (past : Stages model) : Bool :=
  (List.finRange model.source.code.sites).all fun site => decide
    (ReceivedStatementAuthentication.work vocabulary encoding law start (past.map Prod.fst) observedAt
      (ReceivedStatementAuthentication.remembered start past observedAt site) site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = [])

def Clear (past : Stages model) : Prop :=
  LocalJointResponse.Clear model start vocabulary encoding law past ∧
    responsesClosed model start vocabulary encoding law observedAt past = true
instance (past : Stages model) : Decidable (Clear model start vocabulary encoding law observedAt past) := by
  unfold Clear; infer_instance

theorem completion_has_no_unprocessed_locally_supported_response (past : Stages model)
    (closed : responsesClosed model start vocabulary encoding law observedAt past = true) (site : Fin model.source.code.sites) :
    ReceivedStatementAuthentication.work vocabulary encoding law start (past.map Prod.fst) observedAt
      (ReceivedStatementAuthentication.remembered start past observedAt site) site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = [] :=
  of_decide_eq_true ((List.all_eq_true.mp closed) site (List.mem_finRange site))

inductive Action (observedAt : Nat) (past : Stages model) where
  | inherited (action : LocalJointResponse.Action model start vocabulary encoding law past)
  | received (live : 0 < fuel model start past)

inductive Kind where
  | inherited (kind : LocalJointResponse.Kind)
  | received
  deriving DecidableEq

def kind {past : Stages model} : Action model start vocabulary encoding law observedAt past → Kind
  | .inherited action => .inherited (LocalJointResponse.kind model start vocabulary encoding law action)
  | .received _ => .received

def after (past : Stages model) : Action model start vocabulary encoding law observedAt past → Stages model
  | .inherited action => LocalJointResponse.after model start vocabulary encoding law past action
  | .received _ => past ++ [(protocol model start vocabulary encoding law observedAt past, OriginQueue.environment start)]

inductive Step (past : Stages model) where
  | clear (covered : Clear model start vocabulary encoding law observedAt past)
  | exhausted (empty : fuel model start past = 0)
  | advance (action : Action model start vocabulary encoding law observedAt past)

-- Original duties, claims and queue remain completion gates. A single local
-- response returns to them immediately instead of consuming a separate horizon.
def step (past : Stages model) : Step model start vocabulary encoding law observedAt past :=
  if covered : Clear model start vocabulary encoding law observedAt past then .clear covered
  else if live : 0 < fuel model start past then
    if (StageTrace.activation (row model start vocabulary encoding law observedAt past)).isSome &&
        !(row model start vocabulary encoding law observedAt past).submitted.isEmpty then .advance (.received live)
    else match LocalJointResponse.step model start vocabulary encoding law past with
      | .advance action => .advance (.inherited action)
      | .clear _ => .advance (.received live)
      | .exhausted _ => .advance (.received live)
  else .exhausted (by omega)

theorem every_action_retains_the_whole_actual_prefix (past : Stages model)
    (action : Action model start vocabulary encoding law observedAt past) :
    past <+: after model start vocabulary encoding law observedAt past action := by
  cases action with
  | inherited action => exact LocalJointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action
  | received live => exact List.prefix_append _ _

theorem every_action_spends_actual_fuel (past : Stages model)
    (action : Action model start vocabulary encoding law observedAt past) :
    fuel model start (after model start vocabulary encoding law observedAt past action) < fuel model start past := by
  cases action with
  | inherited action => exact LocalJointResponse.every_action_spends_actual_fuel model start vocabulary encoding law past action
  | received live =>
    change fuel model start (past ++ [_]) < _
    simp only [fuel, LocalJointResponse.fuel, UnifiedResponse.fuel_after_actual_extension, List.length_singleton]
    change 0 < UnifiedResponse.fuel model start past at live
    omega

theorem an_owned_received_action_uses_only_its_actual_local_record
    (past : Stages model) (site : Fin model.source.code.sites)
    (owned : StageTrace.activation (row model start vocabulary encoding law observedAt past) = some site) :
    (row model start vocabulary encoding law observedAt past).submitted =
      ReceivedStatementAuthentication.work vocabulary encoding law start (past.map Prod.fst) observedAt
      (ReceivedStatementAuthentication.remembered start past observedAt site) site
        ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) :=
  ReceivedStatementAuthentication.an_owned_activation_submits_the_locally_authenticated_word
    vocabulary encoding law start past observedAt (OriginQueue.environment start) site owned

theorem an_owned_nonempty_response_has_its_actual_paid_receipt
    (past : Stages model) (site : Fin model.source.code.sites)
    (owned : StageTrace.activation (row model start vocabulary encoding law observedAt past) = some site)
    (submitted : (row model start vocabulary encoding law observedAt past).submitted ≠ []) :
    ∃ body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (past.map Prod.fst) observedAt
      (ReceivedStatementAuthentication.remembered start past observedAt site) site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start past site past.length).receipts,
        receipt.statement = body ∧
        RequestReadback.localRead (code := model.source.code) ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) = some body.request ∧
        body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start past)).current := by
  rw [an_owned_received_action_uses_only_its_actual_local_record model start vocabulary encoding law observedAt past site owned] at submitted
  exact ReceivedStatementAuthentication.nonempty_work_has_actual_paid_communication_support vocabulary encoding law start past observedAt site submitted

theorem the_local_response_policy_is_installed_in_the_actual_source
    (past : Stages model) (site : Fin model.source.code.sites)
    (owned : StageTrace.activation (row model start vocabulary encoding law observedAt past) = some site) :
    ((EventHistory.execute start past).after (protocol model start vocabulary encoding law observedAt past)
      (OriginQueue.environment start)).source.feedbackPolicy (EventHistory.execute start past).cut =
      some (ReceivedStatementAuthentication.policy vocabulary encoding law start (past.map Prod.fst) observedAt
        (ReceivedStatementAuthentication.remembered start past observedAt)) :=
  StageTrace.the_live_work_policy_is_installed_in_the_actual_source _ _ _
    (StageTrace.an_owned_activation_submits_its_selected_work _ _ _ site owned).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedResponse
