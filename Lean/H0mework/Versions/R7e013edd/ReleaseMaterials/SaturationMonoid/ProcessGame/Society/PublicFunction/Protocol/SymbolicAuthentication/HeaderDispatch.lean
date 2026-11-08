import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderQuorum
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveDynamicCommandDomain

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderDispatch
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
  (law : StageReception.Law model.source.code) (delay : Nat)

abbrev State := LocalCommandRun.State model start
abbrev row (state : State model start) (input : LocalCommandSource.Input) :=
  (LocalCommandSource.observe model (state.current model start) input).row model
abbrev observed (state : State model start) (receiver : Fin model.source.code.sites) :=
  HeaderReception.run vocabulary law start state.stages receiver state.stages.length
def seen (state : State model start) (receiver : Fin model.source.code.sites) :=
  ((observed model start vocabulary law state receiver).receipts.map
    fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))

-- Candidates are predictions of the original local selector, never supplied wires.
def isDelivery (input : LocalCommandSource.Input) : Bool := match input with
  | .event index => match model.source.code.eventAlphabet[index]? with | some (.deliver _) => true | _ => false
  | _ => false
def isSend (input : LocalCommandSource.Input) : Bool := match input with
  | .event index => match model.source.code.eventAlphabet[index]? with | some (.send _ _) => true | _ => false
  | _ => false
def deliveryTest (state : State model start) (input : LocalCommandSource.Input) : Bool :=
  let candidate := row model start state input
  (HeaderTransport.wires vocabulary start state.stages).any fun wire =>
    decide (HeaderReception.check vocabulary law start state.stages wire.recipient
      candidate (seen model start vocabulary law state wire.recipient) wire = .accepted wire)
def delivery (state : State model start) (input : LocalCommandSource.Input) : Bool :=
  if isDelivery model input then deliveryTest model start vocabulary law state input else false
def sendingTest (state : State model start) (input : LocalCommandSource.Input) : Bool :=
  match HeaderTransport.issue vocabulary (StageTrace.records start state.stages) (row model start state input) with
  | none => false
  | some wire => decide ((wire.ballot.cut,wire.ballot.position) ∉
      seen model start vocabulary law state wire.recipient)
def sending (state : State model start) (input : LocalCommandSource.Input) : Bool :=
  if isSend model input then sendingTest model start vocabulary law state input else false

def offers (state : State model start) : List LocalCommandSource.Input :=
  let menu := DynamicCommandSource.menu model start delay state
  menu.filter (delivery model start vocabulary law state) ++
    menu.filter (sending model start vocabulary law state) ++ menu
def choose (state : State model start) : LocalCommandSource.Input :=
  let menu := DynamicCommandSource.menu model start delay state
  ((menu.find? (delivery model start vocabulary law state)).orElse fun _ =>
    (menu.find? (sending model start vocabulary law state)).orElse fun _ => menu.head?).getD .idle

theorem choose_is_the_first_offer (state : State model start) :
    choose model start vocabulary law delay state = (offers model start vocabulary law delay state).headD .idle := by
  simp [choose,offers,List.headD_eq_head?_getD,List.head?_append]

theorem every_offer_is_in_the_actual_dynamic_domain
    (state : State model start) (input : LocalCommandSource.Input)
    (inside : input ∈ offers model start vocabulary law delay state) :
    input ∈ DynamicCommandSource.menu model start delay state := by
  simp only [offers,List.mem_append] at inside
  rcases inside with (first | second) | third
  · exact (List.mem_filter.mp first).1
  · exact (List.mem_filter.mp second).1
  · exact third

theorem every_choice_is_in_the_original_source_menu (state : State model start) :
    choose model start vocabulary law delay state ∈ CommandWindowSource.menu model := by
  cases actual : offers model start vocabulary law delay state with
  | nil => simp only [choose_is_the_first_offer,actual,List.headD_nil]; exact List.mem_cons_self
  | cons input rest =>
    have inside : input ∈ offers model start vocabulary law delay state := by rw [actual]; exact List.mem_cons_self
    simpa only [choose_is_the_first_offer,actual,List.headD_cons] using
      (List.mem_filter.mp (every_offer_is_in_the_actual_dynamic_domain model start vocabulary law delay state input inside)).1

theorem positive_actual_fuel_admits_the_generated_choice
    (state : State model start) (live : 0 < (EventStep.seed (state.current model start)).remaining) :
    choose model start vocabulary law delay state ∈ DynamicCommandSource.menu model start delay state := by
  have menu := LiveDynamicCommandDomain.positive_actual_fuel_generates_a_nonempty_dynamic_domain model start delay state live
  have nonempty : offers model start vocabulary law delay state ≠ [] := by
    intro empty
    have count := congrArg List.length empty
    simp only [offers,List.length_append,List.length_nil] at count
    have zero : (DynamicCommandSource.menu model start delay state).length = 0 := by omega
    exact menu (List.eq_nil_of_length_eq_zero zero)
  exact every_offer_is_in_the_actual_dynamic_domain model start vocabulary law delay state _
    (by cases actual : offers model start vocabulary law delay state with
        | nil => exact False.elim (nonempty actual)
        | cons input rest => simp only [choose_is_the_first_offer,actual,List.headD_cons]; exact List.mem_cons_self)

theorem every_delivery_offer_keeps_its_actual_paid_source_and_acceptance
    (state : State model start) (input : LocalCommandSource.Input)
    (accepted : delivery model start vocabulary law state input = true) :
    ∃ wire ∈ HeaderTransport.wires vocabulary start state.stages,
      HeaderReception.check vocabulary law start state.stages wire.recipient
        (row model start state input) (seen model start vocabulary law state wire.recipient) wire = .accepted wire := by
  unfold delivery at accepted
  split at accepted <;> try contradiction
  obtain ⟨wire,member,checked⟩ := List.any_eq_true.mp accepted
  exact ⟨wire,member,of_decide_eq_true checked⟩

theorem every_send_offer_is_a_new_owned_packet_with_a_prior_paid_origin
    (state : State model start) (input : LocalCommandSource.Input)
    (selected : sending model start vocabulary law state input = true) :
    ∃ wire, HeaderTransport.issue vocabulary (StageTrace.records start state.stages)
      (row model start state input) = some wire ∧
      (wire.ballot.cut,wire.ballot.position) ∉ seen model start vocabulary law state wire.recipient ∧
      ∃ sender recipient, HeaderTransport.outgoing (row model start state input) = some (sender,recipient) ∧
        ∃ origin ∈ StageTrace.records start state.stages, wire.ballot ∈ HeaderTransport.ballots vocabulary origin := by
  unfold sending at selected
  split at selected <;> try contradiction
  unfold sendingTest at selected
  split at selected <;> try contradiction
  rename_i wire made
  obtain ⟨sender,recipient,packet,body,origin,owned,_,_,_,_,_,prior,paid,_,_,_,same⟩ :=
    HeaderTransport.issue_has_actual_packet_and_prior_owned_item vocabulary _ (row model start state input) wire made
  refine ⟨wire,made,of_decide_eq_true selected,sender,recipient,owned,origin,prior,?_⟩
  simpa only [same] using paid

def actual (state : State model start) : Nat → DynamicCommandSource.Outcome model start delay :=
  DynamicCommandSource.actual model start delay (fun _ before => choose model start vocabulary law delay before) state

def journey (state : State model start) : Nat → State model start × List LocalCommandSource.Input :=
  Nat.rec (state,[]) (fun _ previous =>
    let input := choose model start vocabulary law delay previous.1
    (LocalCommandRun.step model start previous.1 input,previous.2 ++ [input]))

theorem the_generated_transcript_executes_the_same_actual_state
    (state : State model start) (count : Nat) :
    (journey model start vocabulary law delay state count).1 =
      (journey model start vocabulary law delay state count).2.foldl (LocalCommandRun.step model start) state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change LocalCommandRun.step model start (journey model start vocabulary law delay state count).1 _ =
      ((journey model start vocabulary law delay state count).2 ++ [_]).foldl _ state
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,← ih]

theorem resuming_the_actual_state_is_the_same_generated_execution
    (state : State model start) (before after : Nat) :
    (journey model start vocabulary law delay state (before+after)).1 =
      (journey model start vocabulary law delay
        (journey model start vocabulary law delay state before).1 after).1 := by
  induction after with
  | zero => rfl
  | succ after ih =>
    exact congrArg (fun current => LocalCommandRun.step model start current
      (choose model start vocabulary law delay current)) ih

theorem every_actual_dispatch_step_spends_its_original_invocation
    (state : State model start) (input : LocalCommandSource.Input) :
    (EventStep.seed ((LocalCommandRun.step model start state input).current model start)).remaining =
      (EventStep.seed (state.current model start)).remaining - 1 := by
  change (EventStep.seed (EventHistory.execute start (state.stages ++ [_]))).remaining = _
  rw [OriginQueue.execute_append]
  change (EventStep.seed ((state.current model start).after _ _)).remaining = _
  rw [EventStep.actual_next_state]
  rfl

theorem the_actual_invocation_account_bounds_every_generated_prefix
    (state : State model start) (count : Nat) :
    (EventStep.seed ((journey model start vocabulary law delay state count).1.current model start)).remaining =
      (EventStep.seed (state.current model start)).remaining - count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (EventStep.seed ((LocalCommandRun.step model start
      (journey model start vocabulary law delay state count).1 _).current model start)).remaining = _
    rw [every_actual_dispatch_step_spends_its_original_invocation,ih]
    omega

theorem original_fuel_generates_every_actual_admitted_dispatch_prefix
    (state : State model start) (count : Nat)
    (funded : count ≤ (EventStep.seed (state.current model start)).remaining) :
    actual model start vocabulary law delay state count =
      .running (journey model start vocabulary law delay state count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have before := ih (by omega)
    have live : 0 < (EventStep.seed ((journey model start vocabulary law delay state count).1.current model start)).remaining := by
      rw [the_actual_invocation_account_bounds_every_generated_prefix]
      omega
    have allowed := (List.mem_filter.mp (positive_actual_fuel_admits_the_generated_choice
      model start vocabulary law delay _ live)).2
    change DynamicCommandSource.tick model start delay
      (fun _ previous => choose model start vocabulary law delay previous) count
      (actual model start vocabulary law delay state count) = _
    rw [before]
    simp only [DynamicCommandSource.tick,DynamicCommandSource.submit,allowed,dif_pos]
    rfl

theorem every_running_dispatch_is_an_original_dynamic_execution
    (state branch : State model start) (count : Nat)
    (running : actual model start vocabulary law delay state count = .running branch) :
    branch ∈ DynamicCommandSource.cases model start delay state count :=
  DynamicCommandSource.every_running_adaptive_execution_has_its_generated_source_branch model start delay
    (fun _ before => choose model start vocabulary law delay before) state branch count
    (fun _ before => every_choice_is_in_the_original_source_menu model start vocabulary law delay before) running

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderDispatch
