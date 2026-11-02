import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RefusalHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReview

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))

abbrev current := EventHistory.execute start past
abbrev native := IncidentChallenge.native model start past
abbrev family := IncidentChallenge.family model start past
abbrev sourceIndex := IncidentChallenge.sourceIndex model start past
abbrev depth := IncidentChallenge.depth model start past
abbrev inventory := (Native.Authority.fullGenerate (native model start past) (depth model start past)).challenges
def pending := (inventory model start past).filter fun row => row.2.isPending (family model start past) (sourceIndex model start past)
def complete : Bool := (pending model start past).isEmpty
abbrev action (receiver : Fin model.source.code.sites) :=
  Mandate.request model.scope (EventStep.seed (current model start past)).current (model.source.code.siteParty receiver) .revoke

inductive Obstruction where
  | notMember | unsupportedAction | noActionCapacity | unsupportedActivation | exhausted | sealed
  deriving DecidableEq

structure Ready where
  private mk ::
  outstanding : complete model start past = false
  receiver : Fin model.source.code.sites
  member : model.source.code.siteParty receiver ∈ Delegation.members model.scope.task
  supported : action model start past receiver ∈ model.source.code.actions
  capacity : 1 ≤ model.source.code.actionLimit
  activation : .activate receiver ∈ model.source.code.eventAlphabet
  fuel : 0 < (EventStep.seed (current model start past)).remaining
  owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start past).ownerStart
    (EventStep.seed (current model start past)).history.length = some receiver
  memory : model.source.code.memoryReady ((EventStep.seed (current model start past)).frame.inbox receiver) = true

inductive Plan where
  | clear (closed : complete model start past = true)
  | environmentTurn
  | blocked (reason : Obstruction)
  | paid (ready : Ready model start past)
      (accepted : model.source.code.law.Valid (EventStep.seed (current model start past)).current (action model start past ready.receiver))
  | refused (ready : Ready model start past)
      (denied : ¬ model.source.code.law.Valid (EventStep.seed (current model start past)).current (action model start past ready.receiver))

-- The entire native inventory drives this request; neither response journal is a selection premise.
def produce : Plan model start past :=
  if closed : complete model start past = true then .clear closed else
  match owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start past).ownerStart
      (EventStep.seed (current model start past)).history.length with
  | none => .environmentTurn
  | some receiver =>
    if member : model.source.code.siteParty receiver ∈ Delegation.members model.scope.task then
    if supported : action model start past receiver ∈ model.source.code.actions then
    if capacity : 1 ≤ model.source.code.actionLimit then
    if activation : .activate receiver ∈ model.source.code.eventAlphabet then
    if fuel : 0 < (EventStep.seed (current model start past)).remaining then
    if memory : model.source.code.memoryReady ((EventStep.seed (current model start past)).frame.inbox receiver) = true then
      let ready : Ready model start past :=
        ⟨Bool.eq_false_of_not_eq_true closed, receiver, member, supported, capacity, activation, fuel, owner, memory⟩
      if accepted : model.source.code.law.Valid (EventStep.seed (current model start past)).current (action model start past receiver)
      then .paid ready accepted else .refused ready accepted
    else .blocked .sealed
    else .blocked .exhausted
    else .blocked .unsupportedActivation
    else .blocked .noActionCapacity
    else .blocked .unsupportedAction
    else .blocked .notMember

variable (ready : Ready model start past)

def work : model.source.code.Policy := fun key _ =>
  if key.1 = ready.receiver then [action model start past ready.receiver] else []

theorem work_generated : work model start past ready ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split
  · exact ⟨ready.capacity, by intro request member; simpa only [List.mem_singleton.mp member] using ready.supported⟩
  · simp

def localActivation : LocalMove model.source.code ready.receiver :=
  ⟨some ⟨.activate ready.receiver, ready.activation⟩, by
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨⟨.activate ready.receiver, ready.activation⟩, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_attach _ _, by simp⟩⟩

def protocol : Rule model.source.code where
  work := ⟨work model start past ready, work_generated model start past ready⟩
  events := fun key _ => if same : key.1 = ready.receiver then
    same.symm ▸ localActivation model start past ready else ⟨none, List.mem_cons_self⟩

abbrev row (rival : Opponent model.source.code) :=
  StageTrace.material (current model start past) (protocol model start past ready) rival

theorem the_actual_owner_submits_the_original_member_request (rival : Opponent model.source.code) :
    StageTrace.activation (row model start past ready rival) = some ready.receiver ∧
      (row model start past ready rival).submitted = [action model start past ready.receiver] := by
  have live : (EventStep.seed (current model start past)).remaining ≠ 0 := Nat.ne_of_gt ready.fuel
  have activation : StageTrace.activation (row model start past ready rival) = some ready.receiver := by
    simp [row, StageTrace.activation, StageTrace.material, StageTrace.capture, live, ready.owner,
      localEvent, protocol, localActivation]
  refine ⟨activation, ?_⟩
  have actual := StageTrace.an_owned_activation_submits_its_selected_work (current model start past)
    (protocol model start past ready) rival ready.receiver activation
  exact actual.2.trans (by simp [protocol, Code.action, ready.memory, work])

theorem actual_withdrawal_standing : Mandate.Challenge.Withdrawal (scope := model.scope)
    (EventStep.seed (current model start past)).current (action model start past ready.receiver) :=
  ⟨rfl, rfl, rfl, rfl, Or.inl ⟨ready.member, rfl⟩⟩

def stages (rival : Opponent model.source.code) :=
  match produce model start past with
  | .paid selected _ | .refused selected _ => past ++ [(protocol model start past selected, rival)]
  | _ => past

theorem every_result_preserves_the_whole_actual_prefix (rival : Opponent model.source.code) :
    ∃ tail, stages model start past rival = past ++ tail := by
  unfold stages
  cases produce model start past with
  | paid selected accepted => exact ⟨_, rfl⟩
  | refused selected denied => exact ⟨_, rfl⟩
  | clear closed => exact ⟨[], (List.append_nil _).symm⟩
  | environmentTurn => exact ⟨[], (List.append_nil _).symm⟩
  | blocked reason => exact ⟨[], (List.append_nil _).symm⟩

theorem completion_covers_every_native_original :
    complete model start past = true ↔
      ∀ original ∈ inventory model start past, original.2.isPending (family model start past) (sourceIndex model start past) = false := by
  simp [complete, pending, List.filter_eq_nil_iff]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReview
