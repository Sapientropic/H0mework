import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponse
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawal

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (pastStages : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev current := EventHistory.execute start pastStages
abbrev observed := IncidentResponse.journal model start pastStages vocabulary encoding law
abbrev snapshot (answer : IncidentResponse.Answer model start vocabulary encoding law) :=
  (EventStep.seed (EventHistory.execute start answer.pastStages)).current.technology
abbrev actor (answer : IncidentResponse.Answer model start vocabulary encoding law) := model.source.code.siteParty answer.response.incident.receiver
abbrev action (answer : IncidentResponse.Answer model start vocabulary encoding law) :=
  Mandate.request model.scope (EventStep.seed (current model start pastStages)).current (actor model start vocabulary encoding law answer) .revoke

inductive Obstruction where
  | snapshotChanged | notMember | unsupportedAction | noActionCapacity | unsupportedActivation | exhausted | notOwner | sealed
  deriving DecidableEq

structure Ready where
  private mk ::
  answer : IncidentResponse.Answer model start vocabulary encoding law
  actual : answer ∈ observed model start pastStages vocabulary encoding law
  sameSnapshot : (EventStep.seed (current model start pastStages)).current.technology = snapshot model start vocabulary encoding law answer
  member : actor model start vocabulary encoding law answer ∈ Delegation.members model.scope.task
  supported : action model start pastStages vocabulary encoding law answer ∈ model.source.code.actions
  capacity : 1 ≤ model.source.code.actionLimit
  activation : .activate answer.response.incident.receiver ∈ model.source.code.eventAlphabet
  fuel : 0 < (EventStep.seed (current model start pastStages)).remaining
  owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start pastStages).ownerStart
    (EventStep.seed (current model start pastStages)).history.length = some answer.response.incident.receiver
  memory : model.source.code.memoryReady ((EventStep.seed (current model start pastStages)).frame.inbox answer.response.incident.receiver) = true

inductive Plan where
  | noResponse
  | blocked (reason : Obstruction)
  | paid (ready : Ready model start pastStages vocabulary encoding law)
      (accepted : model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law ready.answer))
  | refused (ready : Ready model start pastStages vocabulary encoding law)
      (denied : ¬model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law ready.answer))

private theorem head_member {α : Type} (items : List α) (value : α) (first : items.head? = some value) : value ∈ items := by
  cases items with
  | nil => cases first
  | cons head tail =>
    have same : head = value := Option.some.inj first
    subst value
    exact List.mem_cons_self

def produce : Plan model start pastStages vocabulary encoding law :=
  match first : (observed model start pastStages vocabulary encoding law).head? with
  | none => .noResponse
  | some answer =>
    if sameSnapshot : (EventStep.seed (current model start pastStages)).current.technology = snapshot model start vocabulary encoding law answer then
    if member : actor model start vocabulary encoding law answer ∈ Delegation.members model.scope.task then
    if supported : action model start pastStages vocabulary encoding law answer ∈ model.source.code.actions then
    if capacity : 1 ≤ model.source.code.actionLimit then
    if activation : .activate answer.response.incident.receiver ∈ model.source.code.eventAlphabet then
    if fuel : 0 < (EventStep.seed (current model start pastStages)).remaining then
    if owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start pastStages).ownerStart
        (EventStep.seed (current model start pastStages)).history.length = some answer.response.incident.receiver then
    if memory : model.source.code.memoryReady ((EventStep.seed (current model start pastStages)).frame.inbox answer.response.incident.receiver) = true then
      let ready : Ready model start pastStages vocabulary encoding law :=
        ⟨answer, head_member _ _ first, sameSnapshot, member, supported, capacity, activation, fuel, owner, memory⟩
      if accepted : model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law answer) then
        .paid ready accepted
      else .refused ready accepted
    else .blocked .sealed
    else .blocked .notOwner
    else .blocked .exhausted
    else .blocked .unsupportedActivation
    else .blocked .noActionCapacity
    else .blocked .unsupportedAction
    else .blocked .notMember
    else .blocked .snapshotChanged

variable (ready : Ready model start pastStages vocabulary encoding law)

def work : model.source.code.Policy := fun key _ =>
  if key.1 = ready.answer.response.incident.receiver then [action model start pastStages vocabulary encoding law ready.answer] else []

theorem work_generated : work model start pastStages vocabulary encoding law ready ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split
  · exact ⟨ready.capacity, by intro request member; simpa only [List.mem_singleton.mp member] using ready.supported⟩
  · simp

def localActivation : LocalMove model.source.code ready.answer.response.incident.receiver :=
  ⟨some ⟨.activate ready.answer.response.incident.receiver, ready.activation⟩, by
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨⟨.activate ready.answer.response.incident.receiver, ready.activation⟩, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_attach _ _, by simp⟩⟩

def protocol : Rule model.source.code where
  work := ⟨work model start pastStages vocabulary encoding law ready, work_generated model start pastStages vocabulary encoding law ready⟩
  events := fun key _ => if same : key.1 = ready.answer.response.incident.receiver then
    same.symm ▸ localActivation model start pastStages vocabulary encoding law ready
  else ⟨none, List.mem_cons_self⟩

abbrev row (rival : Opponent model.source.code) :=
  StageTrace.material (current model start pastStages) (protocol model start pastStages vocabulary encoding law ready) rival

theorem attempt_uses_the_actual_owned_activation (rival : Opponent model.source.code) :
    StageTrace.activation (row model start pastStages vocabulary encoding law ready rival) = some ready.answer.response.incident.receiver := by
  have live : (EventStep.seed (current model start pastStages)).remaining ≠ 0 := Nat.ne_of_gt ready.fuel
  simp [row, StageTrace.activation, StageTrace.material, StageTrace.capture, live, ready.owner, localEvent, protocol, localActivation]

theorem attempt_submits_the_actual_member_request (rival : Opponent model.source.code) :
    (row model start pastStages vocabulary encoding law ready rival).submitted = [action model start pastStages vocabulary encoding law ready.answer] := by
  have actual := StageTrace.an_owned_activation_submits_its_selected_work (current model start pastStages)
    (protocol model start pastStages vocabulary encoding law ready) rival ready.answer.response.incident.receiver
    (attempt_uses_the_actual_owned_activation model start pastStages vocabulary encoding law ready rival)
  exact actual.2.trans (by simp [protocol, Code.action, ready.memory, work])

theorem request_has_actual_withdrawal_standing : Mandate.Challenge.Withdrawal (scope := model.scope)
    (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law ready.answer) := by
  exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨ready.member, rfl⟩⟩

def stages (rival : Opponent model.source.code) :=
  match produce model start pastStages vocabulary encoding law with
  | .paid selected _ | .refused selected _ => pastStages ++ [(protocol model start pastStages vocabulary encoding law selected, rival)]
  | _ => pastStages

theorem paid_appends_the_actual_attempt (rival : Opponent model.source.code)
    (accepted : model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law ready.answer))
    (selected : produce model start pastStages vocabulary encoding law = .paid ready accepted) :
    stages model start pastStages vocabulary encoding law rival = pastStages ++ [(protocol model start pastStages vocabulary encoding law ready, rival)] := by
  simp only [stages, selected]

theorem refused_appends_the_actual_attempt (rival : Opponent model.source.code)
    (denied : ¬model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law ready.answer))
    (selected : produce model start pastStages vocabulary encoding law = .refused ready denied) :
    stages model start pastStages vocabulary encoding law rival = pastStages ++ [(protocol model start pastStages vocabulary encoding law ready, rival)] := by
  simp only [stages, selected]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawal

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawal.Candidates

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (pastStages : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

-- Membership is supplied by the source journal scan; the old head-only producer is unchanged.
def inspect (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (actual : answer ∈ observed model start pastStages vocabulary encoding law) :
    Plan model start pastStages vocabulary encoding law :=
  if sameSnapshot : (EventStep.seed (current model start pastStages)).current.technology = snapshot model start vocabulary encoding law answer then
  if member : actor model start vocabulary encoding law answer ∈ Delegation.members model.scope.task then
  if supported : action model start pastStages vocabulary encoding law answer ∈ model.source.code.actions then
  if capacity : 1 ≤ model.source.code.actionLimit then
  if activation : .activate answer.response.incident.receiver ∈ model.source.code.eventAlphabet then
  if fuel : 0 < (EventStep.seed (current model start pastStages)).remaining then
  if owner : Distributed.Recall.Information.Agency.ownerAt model.source.code (current model start pastStages).ownerStart
      (EventStep.seed (current model start pastStages)).history.length = some answer.response.incident.receiver then
  if memory : model.source.code.memoryReady ((EventStep.seed (current model start pastStages)).frame.inbox answer.response.incident.receiver) = true then
    let ready : Ready model start pastStages vocabulary encoding law :=
      ⟨answer, actual, sameSnapshot, member, supported, capacity, activation, fuel, owner, memory⟩
    if accepted : model.source.code.law.Valid (EventStep.seed (current model start pastStages)).current (action model start pastStages vocabulary encoding law answer) then
      .paid ready accepted
    else .refused ready accepted
  else .blocked .sealed
  else .blocked .notOwner
  else .blocked .exhausted
  else .blocked .unsupportedActivation
  else .blocked .noActionCapacity
  else .blocked .unsupportedAction
  else .blocked .notMember
  else .blocked .snapshotChanged

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawal.Candidates
