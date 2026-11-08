import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryControlConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Input where
  | idle | command (index : Nat) | event (index : Nat)
  deriving DecidableEq
inductive Refusal where
  | outsideInterface | notOwned | wrongSigner | noCapacity | sealed | unsupportedActivation | notLocalEvent
  deriving DecidableEq
inductive Verdict where
  | stopped | idle | external | local | command | blocked (reason : Refusal)
  deriving DecidableEq

abbrev owner (cursor : Cursor model.source.code) :=
  Distributed.Recall.Information.Agency.ownerAt model.source.code cursor.ownerStart (EventStep.seed cursor).history.length
abbrev request (index : Nat) := model.source.code.actions[index]?

structure Work (cursor : Cursor model.source.code) where
  private mk ::
  worker : Fin model.source.code.sites
  value : Request Party Good Port (Mandate.State Party Technology) Instrument
  original : value ∈ model.source.code.actions
  signed : value.signer = model.source.code.siteParty worker
  owned : owner model cursor = some worker
  live : (EventStep.seed cursor).remaining ≠ 0
  capacity : 1 ≤ model.source.code.actionLimit
  memory : model.source.code.memoryReady ((EventStep.seed cursor).frame.inbox worker) = true
  activation : Event.activate worker ∈ model.source.code.eventAlphabet

structure Local (cursor : Cursor model.source.code) where
  private mk ::
  worker : Fin model.source.code.sites
  owned : owner model cursor = some worker
  move : LocalMove model.source.code worker

inductive Selection (cursor : Cursor model.source.code) where
  | stopped | idle | blocked (reason : Refusal)
  | external (move : Move model.source.code)
  | local (value : Local model cursor)
  | command (value : Work model cursor)

def select (cursor : Cursor model.source.code) (input : Input) : Selection model cursor :=
  if empty : (EventStep.seed cursor).remaining = 0 then .stopped else
  match input with
  | .idle => .idle
  | .command index => match owned : owner model cursor with
    | none => .blocked .notOwned
    | some worker => match original : request model index with
      | none => .blocked .outsideInterface
      | some value =>
        if signed : value.signer = model.source.code.siteParty worker then
          if capacity : 1 ≤ model.source.code.actionLimit then
            if memory : model.source.code.memoryReady ((EventStep.seed cursor).frame.inbox worker) = true then
              if activation : Event.activate worker ∈ model.source.code.eventAlphabet then
                .command ⟨worker,value,List.mem_of_getElem? original,signed,owned,empty,capacity,memory,activation⟩
              else .blocked .unsupportedActivation
            else .blocked .sealed
          else .blocked .noCapacity
        else .blocked .wrongSigner
  | .event index => match original : model.source.code.eventAlphabet[index]? with
    | none => .blocked .outsideInterface
    | some value =>
      let event : Choice model.source.code := ⟨value,List.mem_of_getElem? original⟩
      match owned : owner model cursor with
      | none => .external (some event)
      | some worker =>
        if allowed : some event ∈ ownMoves model.source.code worker then .local ⟨worker,owned,⟨some event,allowed⟩⟩
        else .blocked .notLocalEvent

def Selection.verdict {cursor : Cursor model.source.code} : Selection model cursor → Verdict
  | .stopped => .stopped | .idle => .idle | .external _ => .external
  | .local _ => .local | .command _ => .command | .blocked reason => .blocked reason

def Work.policy {cursor : Cursor model.source.code} (work : Work model cursor) : model.source.code.Policy :=
  fun key _ => if key.1 = work.worker then [work.value] else []

theorem Work.policy_generated {cursor : Cursor model.source.code} (work : Work model cursor) :
    work.policy model ∈ model.source.code.policies := by
  apply model.source.code.every_local_policy_is_enumerated
  intro key _
  unfold Work.policy
  split
  · exact (mem_words_iff _ _ _).mpr ⟨by simpa using work.capacity,by simpa using work.original⟩
  · exact (mem_words_iff _ _ _).mpr (by simp)

def Work.protocol {cursor : Cursor model.source.code} (work : Work model cursor) : Rule model.source.code where
  work := ⟨work.policy model,work.policy_generated model⟩
  events := fun key _ => if same : key.1 = work.worker then
    same.symm ▸ LocalWithdrawal.activation model work.worker work.activation
    else ⟨none,List.mem_cons_self⟩

def Local.protocol {cursor : Cursor model.source.code} (choice : Local model cursor) : Rule model.source.code :=
  {InquiryServiceWindow.quiet model with events := fun key _ =>
    if same : key.1 = choice.worker then same.symm ▸ choice.move else ⟨none,List.mem_cons_self⟩}

def Selection.protocol {cursor : Cursor model.source.code} : Selection model cursor → Rule model.source.code
  | .command work => work.protocol model
  | .local choice => choice.protocol model
  | _ => InquiryServiceWindow.quiet model

def Selection.rival {cursor : Cursor model.source.code} : Selection model cursor → Opponent model.source.code
  | .external move => EventStep.fixed move
  | _ => EventStep.fixed none

structure Entry where
  private mk ::
  before : Cursor model.source.code
  input : Input

def observe (cursor : Cursor model.source.code) (input : Input) : Entry model := ⟨cursor,input⟩
abbrev Entry.selected (entry : Entry model) := select model entry.before entry.input
abbrev Entry.verdict (entry : Entry model) := entry.selected model |>.verdict model
abbrev Entry.stage (entry : Entry model) : EventHistory.Stage (code := model.source.code) :=
  (entry.selected model |>.protocol model,entry.selected model |>.rival model)
abbrev Entry.row (entry : Entry model) := StageTrace.material entry.before (entry.stage model).1 (entry.stage model).2
abbrev Entry.after (entry : Entry model) := entry.before.after (entry.stage model).1 (entry.stage model).2

-- The raw requested index and its source lookup remain available even when the local gate suppresses work.
def Entry.requested (entry : Entry model) := match entry.input with
  | .command index => request model index
  | _ => none

theorem a_selected_command_has_the_actual_owner_and_source_request
    (cursor : Cursor model.source.code) (input : Input) (work : Work model cursor)
    (selected : select model cursor input = .command work) :
    ∃ index, input = .command index ∧ request model index = some work.value ∧
      work.value.signer = model.source.code.siteParty work.worker ∧ owner model cursor = some work.worker := by
  cases input with
  | idle =>
    unfold select at selected
    dsimp only at selected
    split at selected <;> contradiction
  | event index =>
    unfold select at selected
    dsimp only at selected
    split at selected <;> try contradiction
    split at selected <;> try contradiction
    split at selected <;> try contradiction
    split at selected <;> contradiction
  | command index =>
    unfold select at selected
    dsimp only at selected
    split at selected <;> try contradiction
    split at selected <;> try contradiction
    split at selected <;> try contradiction
    split_ifs at selected; try contradiction
    cases Selection.command.inj selected
    exact ⟨index,rfl,by assumption,by assumption,by assumption⟩

theorem the_generated_work_is_actually_submitted {cursor : Cursor model.source.code} (work : Work model cursor) :
    (StageTrace.material cursor (work.protocol model) (EventStep.fixed none)).submitted = [work.value] := by
  have owned : Distributed.Recall.Information.Agency.ownerAt model.source.code cursor.ownerStart
      (EventStep.seed cursor).history.length = some work.worker := work.owned
  have activated : StageTrace.activation (StageTrace.material cursor (work.protocol model) (EventStep.fixed none)) = some work.worker := by
    simp [StageTrace.activation,StageTrace.material,StageTrace.capture,work.live,owned,
      localEvent,Work.protocol,LocalWithdrawal.activation]
  have submitted := StageTrace.an_owned_activation_submits_its_selected_work cursor (work.protocol model)
    (EventStep.fixed none) work.worker activated
  exact submitted.2.trans (by simp only [Work.protocol,Code.action,work.memory,if_true,Work.policy])

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandSource
