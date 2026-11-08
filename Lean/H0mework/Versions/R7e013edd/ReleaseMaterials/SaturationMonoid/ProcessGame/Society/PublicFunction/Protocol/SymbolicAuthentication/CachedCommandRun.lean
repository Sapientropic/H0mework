import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkDispatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedCommandRun
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

abbrev ownerAt (cursor : Cursor model.source.code) (before : Feedback.State model.source.code) :=
  Distributed.Recall.Information.Agency.ownerAt model.source.code cursor.ownerStart before.history.length

def workProtocol (worker : Fin model.source.code.sites)
    (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (original : value ∈ model.source.code.actions) (capacity : 1 ≤ model.source.code.actionLimit)
    (activation : Event.activate worker ∈ model.source.code.eventAlphabet) : Rule model.source.code where
  work := ⟨fun key _ => if key.1 = worker then [value] else [],by
    apply model.source.code.every_local_policy_is_enumerated
    intro key _
    split
    · exact (mem_words_iff _ _ _).mpr ⟨by simpa using capacity,by simpa using original⟩
    · exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun key _ => if same : key.1 = worker then
    same.symm ▸ LocalWithdrawal.activation model worker activation else ⟨none,List.mem_cons_self⟩

def localProtocol (worker : Fin model.source.code.sites) (move : LocalMove model.source.code worker) : Rule model.source.code :=
  {InquiryServiceWindow.quiet model with events := fun key _ =>
    if same : key.1 = worker then same.symm ▸ move else ⟨none,List.mem_cons_self⟩}

-- All gates are evaluated on the retained actual state; no next state is supplied.
def stageAt (cursor : Cursor model.source.code) (before : Feedback.State model.source.code)
    (input : LocalCommandSource.Input) : EventHistory.Stage (code := model.source.code) :=
  let quiet := (InquiryServiceWindow.quiet model,EventStep.fixed none)
  if before.remaining = 0 then quiet else
  match input with
  | .idle => quiet
  | .command index => match ownerAt model cursor before with
    | none => quiet
    | some worker => match original : LocalCommandSource.request model index with
      | none => quiet
      | some value =>
        if value.signer = model.source.code.siteParty worker then
          if capacity : 1 ≤ model.source.code.actionLimit then
            if model.source.code.memoryReady (before.frame.inbox worker) = true then
              if activation : Event.activate worker ∈ model.source.code.eventAlphabet then
                (workProtocol model worker value (List.mem_of_getElem? original) capacity activation,EventStep.fixed none)
              else quiet
            else quiet
          else quiet
        else quiet
  | .event index => match original : model.source.code.eventAlphabet[index]? with
    | none => quiet
    | some value =>
      let event : Choice model.source.code := ⟨value,List.mem_of_getElem? original⟩
      match ownerAt model cursor before with
      | none => (InquiryServiceWindow.quiet model,EventStep.fixed (some event))
      | some worker =>
        if allowed : some event ∈ ownMoves model.source.code worker then
          (localProtocol model worker ⟨some event,allowed⟩,EventStep.fixed none)
        else quiet

set_option linter.unusedSimpArgs false in
theorem stageAt_eq (cursor : Cursor model.source.code) (before : Feedback.State model.source.code)
    (correct : before = EventStep.seed cursor) (input : LocalCommandSource.Input) :
    stageAt model cursor before input = (LocalCommandSource.observe model cursor input).stage model := by
  subst before
  change stageAt model cursor (EventStep.seed cursor) input =
    ((LocalCommandSource.select model cursor input).protocol model,(LocalCommandSource.select model cursor input).rival model)
  generalize selected : LocalCommandSource.select model cursor input = selection
  unfold LocalCommandSource.select at selected
  split at selected
  · subst selection
    simp_all [stageAt,LocalCommandSource.Selection.protocol,LocalCommandSource.Selection.rival]
  · cases input <;> dsimp only at selected
    all_goals repeat' (split at selected)
    all_goals subst selection
    all_goals simp_all [stageAt,ownerAt,LocalCommandSource.owner,LocalCommandSource.request,
      LocalCommandSource.Selection.protocol,LocalCommandSource.Selection.rival,
      LocalCommandSource.Work.protocol,LocalCommandSource.Local.protocol]
    all_goals repeat' (split <;> simp_all [LocalCommandSource.request,LocalCommandSource.owner,ownerAt])
    all_goals first
      | grind [workProtocol,localProtocol,LocalCommandSource.Work.policy]
      | (
        rename_i live index worker owned value original signed capacity memory activation
        change model.source.code.actions[index]? = some value at original
        split
        · rename_i absent
          rw [original] at absent
          contradiction
        · rename_i other found
          have same := Option.some.inj (original.symm.trans found)
          subst other
          rw [if_pos signed]
          rfl)

def materialAt (cursor : Cursor model.source.code) (before : Feedback.State model.source.code)
    (protocol : Rule model.source.code) (rival : Opponent model.source.code) : StageTrace.Record (code := model.source.code) :=
  let call := StageTrace.capture cursor protocol rival before
  let selected : Input model.source.code := ⟨fun _ _ _ => ControlExecution.admitted model.source.code call,cursor.entry.budget⟩
  ⟨cursor,protocol,before,call,word model.source.code (some protocol.work.val) selected before,
    Reaction.Feedback.advance model.source.code (some protocol.work.val) selected before⟩

theorem materialAt_eq (cursor : Cursor model.source.code) (before : Feedback.State model.source.code)
    (correct : before = EventStep.seed cursor) (protocol : Rule model.source.code) (rival : Opponent model.source.code) :
    materialAt model cursor before protocol rival = StageTrace.material cursor protocol rival := by
  subst before
  rfl

structure Cache (state : LocalCommandRun.State model start) where
  cursor : Cursor model.source.code
  before : Feedback.State model.source.code
  rows : List (StageTrace.Record (code := model.source.code))
  cursor_eq : cursor = state.current model start
  before_eq : before = EventStep.seed cursor
  rows_eq : rows = StageTrace.records start state.stages

variable {model start}
def Cache.stage {state : LocalCommandRun.State model start} (cache : Cache model start state) (input : LocalCommandSource.Input) : EventHistory.Stage (code := model.source.code) :=
  stageAt model cache.cursor cache.before input
def Cache.row {state : LocalCommandRun.State model start} (cache : Cache model start state) (input : LocalCommandSource.Input) :=
  materialAt model cache.cursor cache.before (cache.stage input).1 (cache.stage input).2

theorem Cache.stage_eq {state : LocalCommandRun.State model start} (cache : Cache model start state) (input : LocalCommandSource.Input) :
    cache.stage input = (LocalCommandSource.observe model (state.current model start) input).stage model := by
  rw [Cache.stage,stageAt_eq model cache.cursor cache.before cache.before_eq,cache.cursor_eq]
theorem Cache.row_eq {state : LocalCommandRun.State model start} (cache : Cache model start state) (input : LocalCommandSource.Input) :
    cache.row input = HeaderDispatch.row model start state input := by
  rw [Cache.row,materialAt_eq model cache.cursor cache.before cache.before_eq,cache.stage_eq,cache.cursor_eq]
  rfl

variable (model start)
def initial : Cache model start (LocalCommandRun.initial model start) := ⟨start,EventStep.seed start,[],rfl,rfl,rfl⟩

def step {state : LocalCommandRun.State model start} (cache : Cache model start state) (input : LocalCommandSource.Input) :
    Cache model start (LocalCommandRun.step model start state input) where
  cursor := cache.cursor.after (cache.stage input).1 (cache.stage input).2
  before := (cache.row input).after
  rows := cache.rows ++ [cache.row input]
  cursor_eq := by
    change _ = EventHistory.execute start (state.stages ++ [_])
    rw [OriginQueue.execute_append,cache.cursor_eq,cache.stage_eq]
    rfl
  before_eq := by
    rw [Cache.row,materialAt_eq model cache.cursor cache.before cache.before_eq]
    exact (StageTrace.material_is_the_actual_step _ _ _).1
  rows_eq := by
    change _ = StageTrace.records start (state.stages ++ [_])
    rw [OriginQueue.records_append,cache.rows_eq,cache.row_eq]
    rfl

def run : (inputs : List LocalCommandSource.Input) → Cache model start (LocalCommandRun.run model start inputs)
  | [] => initial model start
  | input :: tail => by
    let next := step model start (initial model start) input
    exact fold tail next
where
  fold (inputs : List LocalCommandSource.Input) : {state : LocalCommandRun.State model start} →
      Cache model start state → Cache model start (inputs.foldl (LocalCommandRun.step model start) state) :=
    inputs.rec (motive := fun inputs => {state : LocalCommandRun.State model start} →
      Cache model start state → Cache model start (inputs.foldl (LocalCommandRun.step model start) state))
      (fun {_} cache => cache)
      (fun input _ next {_} cache => next (step model start cache input))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedCommandRun
