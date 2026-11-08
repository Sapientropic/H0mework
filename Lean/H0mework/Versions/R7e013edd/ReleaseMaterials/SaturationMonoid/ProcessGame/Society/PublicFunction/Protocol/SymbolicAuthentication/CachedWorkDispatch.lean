import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedCommandRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedWorkDispatch
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def issuedAt (rows : List (StageTrace.Record (code := code))) (index : Nat) :=
  match rows[index]? with
  | none => none
  | some row => HeaderTransport.issue vocabulary (rows.take index) row
def wires (rows : List (StageTrace.Record (code := code))) :=
  (List.range rows.length).filterMap (issuedAt vocabulary rows)

theorem issuedAt_eq (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) (index : Nat) :
    issuedAt vocabulary (StageTrace.records start stages) index = HeaderTransport.issuedAt vocabulary start stages index := by
  rfl
theorem wires_eq (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    wires vocabulary (StageTrace.records start stages) = HeaderTransport.wires vocabulary start stages := by
  simp only [wires,HeaderTransport.wires,StageTrace.record_count,issuedAt_eq]

def check (law : StageReception.Law code) (rows : List (StageTrace.Record (code := code)))
    (receiver : Fin code.sites) (row : StageTrace.Record (code := code))
    (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := code)) : HeaderReception.Verdict (code := code) :=
  if HeaderReception.delivered row wire.serial ≠ true then .rejected .missingDelivery
  else if ¬ wire.sendCut < row.cursor.cut then .rejected .unauthenticated
  else if decide (wire ∈ wires vocabulary rows) ≠ true then .rejected .unauthenticated
  else if HeaderReception.matchingPacket row wire ≠ true then .rejected .missingPacket
  else if wire.recipient ≠ receiver then .rejected .wrongRecipient
  else if wire.ballot.scope ≠ law.scope receiver row.before.current then .rejected .staleScope
  else if ¬ row.cursor.cut ≤ wire.sendCut + law.maxDelay then .rejected .late
  else if ¬ ∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request then .rejected .unpaidDelivery
  else if (wire.ballot.cut,wire.ballot.position) ∈ seen then .rejected .duplicate
  else .accepted wire

theorem check_eq (law : StageReception.Law code) (start : Cursor code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (row : StageTrace.Record (code := code)) (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := code)) :
    check vocabulary law (StageTrace.records start stages) receiver row seen wire =
      HeaderReception.check vocabulary law start stages receiver row seen wire := by
  simp only [check,HeaderReception.check,HeaderTransport.verify,wires_eq]

def incoming (rows : List (StageTrace.Record (code := code))) (index : Nat) : Option (HeaderTransport.Wire (code := code)) :=
  match rows[index]? with
  | none => none
  | some row => match HeaderTransport.admission row with
    | none => none
    | some event => match event.val with
      | .deliver serial => ((List.range index).filterMap (issuedAt vocabulary rows)).find? (fun wire => wire.serial == serial)
      | _ => none
def receive (law : StageReception.Law code) (rows : List (StageTrace.Record (code := code)))
    (receiver : Fin code.sites) (index : Nat) (previous : HeaderReception.Receiver (code := code)) : HeaderReception.Receiver (code := code) :=
  match rows[index]? with
  | none => previous
  | some row =>
    let candidate := incoming vocabulary rows index
    let verdict := match candidate with
      | none => AttestationReception.VerdictData.rejected .missingWire
      | some wire => check vocabulary law rows receiver row
          (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire
    ⟨match verdict with
      | .accepted wire => previous.receipts ++ [⟨wire,index,row.cursor.cut⟩]
      | .rejected _ => previous.receipts,
      previous.audit ++ [(row.cursor.cut,candidate,verdict)]⟩
def run (law : StageReception.Law code) (rows : List (StageTrace.Record (code := code))) (receiver : Fin code.sites) : Nat → HeaderReception.Receiver (code := code) :=
  Nat.rec ⟨[],[]⟩ (fun index previous => receive vocabulary law rows receiver index previous)

theorem incoming_eq (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) (index : Nat) :
    incoming vocabulary (StageTrace.records start stages) index = HeaderReception.incoming vocabulary start stages index := by
  simp only [incoming,HeaderReception.incoming,issuedAt_eq]
  rfl
theorem receive_eq (law : StageReception.Law code) (start : Cursor code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (index : Nat)
    (previous : HeaderReception.Receiver (code := code)) :
    receive vocabulary law (StageTrace.records start stages) receiver index previous =
      HeaderReception.receive vocabulary law start stages receiver index previous := by
  simp only [receive,HeaderReception.receive,incoming_eq,check_eq]
  rfl
theorem run_eq (law : StageReception.Law code) (start : Cursor code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (count : Nat) :
    run vocabulary law (StageTrace.records start stages) receiver count = HeaderReception.run vocabulary law start stages receiver count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change receive vocabulary law (StageTrace.records start stages) receiver count
      (run vocabulary law (StageTrace.records start stages) receiver count) =
      HeaderReception.receive vocabulary law start stages receiver count (HeaderReception.run vocabulary law start stages receiver count)
    rw [ih,receive_eq]

def ledger (rows : List (StageTrace.Record (code := code))) := rows.flatMap fun row =>
  (List.range row.submitted.length).filterMap (StageBudget.issued vocabulary row)
def actorChoices (rows : List (StageTrace.Record (code := code))) (scope : Scope) (actor : Party) : Finset Bool :=
  (Finset.univ : Finset Bool).filter fun value => ∃ row ∈ rows.filter (fun (row : StageTrace.Record (code := code)) => decide (row.before.remaining ≠ 0)),
    ∃ key : Fin code.sites, code.siteParty key = actor ∧ (scope,value) ∈ StageBudget.labels vocabulary row key
def affected (start : Cursor code) (rows : List (StageTrace.Record (code := code))) (scope : Scope) : Finset Party :=
  (ActorEnvelope.roster start.source).filter fun actor =>
    false ∈ actorChoices vocabulary rows scope actor ∧ true ∈ actorChoices vocabulary rows scope actor
def produce (start : Cursor code) (law : StageReception.Law code) (rows : List (StageTrace.Record (code := code)))
    (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
  if ¬ (ActorEnvelope.roster start.source).card + (affected vocabulary start rows scope).card < threshold+threshold then
    .blocked .unsafeSourceBudget
  else match ActorQuorum.readout (run vocabulary law rows receiver rows.length) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem ledger_eq (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    ledger vocabulary (StageTrace.records start stages) = StageBudget.ledger vocabulary start stages := rfl
theorem affected_eq (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) (scope : Scope) :
    affected vocabulary start (StageTrace.records start stages) scope = ActorStageEnvelope.affected start vocabulary stages scope := rfl
theorem produce_eq (start : Cursor code) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) :
    produce vocabulary start law (StageTrace.records start stages) receiver scope threshold =
      HeaderQuorum.produce start vocabulary law stages receiver scope threshold := by
  simp only [produce,affected_eq,StageTrace.record_count,run_eq,HeaderQuorum.produce,
    ActorStageEnvelope.budget,HeaderQuorum.observed]
  rfl

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start : Cursor model.source.code)
variable {model start}
abbrev Cache := CachedCommandRun.Cache model start
variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (law : StageReception.Law model.source.code)

def choices {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) : List (Move model.source.code) :=
  let fresh := CompletionEnvelope.available (OriginQueue.baseline start) cache.before
  let spent := (cache.rows.filter (InterferenceEnvelope.interference start)).length
  let extra := if spent < model.source.code.eventLimit then
    InterferenceEnvelope.externalEvents.filter fun event => decide (event ∉ fresh) else []
  if (CachedCommandRun.ownerAt model cache.cursor cache.before).isSome then [none]
  else match fresh with
    | [] => none :: extra.map some
    | head :: tail => (head :: tail).map some
def within {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (input : LocalCommandSource.Input) : Bool :=
  let rival := (cache.stage input).2
  let raw := if (CachedCommandRun.ownerAt model cache.cursor cache.before).isSome then none
    else rival cache.before.history cache.before.past cache.before.frame
  decide (Distributed.Recall.Information.Agency.externalChoice model.source.code raw ∈ choices cache)
def menu {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) :=
  (CommandWindowSource.menu model).filter (within cache)
def observed {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (receiver : Fin model.source.code.sites) :=
  run vocabulary law cache.rows receiver cache.rows.length
def seen {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (receiver : Fin model.source.code.sites) :=
  ((observed vocabulary law cache receiver).receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))
def delivery {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (input : LocalCommandSource.Input) : Bool :=
  if HeaderDispatch.isDelivery model input then
    (wires vocabulary cache.rows).any fun wire => decide
      (check vocabulary law cache.rows wire.recipient (cache.row input) (seen vocabulary law cache wire.recipient) wire = .accepted wire)
  else false
def sending {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (input : LocalCommandSource.Input) : Bool :=
  if HeaderDispatch.isSend model input then
    match HeaderTransport.issue vocabulary cache.rows (cache.row input) with
    | none => false
    | some wire => decide ((wire.ballot.cut,wire.ballot.position) ∉ seen vocabulary law cache wire.recipient)
  else false
def nextWork (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))
    {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) :=
  work.find? fun request => !(cache.rows.any fun row => (StageTrace.items row).any fun item =>
    decide (item.request = request ∧ model.source.code.law.Valid item.before item.request))
def workingFor {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state)
    (expected : Option (Request Party Good Port (Mandate.State Party Technology) Instrument)) (input : LocalCommandSource.Input) : Bool :=
  match input with
  | .command index => if model.source.code.actions[index]? = expected then
    match expected with
    | none => false
    | some request => let row := cache.row input
      decide (row.submitted = [request] ∧ ∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request)
    else false
  | _ => false
def choose (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))
    {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) : LocalCommandSource.Input :=
  let candidates := menu cache
  ((candidates.find? (delivery vocabulary law cache)).orElse fun _ =>
    (candidates.find? (workingFor cache (nextWork work cache))).orElse fun _ =>
      (candidates.find? (sending vocabulary law cache)).orElse fun _ => candidates.head?).getD .idle

theorem choices_eq {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) :
    choices cache = InterferenceEnvelope.choices start state.stages 0 := by
  have current : cache.before = EventStep.seed (state.current model start) :=
    by rw [cache.before_eq,cache.cursor_eq]
  unfold choices
  rw [current,cache.rows_eq]
  simp only [InterferenceEnvelope.choices,InterferenceEnvelope.extras,InterferenceEnvelope.spent,
    InterferenceEnvelope.fresh,CompletionEnvelope.fresh,CachedCommandRun.ownerAt,cache.cursor_eq,Nat.not_lt_zero,if_false]
  unfold LocalCommandRun.State.current
  congr 1
  split
  · rename_i absent
    conv_rhs => rw (occs := .pos [1]) [absent]
  · rename_i head tail found
    conv_rhs => rw (occs := .pos [1]) [found]
theorem within_eq {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (input : LocalCommandSource.Input) :
    within cache input = DynamicCommandSource.within model start 0 state input := by
  have current : cache.before = EventStep.seed (state.current model start) :=
    by rw [cache.before_eq,cache.cursor_eq]
  unfold within
  rw [current,choices_eq,cache.stage_eq]
  simp only [DynamicCommandSource.within,DynamicCommandSource.intake,InterferenceEnvelope.intake,
    CompletionEnvelope.intake,CompletionEnvelope.raw,EventStep.selected,CachedCommandRun.ownerAt,cache.cursor_eq]
theorem menu_eq {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) :
    menu cache = DynamicCommandSource.menu model start 0 state := by
  unfold menu DynamicCommandSource.menu
  congr 1
  funext input
  exact within_eq cache input
theorem observed_eq {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) (receiver : Fin model.source.code.sites) :
    observed vocabulary law cache receiver = HeaderDispatch.observed model start vocabulary law state receiver := by
  simp only [observed,cache.rows_eq,StageTrace.record_count,run_eq]
theorem choose_eq (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument))
    {state : LocalCommandRun.State model start} (cache : Cache (model := model) (start := start) state) :
    choose vocabulary law work cache = WorkDispatch.choose model start vocabulary law work state := by
  have seen_eq (receiver) : seen vocabulary law cache receiver = HeaderDispatch.seen model start vocabulary law state receiver := by
    simp only [seen,HeaderDispatch.seen,observed_eq]
  have delivery_eq (input) : delivery vocabulary law cache input = HeaderDispatch.delivery model start vocabulary law state input := by
    simp only [delivery,HeaderDispatch.delivery,HeaderDispatch.deliveryTest,cache.rows_eq,wires_eq,check_eq,cache.row_eq,seen_eq]
  have sending_eq (input) : sending vocabulary law cache input = HeaderDispatch.sending model start vocabulary law state input := by
    simp only [sending,HeaderDispatch.sending,HeaderDispatch.sendingTest,cache.rows_eq,cache.row_eq,seen_eq]
    rfl
  have work_eq : nextWork work cache = WorkDispatch.nextWork model start work state := by
    simp only [nextWork,WorkDispatch.nextWork,WorkDispatch.performed,cache.rows_eq]
  have working_eq (expected input) : workingFor cache expected input = WorkDispatch.workingFor model start state expected input := by
    simp only [workingFor,WorkDispatch.workingFor,cache.row_eq]
    rfl
  simp only [choose,WorkDispatch.choose,menu_eq,funext delivery_eq,funext sending_eq,work_eq,funext (working_eq _)]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedWorkDispatch
