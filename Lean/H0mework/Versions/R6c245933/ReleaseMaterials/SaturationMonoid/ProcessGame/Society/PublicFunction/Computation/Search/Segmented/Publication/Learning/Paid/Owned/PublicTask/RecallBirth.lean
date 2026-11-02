import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Provision
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection.Retained

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.RecallBirth
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication
open Local.Inquiry.Planning.Committed

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (request : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev base := request.model.source.code
abbrev capacity := Recall.Provision.capacity (base request) request.budget
abbrev code := Recall.Provision.code (base request) request.budget
abbrev rule := Recall.Provision.rule (base request) request.budget

/-- A new native source at birth; this does not recode an already running cache. -/
def source : Machine Party Good Port (Mandate.State Party Technology) Instrument where
  code := code request
  reference := Recall.Provision.policy (base request) request.budget request.model.source.reference
  reference_generated := Recall.Provision.policy_generated (base request) request.budget request.model.source.reference
    request.model.source.reference_generated
  history := request.model.source.history
  original := by
    rw [(Recall.lifting_preserves_the_original_physical_and_historical_domain (base request) (capacity request)).2.2.1]
    exact request.model.source.original
  opponent := fun _ _ _ => none
  side := .original
  feedback? := some ⟨fun _ _ _ => none,request.budget⟩

def native : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨request.model.base,request.model.scope,source request,request.model.law_exact,request.model.task_exact⟩

def born : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  model := native request
  budget := request.budget
  installed := request.installed.map (rule request)
  original := rule request request.original
  reference := request.reference.map (rule request)
  reader := request.reader
  quote := request.quote
  recoveryRate := request.recoveryRate
  accountingRate := request.accountingRate
  futureRequests := request.futureRequests
  worldInput := request.worldInput
  worldPending := request.worldPending
  vocabulary := request.vocabulary
  encoding := fun signal => request.encoding (Recall.signal (base request) (capacity request) signal)
  law := ⟨request.law.scope,request.law.maxDelay⟩

theorem birth_preserves_the_original_law_history_costs_and_fee :
    (born request).model.source.code.law = request.model.source.code.law ∧
    (born request).model.source.code.initial = request.model.source.code.initial ∧
    (born request).model.source.history = request.model.source.history ∧
    (born request).model.source.code.histories = request.model.source.code.histories ∧
    (born request).model.source.code.sendCost = request.model.source.code.sendCost ∧
    (born request).model.source.code.deliveryCost = request.model.source.code.deliveryCost ∧
    (born request).quote = request.quote := by
  obtain ⟨law,initial,histories,_,send,delivery⟩ :=
    Recall.lifting_preserves_the_original_physical_and_historical_domain (base request) (capacity request)
  exact ⟨law,initial,rfl,histories,send,delivery,rfl⟩

def observed (point : Cursor (code request)) (protocol : Prefix.Rule (code request))
    (rival : Opponent (code request)) (site : Fin (base request).sites) :=
  Recall.Feedback.receipt (base request) (capacity request) (some protocol.work.val)
    (EventStep.applied point protocol rival) (EventStep.seed point) site

def transcript : Cursor (code request) → List (EventHistory.Stage (code := code request)) →
    Fin (base request).sites → List (Recall.Notice (base request))
  | _,[],_ => []
  | point,(protocol,rival) :: rest,site =>
      (observed request point protocol rival site).toList ++ transcript (point.after protocol rival) rest site

private theorem memory_after (point : Cursor (code request)) (protocol : Prefix.Rule (code request))
    (rival : Opponent (code request)) (site : Fin (base request).sites) :
    (EventStep.seed (point.after protocol rival)).frame.inbox site =
      match observed request point protocol rival site with
      | none => (EventStep.seed point).frame.inbox site
      | some atom => Recall.remember (base request) (capacity request) ((EventStep.seed point).frame.inbox site) atom := by
  rw [EventStep.actual_next_state]
  have actual := Recall.Feedback.actual_cut_uses_the_preserved_local_memory (base request) (capacity request)
    (some protocol.work.val) (EventStep.applied point protocol rival) (EventStep.seed point) site
  cases receipt : Recall.Feedback.receipt (base request) (capacity request) (some protocol.work.val)
      (EventStep.applied point protocol rival) (EventStep.seed point) site <;>
    simpa only [observed,receipt] using actual

private theorem remaining_after (point : Cursor (code request)) (protocol : Prefix.Rule (code request))
    (rival : Opponent (code request)) :
    (EventStep.seed (point.after protocol rival)).remaining = (EventStep.seed point).remaining-1 := by
  rw [EventStep.actual_next_state]
  rfl

private theorem observed_supported (point : Cursor (code request)) (protocol : Prefix.Rule (code request))
    (rival : Opponent (code request)) (site : Fin (base request).sites) :
    ∀ atom ∈ (observed request point protocol rival site).toList,atom ∈ Recall.alphabet (base request) := by
  intro atom inside
  cases decided : Reaction.Feedback.decision (code request) (EventStep.applied point protocol rival) (EventStep.seed point) with
  | none => simp only [observed,Recall.Feedback.receipt,decided,Option.toList_none,List.not_mem_nil] at inside
  | some event =>
      exact Recall.notice_is_generated (base request) (capacity request) protocol.work.val protocol.work.property
        (EventStep.seed point).current {(EventStep.seed point).frame with word := []} event.val site atom (by
          simpa only [observed,Recall.Feedback.receipt,decided] using inside)

private theorem observed_requires_a_live_window (point : Cursor (code request)) (protocol : Prefix.Rule (code request))
    (rival : Opponent (code request)) (site : Fin (base request).sites) (atom : Recall.Notice (base request))
    (actual : observed request point protocol rival site = some atom) : (EventStep.seed point).remaining ≠ 0 := by
  intro stopped
  simp only [observed,Recall.Feedback.receipt,Reaction.Feedback.decision,stopped] at actual
  contradiction

private theorem faithful (point : Cursor (code request)) (stages : List (EventHistory.Stage (code := code request)))
    (site : Fin (base request).sites) (prior : List (Recall.Notice (base request)))
    (initial : Recall.decode (base request) (capacity request) ((EventStep.seed point).frame.inbox site) = some prior)
    (generated : prior ∈ Recall.memories (base request) (capacity request))
    (room : prior.length+(EventStep.seed point).remaining ≤ capacity request) :
    Recall.decode (base request) (capacity request)
      ((EventStep.seed (EventHistory.execute point stages)).frame.inbox site) =
        some (prior ++ transcript request point stages site) := by
  induction stages generalizing point prior with
  | nil => simpa only [EventHistory.execute,transcript,List.append_nil] using initial
  | cons stage rest ih =>
      have changed := memory_after request point stage.1 stage.2 site
      have remaining := remaining_after request point stage.1 stage.2
      cases receipt : observed request point stage.1 stage.2 site with
      | none =>
          have next : Recall.decode (base request) (capacity request)
              ((EventStep.seed (point.after stage.1 stage.2)).frame.inbox site) = some prior := by
            rw [changed,receipt]
            exact initial
          have done := ih (point.after stage.1 stage.2) prior next generated (by rw [remaining];omega)
          simpa only [EventHistory.execute,transcript,receipt,Option.toList_none,List.nil_append] using done
      | some atom =>
          have live := observed_requires_a_live_window request point stage.1 stage.2 site atom receipt
          have atomGenerated := observed_supported request point stage.1 stage.2 site atom (by rw [receipt];simp)
          have extended : prior ++ [atom] ∈ Recall.memories (base request) (capacity request) := by
            apply (mem_sequences_iff _ _ _).mpr
            constructor
            · simp only [List.length_append,List.length_singleton]
              omega
            · intro notice inside
              rcases List.mem_append.mp inside with old | fresh
              · exact ((mem_sequences_iff _ _ _).mp generated).2 notice old
              · exact (List.mem_singleton.mp fresh) ▸ atomGenerated
          have next : Recall.decode (base request) (capacity request)
              ((EventStep.seed (point.after stage.1 stage.2)).frame.inbox site) = some (prior ++ [atom]) := by
            simp only [changed,receipt,Recall.remember,initial]
            exact Recall.decode_encode (base request) (capacity request) _ extended
          have done := ih (point.after stage.1 stage.2) (prior ++ [atom]) next extended (by
            simp only [List.length_append,List.length_singleton,remaining]
            omega)
          simpa only [EventHistory.execute,transcript,receipt,Option.toList_some,List.singleton_append,List.append_assoc] using done

def initialHistory (origin : Distributed.Recall.Information.Origin (native request)) (site : Fin (base request).sites) :=
  Recall.Provision.initialHistory (base request) request.budget
    (Distributed.Recall.Information.originSource (native request) request.budget origin) rfl site

theorem every_legal_history_generates_complete_recall_without_a_supplied_capacity_witness
    (origin : Distributed.Recall.Information.Origin (native request))
    (stages : List (EventHistory.Stage (code := code request))) (site : Fin (base request).sites) :
    let point := EventHistory.execute (EventHistory.ofOrigin (native request) request.budget origin) stages
    Recall.decode (base request) (capacity request) ((EventStep.seed point).frame.inbox site) =
      some (initialHistory request origin site ++ transcript request
        (EventHistory.ofOrigin (native request) request.budget origin) stages site) ∧
    (code request).memoryReady ((EventStep.seed point).frame.inbox site) = true := by
  have initial := Recall.Provision.initial_response_generates_its_own_memory (base request) request.budget
    (Distributed.Recall.Information.originSource (native request) request.budget origin) rfl site
  have kept := faithful request (EventHistory.ofOrigin (native request) request.budget origin) stages site
    (initialHistory request origin site) initial.1 initial.2.1 (by
      have bounded := initial.2.2
      change (initialHistory request origin site).length ≤ (base request).eventLimit at bounded
      change _ + request.budget ≤ (base request).eventLimit+request.budget
      omega)
  refine ⟨kept,?_⟩
  change (Recall.decode (base request) (capacity request) _).isSome = true
  exact congrArg Option.isSome kept

private theorem execute_append (point : Cursor (code request))
    (first later : List (EventHistory.Stage (code := code request))) :
    EventHistory.execute point (first ++ later) = EventHistory.execute (EventHistory.execute point first) later := by
  induction first generalizing point with
  | nil => rfl
  | cons stage rest ih =>
      rcases stage with ⟨protocol,rival⟩
      exact ih _

private theorem execute_controls (point : Cursor (code request)) (rival : Opponent (code request))
    (controls : List (Prefix.Rule (code request))) :
    EventHistory.execute point (controls.map fun protocol => (protocol,rival)) = Splice.install point rival controls := by
  induction controls generalizing point with
  | nil => rfl
  | cons protocol rest ih => exact ih _

theorem every_actual_continuation_retains_its_complete_birth_record
    (origin : Distributed.Recall.Information.Origin (native request))
    (stages : List (EventHistory.Stage (code := code request))) (rival : Opponent (code request))
    (controls : List (Prefix.Rule (code request))) (site : Fin (base request).sites) :
    let start := EventHistory.ofOrigin (native request) request.budget origin
    let final := Splice.install (EventHistory.execute start stages) rival controls
    Recall.decode (base request) (capacity request) ((EventStep.seed final).frame.inbox site) =
      some (initialHistory request origin site ++ transcript request start
        (stages ++ controls.map fun protocol => (protocol,rival)) site) ∧
    (code request).memoryReady ((EventStep.seed final).frame.inbox site) = true := by
  have complete := every_legal_history_generates_complete_recall_without_a_supplied_capacity_witness request origin
    (stages ++ controls.map fun protocol => (protocol,rival)) site
  dsimp only at complete ⊢
  have same := (execute_append request (EventHistory.ofOrigin (native request) request.budget origin)
    stages (controls.map fun protocol => (protocol,rival))).trans
      (execute_controls request _ rival controls)
  exact same ▸ complete

theorem every_prior_raw_request_has_its_actual_native_birth_source
    (index : Nat) (inside : index < request.model.source.history.length) :
    ((native request).source.actualExecution index).submitted =
      (request.model.source.actualExecution index).submitted := by
  exact (Machine.history_word_is_actual (native request).source index inside).trans
    (Machine.history_word_is_actual request.model.source index inside).symm

variable {request}
def memory {signal : Fin (code request).signals}
    {fits : (born request).reference.length ≤ horizon (PublicTask.domain (born request) signal)}
    {quotas : List Nat} {point : Cursor (code request)} {rival : Opponent (code request)}
    (choice : Prefix.Choice (born request).model (PublicTask.domain (born request) signal) (born request).original
      (PaidSearch.fees (born request) quotas) (PaidSearch.reference (born request) signal fits)) :
    Local.Inquiry.Planning.Committed.CompleteSelection.Observation.Memory
      (Feedback.task (born request) signal fits quotas point rival choice) :=
  ⟨base request,capacity request,rfl⟩

variable (request)

def produce (quotas : List Nat) (point : Cursor (code request)) (rival : Opponent (code request))
    (localRounds : Nat) (sender : Fin (code request).sites) (rounds : Nat) :=
  Local.Inquiry.Planning.Committed.CompleteSelection.Execution.Public.produce
    (born request) quotas point rival localRounds sender rounds

variable (quotas : List Nat) (rival : Opponent (code request))
  (localRounds : Nat) (sender : Fin (code request).sites) (rounds : Nat)

def StrategyContract
    (point : Cursor (code request))
    (prior : CompleteSelection.Execution.Public.Prior (born request) quotas point rival localRounds)
    (next : CompleteSelection.Execution.Public.Follow (born request) quotas point rival localRounds sender rounds prior) : Prop :=
  match prior,next with
  | .inherited _,_ => True
  | .installed fits _ _ choice _ actual _,next =>
      let task := Feedback.task (born request) _ fits quotas point rival choice
      CompleteSelection.Observation.WalkContract task (memory (request := request) choice) next.generated ∧
      CompleteSelection.Execution.Runtime.read task (CompleteSelection.compile task)
        (Local.Inquiry.Frame.pack actual.1) sender rounds next next.controls.length = some next

theorem all_legal_histories_generate_native_paid_complete_history_strategies
    (origin : Distributed.Recall.Information.Origin (native request))
    (stages : List (EventHistory.Stage (code := code request)))
    (installed : stages.map Prod.fst = (born request).installed) :
    let point := EventHistory.execute (EventHistory.ofOrigin (native request) request.budget origin) stages
    let made := produce request quotas point rival localRounds sender rounds
    CompleteSelection.Execution.Public.Sound (born request) quotas point rival localRounds sender rounds made.1 made.2 ∧
    CompleteSelection.Retained.Public.Contract (born request) quotas point rival localRounds sender rounds made.1 made.2 ∧
    StrategyContract request quotas rival localRounds sender rounds point made.1 made.2 := by
  refine ⟨CompleteSelection.Execution.Public.all_legal_public_histories_generate_complete_paid_chains_with_original_responsibility
    (born request) quotas rival localRounds sender rounds origin stages installed,
    CompleteSelection.Retained.Public.all_legal_public_histories_generate_executed_whole_chain_nondomination
      (born request) quotas rival localRounds sender rounds origin stages installed,?_⟩
  have coverage (point : Cursor (code request))
      (prior : CompleteSelection.Execution.Public.Prior (born request) quotas point rival localRounds) :
      StrategyContract request quotas rival localRounds sender rounds point prior
        (CompleteSelection.Execution.Public.follow (born request) quotas point rival localRounds sender rounds prior) := by
    cases prior with
    | inherited => trivial
    | installed fits work released choice selected actual generated =>
        constructor
        · exact CompleteSelection.Observation.the_complete_actual_feedback_walk_has_full_observation_strategy_coverage
            _ (memory (request := request) choice) _
        · exact CompleteSelection.Execution.Runtime.the_final_named_read_releases_its_source_generated_outcome _ _ _ _ _ _
  exact coverage _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.RecallBirth
