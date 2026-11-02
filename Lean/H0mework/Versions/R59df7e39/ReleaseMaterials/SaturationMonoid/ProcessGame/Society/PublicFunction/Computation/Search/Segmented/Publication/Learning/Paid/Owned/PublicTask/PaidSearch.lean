import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Deployment.Path

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.PaidSearch
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private theorem execute_with_one_opponent (point : Cursor code) (rules : List (Prefix.Rule code))
    (rival : Opponent code) :
    EventHistory.execute point (rules.map fun rule => (rule,rival)) = Splice.install point rival rules := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih _

private theorem execute_append (point : Cursor code)
    (first later : List (EventHistory.Stage (code := code))) :
    EventHistory.execute point (first ++ later) = EventHistory.execute (EventHistory.execute point first) later := by
  induction first generalizing point with
  | nil => rfl
  | cons stage tail ih => exact ih _

variable (request : Request (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (signal : Fin request.model.source.code.signals)
  (fits : request.reference.length ≤ horizon (domain request signal)) (quotas : List Nat)

abbrev reference : Program request.model.source.code (horizon (domain request signal)) := ⟨request.reference,fits⟩
abbrev fees := Focused.Sparse.reserved request.model request.original request.reader request.quote quotas

variable (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code)

/-- The initial work queue is generated only by the original paid scanner. -/
def execution := Focused.Sparse.trace request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival

abbrev paidPoint := (execution request signal fits quotas point rival).final.point
abbrev scanRules := (execution request signal fits quotas point rival).rules
abbrev endAt := arrival (paidPoint request signal fits quotas point rival)

def nextRequest : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  {request with installed := request.installed ++ scanRules request signal fits quotas point rival}

/-- The public history grows by the actual fee attempts; it does not import a private outcome. -/
theorem the_payment_history_generates_its_own_next_public_request
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed)
    (actual : point = EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages) :
    Knowledge.Contains
      (fiber (views (nextRequest request signal fits quotas point rival)) request.reader
        (observation (currentView (paidPoint request signal fits quotas point rival)) request.reader))
      (currentView (paidPoint request signal fits quotas point rival)) := by
  let later := (scanRules request signal fits quotas point rival).map fun rule => (rule,rival)
  have source := (execution request signal fits quotas point rival).the_actual_source_contains_exactly_the_executed_fee_prefix
  have final : paidPoint request signal fits quotas point rival =
      EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) (stages ++ later) := by
    rw [execute_append,←actual]
    exact source.1.trans (execute_with_one_opponent point _ rival).symm
  have history : (stages ++ later).map Prod.fst = (nextRequest request signal fits quotas point rival).installed := by
    simp [List.map_append,List.map_map,Function.comp_def,later,installed,nextRequest]
  have generated := every_actual_receipt_has_a_complete_local_source
    (nextRequest request signal fits quotas point rival) origin (stages ++ later) history
  dsimp only [nextRequest] at generated
  rw [←final] at generated
  exact generated

abbrev finished := Focused.Sparse.result request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival

abbrev scanRoot := Focused.Sparse.Runtime.facade request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival

abbrev deployed := Focused.Sparse.Deployment.full request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival
    (endAt request signal fits quotas point rival)

/-- This fixed facade installs the source-selected suffix, or the actual unsuccessful payment prefix. -/
abbrev facade := Focused.Sparse.Deployment.Path.facade request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival
    (endAt request signal fits quotas point rival)

abbrev Failure := Focused.Sparse.CloseReason request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival
  (execution request signal fits quotas point rival)

inductive Result where
  | unavailable (why : Failure request signal fits quotas point rival)
  | completed (work : Focused.Sparse.Finished request.model (domain request signal) request.original
      (reference request signal fits) request.reader request.quote quotas)
      (released : finished request signal fits quotas point rival = some work)

def generate : Result request signal fits quotas point rival :=
  match seen : finished request signal fits quotas point rival with
  | none => .unavailable (Focused.Sparse.closing_obstruction request.model (domain request signal) request.original
      (reference request signal fits) request.reader request.quote quotas (currentView point) rival
      (execution request signal fits quotas point rival) seen)
  | some work => .completed work seen

variable {request signal fits quotas point rival}

theorem no_unpaid_search_can_enter_the_initial_queue
    (unpaid : (execution request signal fits quotas point rival).payments = []) :
    (execution request signal fits quotas point rival).cached = none := by
  have replayed := (execution request signal fits quotas point rival).the_entire_cache_replays_only_its_own_ordered_actual_paid_slots
  rw [unpaid] at replayed
  exact replayed

variable (work : Focused.Sparse.Finished request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas)
  (released : finished request signal fits quotas point rival = some work)

include released in
theorem every_completed_search_replays_only_its_actual_paid_work :
    Focused.Sparse.replayPayments request.model (domain request signal) request.original (reference request signal fits)
      request.reader request.quote quotas rival none
      (execution request signal fits quotas point rival).payments = some work.work ∧
    ∃ closing, (execution request signal fits quotas point rival).closingReceipt = some closing :=
  Focused.Sparse.a_released_finished_cache_is_its_actual_payment_replay_and_has_a_closing_receipt
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas (currentView point) rival work released

include released in
theorem every_completed_search_keeps_the_entire_original_reference_and_fee_prefix :
    scanRules request signal fits quotas point rival = fees request quotas ∧
    paidPoint request signal fits quotas point rival = Splice.install point rival (fees request quotas) ∧
    quotas.length ≤ horizon (domain request signal) :=
  Focused.Sparse.a_released_result_has_executed_the_entire_fixed_fee_plan
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas (currentView point) rival work released

variable (choice : Prefix.Choice request.model (domain request signal) request.original
  (fees request quotas) (reference request signal fits)) (selected : work.choice = some choice)

include selected in
theorem the_paid_source_selects_a_fully_reviewable_original_completion :
    Prefix.Contract request.model (domain request signal) request.original (fees request quotas)
      (reference request signal fits) (.selected choice) :=
  Focused.Sparse.a_selected_cache_has_the_complete_independently_reviewable_contract
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas work choice selected

include released in
private theorem arrived :
    Focused.Sparse.Runtime.read request.model (domain request signal) request.original (reference request signal fits)
      request.reader request.quote quotas (currentView point) rival (endAt request signal fits quotas point rival) =
      some (execution request signal fits quotas point rival,some work) := by
  rw [Focused.Sparse.Runtime.read_is_the_arrived_source_generated_outcome]
  simp only [Focused.Sparse.Runtime.available,execution,endAt,paidPoint,le_refl,ite_true]
  exact congrArg (fun closed => some (Focused.Sparse.trace request.model (domain request signal) request.original
    (reference request signal fits) request.reader request.quote quotas (currentView point) rival,closed)) released

include released selected in
theorem the_paid_source_executes_the_new_suffix_without_repaying_the_scan :
    deployed request signal fits quotas point rival = Splice.install point rival
      (Focused.Sparse.Deployment.completeControls request.model (domain request signal) request.original (currentView point) choice.policy.protocol) :=
  Focused.Sparse.Deployment.the_actual_deployment_is_the_entire_selected_window_without_repaying_its_prefix
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas (currentView point) rival (endAt request signal fits quotas point rival)
    (execution request signal fits quotas point rival) work choice (arrived work released) selected

include released selected in
theorem the_actual_deployment_is_the_complete_original_evaluated_source :
    (deployed request signal fits quotas point rival).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point request.original
        (clip (Focused.Sparse.Deployment.actualHorizon request.model (currentView point)) choice.policy.protocol) rival).input :=
  Focused.Sparse.Deployment.the_installed_input_is_the_complete_original_evaluated_input
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas (currentView point) rival (endAt request signal fits quotas point rival)
    (execution request signal fits quotas point rival) work choice (arrived work released) selected


def the_completed_negative_answer_retains_every_original_failure_row
    (empty : work.choice = none) (raw : Program request.model.source.code (horizon (domain request signal))) :
    Selection.Rejection request.model (domain request signal) request.original (reference request signal fits)
      (Prefix.extension (horizon (domain request signal)) (fees request quotas) raw) :=
  Focused.Sparse.the_failed_paid_cache_returns_the_stored_original_failure
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas work empty raw

variable (request signal fits quotas point rival)

abbrev cutPoint (count : Nat) := Focused.Sparse.Deployment.Path.cutPoint request.model (domain request signal) request.original
  (reference request signal fits) request.reader request.quote quotas (currentView point) rival
  (endAt request signal fits quotas point rival) count

abbrev current (count : Nat) := (facade request signal fits quotas point rival).seed.advance count

def RootConsumption : Prop := ∀ (count : Nat) (face : Focused.Sparse.Deployment.Path.Face),
  let node := current request signal fits quotas point rival count
  HEq ((facade request signal fits quotas point rival).readoutAt node face)
    (node.tick.generated.projectionOutcome
      (((facade request signal fits quotas point rival).installationAt node face).embed
        ((facade request signal fits quotas point rival).projectionAt node face))) ∧
  HEq node.tick.generated.wholeLedgerWriteBack
    (node.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt node.current.visit.current) ∧
  node.tick.nextCurrent = (facade request signal fits quotas point rival).process.stateAt
    ((facade request signal fits quotas point rival).process.successor node.state)

theorem the_same_original_root_consumes_all_closed_faces_and_its_own_next :
    RootConsumption request signal fits quotas point rival := by
  intro count face
  have same := (facade request signal fits quotas point rival).readoutAt_factorizes
    (current request signal fits quotas point rival count) face
  exact ⟨same.2.2.2.1,same.2.2.1,same.2.2.2.2⟩

def NativePrefix : Prop := ∀ (count visit : Nat),
  visit ≤ arrival (cutPoint request signal fits quotas point rival count) →
  Native.Coupling.Match request.model.source.code
    (cutPoint request signal fits quotas point rival count).source.input
    (deployed request signal fits quotas point rival).source.input
    (Financial.accountAt (cutPoint request signal fits quotas point rival count).source.input visit)
    (Financial.accountAt (deployed request signal fits quotas point rival).source.input visit)

theorem every_actual_cut_keeps_its_complete_original_financial_prefix :
    NativePrefix request signal fits quotas point rival :=
  Focused.Sparse.Deployment.Path.each_actual_prefix_preserves_its_entire_native_financial_account
    request.model (domain request signal) request.original (reference request signal fits)
    request.reader request.quote quotas (currentView point) rival (endAt request signal fits quotas point rival)

inductive PublicResult (request : Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
    (quotas : List Nat) (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code) where
  | absent (empty : fiber (views request) request.reader (observation (currentView point) request.reader) = [])
  | overBudget (long : horizon (domain request (observation (currentView point) request.reader)) < request.reference.length)
  | scanned (fits : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)))
      (result : Result request (observation (currentView point) request.reader) fits quotas point rival)

/-- No planner, successful cache or proof of payment is an input to this producer. -/
def produce : PublicResult request quotas point rival :=
  if empty : fiber (views request) request.reader (observation (currentView point) request.reader) = [] then .absent empty
  else if bounded : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)) then
    .scanned bounded (generate request (observation (currentView point) request.reader) bounded quotas point rival)
  else .overBudget (Nat.lt_of_not_ge bounded)

variable {request signal fits quotas point rival}

structure Contract : Prop where
  nextKnowledge : Knowledge.Contains
    (fiber (views (nextRequest request signal fits quotas point rival)) request.reader
      (observation (currentView (paidPoint request signal fits quotas point rival)) request.reader))
    (currentView (paidPoint request signal fits quotas point rival))
  noFreeCache : (execution request signal fits quotas point rival).payments = [] →
    (execution request signal fits quotas point rival).cached = none
  root : RootConsumption request signal fits quotas point rival
  finance : NativePrefix request signal fits quotas point rival
  completed : ∀ work, finished request signal fits quotas point rival = some work →
    (Focused.Sparse.replayPayments request.model (domain request signal) request.original (reference request signal fits)
      request.reader request.quote quotas rival none (execution request signal fits quotas point rival).payments = some work.work) ∧
    (∃ closing, (execution request signal fits quotas point rival).closingReceipt = some closing) ∧
    (scanRules request signal fits quotas point rival = fees request quotas) ∧
    (∀ choice, work.choice = some choice →
      Prefix.Contract request.model (domain request signal) request.original (fees request quotas)
        (reference request signal fits) (.selected choice) ∧
      (deployed request signal fits quotas point rival).source.input =
        (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point request.original
          (clip (Focused.Sparse.Deployment.actualHorizon request.model (currentView point)) choice.policy.protocol) rival).input)

def PublicResult.Sound : PublicResult request quotas point rival → Prop
  | .absent _ => False
  | .overBudget _ => True
  | .scanned fits _ => Contract (request := request) (signal := observation (currentView point) request.reader)
      (fits := fits) (quotas := quotas) (point := point) (rival := rival)

theorem all_origins_and_finite_adaptive_histories_generate_a_paid_search_or_precise_obstruction
    (request : Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed)
    (rival : Opponent request.model.source.code) (quotas : List Nat) :
    (produce request quotas (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages) rival).Sound := by
  let point := EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages
  have covered := every_actual_receipt_has_a_complete_local_source request origin stages installed
  unfold produce
  split
  · rename_i empty
    obtain ⟨representative,inside,_⟩ := covered
    rw [empty] at inside
    cases inside
  · split
    · rename_i fits
      refine ⟨the_payment_history_generates_its_own_next_public_request request _ fits quotas point rival origin stages installed rfl,
        no_unpaid_search_can_enter_the_initial_queue,
        the_same_original_root_consumes_all_closed_faces_and_its_own_next request _ fits quotas point rival,
        every_actual_cut_keeps_its_complete_original_financial_prefix request _ fits quotas point rival,?_⟩
      intro work released
      obtain ⟨replayed,closing⟩ := every_completed_search_replays_only_its_actual_paid_work work released
      have paidHistory := every_completed_search_keeps_the_entire_original_reference_and_fee_prefix work released
      refine ⟨replayed,closing,paidHistory.1,?_⟩
      intro choice selected
      exact ⟨the_paid_source_selects_a_fully_reviewable_original_completion work choice selected,
        the_actual_deployment_is_the_complete_original_evaluated_source work released choice selected⟩
    · trivial

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.PaidSearch
