import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.PaidSearch

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Feedback
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (request : Request (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (signal : Fin request.model.source.code.signals)
  (fits : request.reference.length ≤ horizon (domain request signal)) (quotas : List Nat)
  (point : Cursor request.model.source.code) (rival : Opponent request.model.source.code)

private theorem scan_budget {before : View (code := request.model.source.code)}
    {cache : Option (Focused.Sparse.Cache request.model (domain request signal) request.original
      (PaidSearch.reference request signal fits) request.reader request.quote quotas)} {jobs : List Nat}
    (execution : Focused.Sparse.Scan request.model (domain request signal) request.original
      (PaidSearch.reference request signal fits) request.reader request.quote quotas rival before cache jobs) :
    execution.rules.length ≤ (Cut.seed before.point).remaining := by
  induction execution with
  | empty | stopped => exact Nat.zero_le _
  | next before prior quota rest consumed later ih =>
      have positive : (Cut.seed before.point).remaining ≠ 0 := by
        intro empty
        simp only [Charge.trace,dif_pos empty,Cut.Trace.rules] at consumed
        cases consumed
      have actual := (Charge.trace request.quote request.reader before rival).final_is_generated_only_by_its_actual_single_cut_rules
      rw [consumed] at actual
      have remaining : (Cut.seed (Charge.trace request.quote request.reader before rival).final.point).remaining =
          (Cut.seed before.point).remaining-1 := by
        rw [actual]
        exact Installation.Chain.after_remaining (model := request.model) before.point _ rival
      change later.rules.length+1 ≤ _
      rw [remaining] at ih
      omega

variable (work : Focused.Sparse.Finished request.model (domain request signal) request.original
  (PaidSearch.reference request signal fits) request.reader request.quote quotas)
  (released : PaidSearch.finished request signal fits quotas point rival = some work)
  (choice : Prefix.Choice request.model (domain request signal) request.original
    (PaidSearch.fees request quotas) (PaidSearch.reference request signal fits))

include released in
theorem the_released_search_fits_its_own_actual_seed_window :
    (PaidSearch.fees request quotas).length ≤ (Cut.seed point).remaining := by
  have bounded := scan_budget request signal fits quotas rival (PaidSearch.execution request signal fits quotas point rival)
  have emitted := (PaidSearch.every_completed_search_keeps_the_entire_original_reference_and_fee_prefix work released).1
  change (PaidSearch.scanRules request signal fits quotas point rival).length ≤ (Cut.seed point).remaining at bounded
  rw [emitted] at bounded
  exact bounded

/-- The old responsibility origin stays attached while its actual fee prefix grows. -/
def paidView := Window.Observed.Transcript.actualView (PaidSearch.fees request quotas) (currentView point) rival

def paidBeliefs :=
  fiber (Window.Observed.Transcript.publicViews (PaidSearch.fees request quotas)
    (fiber (views request) request.reader signal)) request.reader
    (observation (paidView request quotas point rival) request.reader)

abbrev task : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  model := request.model
  domain := domain request signal
  original := request.original
  baseline := choice.policy.protocol
  point := currentView point
  rival := rival
  reader := request.reader
  quote := request.quote
  recoveryRate := request.recoveryRate
  accountingRate := request.accountingRate
  futureRequests := request.futureRequests
  worldInput := request.worldInput
  worldPending := request.worldPending
  vocabulary := request.vocabulary
  encoding := request.encoding
  law := request.law
  continueUnreserved := true
  initialVerifier := Thunk.mk fun _ => .isTrue (Prefix.Commitment.admissible_plan_is_its_own_valid_reference
    request.model (domain request signal) request.original _ _ choice.policy.accepted)

/-- The seed is built inside the paid source, never supplied as a successful input. -/
def seed : Cache (task request signal fits quotas point rival choice) where
  past := PaidSearch.fees request quotas
  programme := choice.policy.protocol
  beliefs := paidBeliefs request signal quotas point rival
  within := work.room
  actualWithin := the_released_search_fits_its_own_actual_seed_window request signal fits quotas point rival work released
  retained := Prefix.the_selected_plan_really_preserves_the_committed_control_prefix
    request.model (domain request signal) request.original (PaidSearch.fees request quotas)
    (PaidSearch.reference request signal fits) choice work.room
  above := Prefix.Commitment.admissible_plan_is_its_own_valid_reference
    request.model (domain request signal) request.original _ _ choice.policy.accepted

variable {request signal fits quotas point rival}

theorem the_seed_preserves_the_actual_old_origin :
    ((seed request signal fits quotas point rival work released choice).current (currentView point) rival).origin.val =
      (currentView point).origin.val := by
  change (Window.Observed.Transcript.actualView (PaidSearch.fees request quotas) (currentView point) rival).origin.val = _
  have preserved (rules : List (Prefix.Rule request.model.source.code)) (view : View (code := request.model.source.code)) :
      (Window.Observed.Transcript.actualView rules view rival).origin.val = view.origin.val := by
    induction rules generalizing view with
    | nil => rfl
    | cons rule tail ih => exact ih _
  exact preserved _ _

include released in
theorem the_seed_starts_at_the_actual_paid_point :
    ((seed request signal fits quotas point rival work released choice).current (currentView point) rival).point =
      PaidSearch.paidPoint request signal fits quotas point rival := by
  have actual := Paid.State.current_is_the_actual_control_prefix
    (seed request signal fits quotas point rival work released choice)
    (task request signal fits quotas point rival choice).point (task request signal fits quotas point rival choice).rival
  change (Window.Observed.Transcript.actualView (PaidSearch.fees request quotas) (currentView point) rival).point = _
  exact actual.trans (PaidSearch.every_completed_search_keeps_the_entire_original_reference_and_fee_prefix work released).2.1.symm

theorem the_seed_keeps_actual_local_knowledge
    (covered : Knowledge.Contains (fiber (views request) request.reader signal) (currentView point)) :
    Knowledge.Contains (seed request signal fits quotas point rival work released choice).beliefs
      ((seed request signal fits quotas point rival work released choice).current (currentView point) rival) := by
  exact Prefix.Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain _ _
    (Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
      (PaidSearch.fees request quotas) _ _ covered rival) request.reader

variable (rounds : Nat)

abbrev evolved := Owned.trace (task request signal fits quotas point rival choice) rounds
  (seed request signal fits quotas point rival work released choice)

/-- Already paid controls remain the literal prefix of every later actual word. -/
theorem no_initial_search_fee_is_replayed_or_erased :
    (evolved work released choice rounds).1.past = PaidSearch.fees request quotas ++
      Owned.executed (task request signal fits quotas point rival choice) rounds
        (seed request signal fits quotas point rival work released choice) := by
  simp only [evolved,Owned.trace_is_the_original_run_and_reports]
  exact Owned.the_whole_run_locks_every_actual_fee_wait_and_selected_stage _ _ _

theorem every_later_feedback_preserves_original_responsibility_and_knowledge
    (covered : Knowledge.Contains (fiber (views request) request.reader signal) (currentView point)) :
    Selection.acceptable request.model (domain request signal) request.original
      (PaidSearch.reference request signal fits) (evolved work released choice rounds).1.programme ∧
    Knowledge.Contains (evolved work released choice rounds).1.beliefs
      ((evolved work released choice rounds).1.current (currentView point) rival) := by
  constructor
  · exact Selection.acceptable_trans request.model (domain request signal) request.original _ _ _
      (evolved work released choice rounds).1.above choice.policy.accepted
  · simp only [evolved,Owned.trace_is_the_original_run_and_reports]
    exact Owned.the_whole_run_preserves_actual_origin_knowledge _ _ _
      (the_seed_keeps_actual_local_knowledge work released choice covered)

private theorem nondomination_survives {Policy Axis : Type} (axes : List Axis) (benefit : Policy → Axis → ℚ)
    (old next other : Policy) (maximal : ¬ Distributed.Improves axes benefit old other)
    (above : Distributed.NoWorse axes benefit next old) : ¬ Distributed.Improves axes benefit next other := by
  intro strict
  exact maximal ⟨Distributed.noWorse_trans strict.1 above,
    fun reverse => strict.2 (Distributed.noWorse_trans above reverse)⟩

theorem every_later_feedback_keeps_the_entire_original_paid_pool_nondominated
    (other : Prefix.Candidate request.model (domain request signal) request.original
      (PaidSearch.fees request quotas) (PaidSearch.reference request signal fits))
    (inside : other ∈ Prefix.candidates request.model (domain request signal) request.original
      (PaidSearch.fees request quotas) (PaidSearch.reference request signal fits)) :
    ¬ Distributed.Improves (Selection.axes (fuel := horizon (domain request signal)) request.model (domain request signal))
      (Selection.benefit request.model (domain request signal) request.original)
      (evolved work released choice rounds).1.programme other.protocol :=
  nondomination_survives _ _ _ _ _ (choice.maximal other inside)
    (Selection.acceptance_bounds_every_benefit request.model (domain request signal) request.original _ _
      (evolved work released choice rounds).1.above)

theorem every_existing_strict_net_improvement_survives_feedback
    (strict : Distributed.Improves (Selection.axes (fuel := horizon (domain request signal)) request.model (domain request signal))
      (Selection.benefit request.model (domain request signal) request.original)
      (PaidSearch.reference request signal fits) choice.policy.protocol) :
    Distributed.Improves (Selection.axes (fuel := horizon (domain request signal)) request.model (domain request signal))
      (Selection.benefit request.model (domain request signal) request.original)
      (PaidSearch.reference request signal fits) (evolved work released choice rounds).1.programme := by
  have above := Selection.acceptance_bounds_every_benefit request.model (domain request signal) request.original _ _
    (evolved work released choice rounds).1.above
  exact ⟨Distributed.noWorse_trans above strict.1,
    fun reverse => strict.2 (Distributed.noWorse_trans reverse above)⟩

variable (request quotas point rival)

inductive Output where
  | absent (empty : fiber (views request) request.reader (observation (currentView point) request.reader) = [])
  | overBudget (long : horizon (domain request (observation (currentView point) request.reader)) < request.reference.length)
  | unavailable (fits : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)))
      (why : PaidSearch.Failure request (observation (currentView point) request.reader) fits quotas point rival)
  | rejected (fits : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)))
      (work : Focused.Sparse.Finished request.model (domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.reference request _ fits) request.reader request.quote quotas)
      (released : PaidSearch.finished request _ fits quotas point rival = some work) (empty : work.choice = none)
  | continued (fits : request.reference.length ≤ horizon (domain request (observation (currentView point) request.reader)))
      (work : Focused.Sparse.Finished request.model (domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.reference request _ fits) request.reader request.quote quotas)
      (released : PaidSearch.finished request _ fits quotas point rival = some work)
      (choice : Prefix.Choice request.model (domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.fees request quotas) (PaidSearch.reference request _ fits)) (selected : work.choice = some choice)
      (actual : Cache (task request _ fits quotas point rival choice) × List Report)
      (generated : actual = evolved work released choice rounds)

def produce : Output request quotas point rival rounds :=
  match PaidSearch.produce request quotas point rival with
  | .absent empty => .absent empty
  | .overBudget long => .overBudget long
  | .scanned fits (.unavailable why) => .unavailable fits why
  | .scanned fits (.completed work released) =>
      match seen : work.choice with
      | none => .rejected fits work released seen
      | some choice => .continued fits work released choice seen (evolved work released choice rounds) rfl

structure Occurrence where
  generated : Output request quotas point rival rounds
  exact_generation : generated = produce request quotas point rival rounds

def occurrence : Occurrence request quotas point rival rounds := ⟨produce request quotas point rival rounds,rfl⟩

namespace Occurrence
variable {request quotas point rival rounds}
def controls (made : Occurrence request quotas point rival rounds) := match made.generated with
  | .absent .. | .overBudget .. => []
  | .unavailable fits .. | .rejected fits .. => PaidSearch.scanRules request _ fits quotas point rival
  | .continued _ _ _ _ _ actual _ => actual.1.past
end Occurrence


namespace Output
variable {request quotas point rival rounds}
def search : Output request quotas point rival rounds → PaidSearch.PublicResult request quotas point rival
  | .absent empty => .absent empty
  | .overBudget long => .overBudget long
  | .unavailable fits why => .scanned fits (.unavailable why)
  | .rejected fits work released _ | .continued fits work released .. => .scanned fits (.completed work released)

def controls : Output request quotas point rival rounds → List (Prefix.Rule request.model.source.code)
  | .absent .. | .overBudget .. => []
  | .unavailable fits .. | .rejected fits .. => PaidSearch.scanRules request _ fits quotas point rival
  | .continued _ _ _ _ _ actual _ => actual.1.past

def Sound : Output request quotas point rival rounds → Prop
  | .absent .. => False
  | .overBudget .. | .unavailable .. | .rejected .. => True
  | .continued fits _ _ _ _ actual _ =>
      Selection.acceptable request.model (domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.reference request _ fits) actual.1.programme ∧
      Knowledge.Contains actual.1.beliefs (actual.1.current (currentView point) rival) ∧
      (∃ suffix, actual.1.past = PaidSearch.fees request quotas ++ suffix) ∧
      (∀ other ∈ Prefix.candidates request.model (domain request (observation (currentView point) request.reader))
        request.original (PaidSearch.fees request quotas) (PaidSearch.reference request _ fits),
        ¬ Distributed.Improves
          (Selection.axes (fuel := horizon (domain request (observation (currentView point) request.reader)))
            request.model (domain request (observation (currentView point) request.reader)))
          (Selection.benefit request.model (domain request (observation (currentView point) request.reader)) request.original)
          actual.1.programme other.protocol)
end Output

/-- No future feedback result influences the source's initial paid choice. -/
theorem the_initial_search_projection_is_independent_of_later_feedback :
    (produce request quotas point rival rounds).search = PaidSearch.produce request quotas point rival := by
  unfold produce
  cases PaidSearch.produce request quotas point rival with
  | absent | overBudget => rfl
  | scanned fits result =>
      cases result with
      | unavailable => rfl
      | completed work released =>
          dsimp only
          split <;> rfl

theorem all_origins_and_finite_histories_generate_paid_origin_preserving_feedback
    (request : Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed)
    (rival : Opponent request.model.source.code) (quotas : List Nat) (rounds : Nat) :
    (produce request quotas (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages) rival rounds).Sound := by
  have covered := every_actual_receipt_has_a_complete_local_source request origin stages installed
  unfold produce
  cases made : PaidSearch.produce request quotas
      (EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages) rival with
  | absent empty =>
      have real := PaidSearch.all_origins_and_finite_adaptive_histories_generate_a_paid_search_or_precise_obstruction
        request origin stages installed rival quotas
      rw [made] at real
      exact real
  | overBudget => trivial
  | scanned fits result =>
      cases result with
      | unavailable => trivial
      | completed work released =>
          dsimp only
          split
          · trivial
          · rename_i choice picked
            have preserved :=  every_later_feedback_preserves_original_responsibility_and_knowledge
              work released choice rounds covered
            refine ⟨preserved.1,preserved.2,?_,?_⟩
            · exact ⟨_,no_initial_search_fee_is_replayed_or_erased work released choice rounds⟩
            · exact every_later_feedback_keeps_the_entire_original_paid_pool_nondominated work released choice rounds

namespace Output
variable {request quotas point rival rounds}
def paidControls : Output request quotas point rival rounds → List (Prefix.Rule request.model.source.code)
  | .absent .. | .overBudget .. => []
  | .unavailable fits .. | .rejected fits .. | .continued fits .. => PaidSearch.scanRules request _ fits quotas point rival

theorem controls_extend_the_same_actual_paid_search (result : Output request quotas point rival rounds) :
    ∃ suffix, result.controls = result.paidControls ++ suffix := by
  cases result with
  | absent | overBudget => exact ⟨[],rfl⟩
  | unavailable | rejected => exact ⟨[],(List.append_nil _).symm⟩
  | continued fits work released choice selected actual generated =>
      change ∃ suffix, actual.1.past = PaidSearch.scanRules request _ fits quotas point rival ++ suffix
      rw [generated]
      rw [(PaidSearch.every_completed_search_keeps_the_entire_original_reference_and_fee_prefix work released).1]
      exact ⟨_,no_initial_search_fee_is_replayed_or_erased work released choice rounds⟩
end Output

abbrev full := Splice.install point rival (produce request quotas point rival rounds).controls

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Feedback
