import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Admission
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Reception
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private theorem record_after_is_the_exact_delivery_prefix (start : Cursor code)
    (stages : List (EventHistory.Stage (code := code))) (index : Nat)
    (row : StageTrace.Record (code := code)) (found : (StageTrace.records start stages)[index]? = some row) :
    row.after = EventStep.seed (EventHistory.execute start (stages.take (index+1))) := by
  induction stages generalizing start index with
  | nil => simp only [StageTrace.records,List.getElem?_nil] at found;cases found
  | cons stage rest ih =>
    rcases stage with ⟨rule,rival⟩
    cases index with
    | zero =>
      simp only [StageTrace.records,List.getElem?_cons_zero] at found
      cases Option.some.inj found
      exact (StageTrace.material_is_the_actual_step start rule rival).1
    | succ index =>
      simp only [StageTrace.records,List.getElem?_cons_succ] at found
      simpa only [List.take_succ_cons,EventHistory.execute] using ih (start.after rule rival) index found

private theorem actual_view_has_the_executed_point (controls : List (Prefix.Rule code))
    (point : View (code := code)) (rival : Opponent code) :
    (Window.Observed.Transcript.actualView controls point rival).point =
      EventHistory.execute point.point (controls.map (fun rule => (rule,rival))) := by
  induction controls generalizing point with
  | nil => rfl
  | cons rule rest ih => exact ih (Evidence.after point rule rival)

variable (point : View (code := code)) (rival : Opponent code)
  (reader : Fin code.sites)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (past : List (Prefix.Rule code)) (previous : Nat)

abbrev stages := past.map (fun rule => (rule,rival))
abbrev observed := RequestReadback.produce vocabulary encoding law point.point (stages rival past) reader past.length

/-- Poll the cumulative actual trace, but consume only a delivery at this newly
executed stage. Earlier sends may arrive now; an earlier receipt is not reused. -/
def fresh := (observed point rival reader vocabulary encoding law past).receipts.filter
  (fun receipt => decide (previous ≤ receipt.confirmation.index ∧ receipt.confirmation.index+1 = past.length))

theorem mem_fresh_iff (receipt : RequestReadback.Receipt (code := code)) :
    receipt ∈ fresh point rival reader vocabulary encoding law past previous ↔
      receipt ∈ (observed point rival reader vocabulary encoding law past).receipts ∧
      previous ≤ receipt.confirmation.index ∧ receipt.confirmation.index+1 = past.length := by
  simp only [fresh,List.mem_filter,decide_eq_true_eq]

inductive Outcome where
  | silent (absent : fresh point rival reader vocabulary encoding law past previous = [])
  | received (first : RequestReadback.Receipt (code := code))
      (rest : List (RequestReadback.Receipt (code := code)))
      (exactly : fresh point rival reader vocabulary encoding law past previous = first :: rest)

def generate : Outcome point rival reader vocabulary encoding law past previous :=
  match found : fresh point rival reader vocabulary encoding law past previous with
  | [] => .silent found
  | first :: rest => .received first rest found

theorem a_new_receipt_reads_this_exact_actual_cut
    (receipt : RequestReadback.Receipt (code := code))
    (inside : receipt ∈ fresh point rival reader vocabulary encoding law past previous) :
    observation (Window.Observed.Transcript.actualView past point rival) reader = receipt.reading := by
  obtain ⟨included,_,latest⟩ := (mem_fresh_iff point rival reader vocabulary encoding law past previous receipt).mp inside
  obtain ⟨_,_,_,_,row,found,reading,_,_⟩ :=
    RequestReadback.recovered_requests_have_paid_communication_complete_source_and_local_readback
      vocabulary encoding law point.point (stages rival past) reader past.length receipt included
  have actual := record_after_is_the_exact_delivery_prefix point.point (stages rival past) receipt.confirmation.index row found
  rw [latest] at actual
  change row.after = EventStep.seed (EventHistory.execute point.point ((past.map (fun rule => (rule,rival))).take past.length)) at actual
  rw [←List.map_take,List.take_length] at actual
  change (EventStep.seed (Window.Observed.Transcript.actualView past point rival).point).frame.inbox reader = _
  rw [actual_view_has_the_executed_point,←actual]
  exact reading.symm

def condition (receipts : List (RequestReadback.Receipt (code := code)))
    (beliefs : List (View (code := code))) :=
  receipts.foldl (fun views receipt => fiber views reader receipt.reading) beliefs

theorem condition_only_removes_existing_beliefs
    (receipts : List (RequestReadback.Receipt (code := code)))
    (beliefs : List (View (code := code))) :
    ∀ view ∈ condition reader receipts beliefs, view ∈ beliefs := by
  induction receipts generalizing beliefs with
  | nil => exact fun _ inside => inside
  | cons receipt rest ih =>
      intro view inside
      exact ((mem_fiber _ _ _ _).mp (ih _ view inside)).1

theorem every_actual_new_receipt_preserves_actual_knowledge
    (beliefs : List (View (code := code)))
    (covered : Knowledge.Contains beliefs (Window.Observed.Transcript.actualView past point rival)) :
    Knowledge.Contains (condition reader (fresh point rival reader vocabulary encoding law past previous) beliefs)
      (Window.Observed.Transcript.actualView past point rival) := by
  have preserve (receipts : List (RequestReadback.Receipt (code := code)))
      (all : ∀ receipt ∈ receipts, observation (Window.Observed.Transcript.actualView past point rival) reader = receipt.reading)
      (views : List (View (code := code)))
      (contains : Knowledge.Contains views (Window.Observed.Transcript.actualView past point rival)) :
      Knowledge.Contains (condition reader receipts views) (Window.Observed.Transcript.actualView past point rival) := by
    induction receipts generalizing views with
    | nil => exact contains
    | cons receipt rest ih =>
        have updated := Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain _ _ contains reader
        rw [all receipt (List.mem_cons_self)] at updated
        exact ih (fun body inside => all body (List.mem_cons_of_mem _ inside)) _ updated
  exact preserve _ (fun receipt inside => a_new_receipt_reads_this_exact_actual_cut point rival reader vocabulary encoding law past previous receipt inside) beliefs covered

theorem no_new_stage_cannot_reuse_an_old_receipt
    (unchanged : past.length ≤ previous) :
    fresh point rival reader vocabulary encoding law past previous = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro receipt inside
  have bounds := ((mem_fresh_iff point rival reader vocabulary encoding law past previous receipt).mp inside).2
  omega

theorem a_consumed_packet_cannot_reappear_in_a_later_stage
    (later : List (Prefix.Rule code)) (laterStart : Nat)
    (ordered : past.length ≤ laterStart)
    (receipt : RequestReadback.Receipt (code := code))
    (consumed : receipt ∈ fresh point rival reader vocabulary encoding law past previous) :
    receipt ∉ fresh point rival reader vocabulary encoding law later laterStart := by
  intro repeated
  have first := ((mem_fresh_iff point rival reader vocabulary encoding law past previous receipt).mp consumed).2
  have second := ((mem_fresh_iff point rival reader vocabulary encoding law later laterStart receipt).mp repeated).2
  omega

variable {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}

/-- Only beliefs change. The already accepted programme and all actual resource
attempts remain the same; subsequent requests consume the refined state. -/
def refresh (point : View (code := model.source.code)) (rival : Opponent model.source.code)
    (reader : Fin model.source.code.sites)
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
    (previous : Nat) (state : Publication.Learning.Paid.State model domain original baseline actualHorizon) :=
  {state with beliefs := condition reader (fresh point rival reader vocabulary encoding law state.past previous) state.beliefs}

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Reception
