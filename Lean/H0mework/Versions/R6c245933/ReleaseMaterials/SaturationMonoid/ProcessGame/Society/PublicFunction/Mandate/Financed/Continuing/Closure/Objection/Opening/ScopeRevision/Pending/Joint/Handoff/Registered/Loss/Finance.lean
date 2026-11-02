import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Finance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting
noncomputable section
local notation "sources" => Pending.Joint.Finance.sources
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} {authority : ScopeRevision.Ready old}
  {originInputs : List (List Action)} {inventory : Pending.Joint.Inventory authority originInputs}
  {fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs} {original : List Action}

variable (cursor : Cursor authority inventory fresh original)
def visits := cursor.book.map Entry.visit
def events := ((visits cursor).map fun receipt => (receipt.native sources).events).flatten

theorem accept_visits (word : List Action) : visits (cursor.accept word) = visits cursor ++ [Loss.visit cursor.state word] :=
  cursor.every_actual_input_keeps_all_prior_origins_and_adds_its_own word

theorem accept_events (word : List Action) : events (cursor.accept word) =
    events cursor ++ (Continuation.financialRun cursor.state word).events := by
  simp only [events,accept_visits,List.map_append,List.map_singleton,List.flatten_append,List.flatten_singleton]
  rfl

theorem accept_current (word : List Action) : (cursor.accept word).before = (law fresh).next cursor.before word := by
  change (OutstandingSource.History.replay (source fresh) (cursor.state.inputs ++ [word])).frame.raw = _
  simp only [OutstandingSource.History.replay,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

theorem visit_raw (word : List Action) : Registered.Finance.raw (Loss.visit cursor.state word) = (law fresh).rawItems cursor.before word := by
  have same := Loss.new_visit_is_the_original_actual_law_current_and_input cursor.state word
  rw [← cursor.before_is_the_same_actual_current] at same
  change Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.items
    (Loss.occurrence (Loss.visit cursor.state word)) = _
  rw [same]
  rfl

def adjusted (actor : Bool) (good : Good) := cursor.before.stock actor good +
  Registered.Finance.quantity (visits cursor) false actor good - Registered.Finance.quantity (visits cursor) true actor good

theorem accept_adjusted (word : List Action) (actor : Bool) (good : Good) :
    adjusted (cursor.accept word) actor good = adjusted cursor actor good := by
  have material : ((law fresh).next cursor.before word).stock actor good +
      ((Registered.Finance.raw (Loss.visit cursor.state word)).map fun item =>
        Registered.Finance.flow (Loss.visit cursor.state word) item false actor good).sum =
      cursor.before.stock actor good + ((Registered.Finance.raw (Loss.visit cursor.state word)).map fun item =>
        Registered.Finance.flow (Loss.visit cursor.state word) item true actor good).sum := by
    rw [visit_raw]
    exact (law fresh).actual_next_material_balance cursor.before word actor good
  unfold adjusted
  rw [accept_current,accept_visits]
  simp only [Registered.Finance.quantity,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
  linarith only [material]

theorem reaction_adjusted (actor party : Bool) (good : Good) :
    adjusted (Source.reaction cursor actor) party good = adjusted cursor party good := by
  unfold Source.reaction
  split
  · rfl
  · exact accept_adjusted _ _ _ _

theorem advance_adjusted (actor : Bool) (good : Good) :
    adjusted (Source.advance cursor) actor good = adjusted cursor actor good := by
  unfold Source.advance
  split
  · rw [reaction_adjusted]
    exact accept_adjusted _ _ _ _
  · exact accept_adjusted _ _ _ _
  · exact accept_adjusted _ _ _ _

private theorem local_partition (receipt : Registered.Finance.Visit) (incoming : Bool) (actor : Bool) (good : Good) :
    ((Registered.Finance.raw receipt).map fun item => Registered.Finance.cashAt receipt item true incoming actor good).sum +
    ((Registered.Finance.raw receipt).map fun item => Registered.Finance.cashAt receipt item false incoming actor good).sum +
      atVisit sources (receipt.window sources) (if incoming then .credit else .debit) actor good =
    ((Registered.Finance.raw receipt).map fun item => Registered.Finance.flow receipt item incoming actor good).sum := by
  unfold atVisit rawTotal
  change _ + _ + ((Registered.Finance.raw receipt).map fun item => rawAmount sources receipt.sourceIndex item
    (if incoming then .credit else .debit) actor good).sum = _
  induction Registered.Finance.raw receipt with
  | nil => simp
  | cons item rest ih =>
    simp only [List.map_cons,List.sum_cons] at *
    have cashHead : Registered.Finance.cashAt receipt item true incoming actor good + Registered.Finance.cashAt receipt item false incoming actor good =
        if PublicFunction.Costs.isDebtPayment item.request then 0 else Registered.Finance.flow receipt item incoming actor good := by
      unfold Registered.Finance.cashAt
      cases debt : PublicFunction.Costs.isDebtPayment item.request <;>
        cases choice : Registered.Finance.selected receipt item.index <;> simp_all only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true,add_zero,zero_add]
    have nativeHead : (if PublicFunction.Costs.isDebtPayment item.request then 0 else Registered.Finance.flow receipt item incoming actor good) +
        rawAmount sources receipt.sourceIndex item (if incoming then .credit else .debit) actor good =
        Registered.Finance.flow receipt item incoming actor good := by
      cases operation : item.request.operation <;> cases incoming <;>
        simp only [PublicFunction.Costs.isDebtPayment,operation,rawAmount,Registered.Finance.flow,Bool.false_eq_true,if_false,if_true,add_zero,zero_add]
    linarith only [cashHead,nativeHead,ih]

private theorem receipt_sum (entries : List Registered.Finance.Visit) (incoming : Bool) (actor : Bool) (good : Good) :
    Registered.Finance.cash entries true incoming actor good + Registered.Finance.cash entries false incoming actor good +
      Financial.Family.Migration.Posting.total sources (entries.map (VisitReceipt.window sources))
        (if incoming then .credit else .debit) actor good = Registered.Finance.quantity entries incoming actor good := by
  induction entries with
  | nil => simp [Registered.Finance.cash,Registered.Finance.quantity,Financial.Family.Migration.Posting.total]
  | cons receipt rest ih =>
    have head := local_partition receipt incoming actor good
    simp only [Registered.Finance.cash,Registered.Finance.quantity,List.map_cons,List.sum_cons,Financial.Family.Migration.Posting.total] at *
    linarith only [head,ih]

def HistoryExact : Prop := cursor.state.finance.current.history =
  (Registered.Finance.before authority inventory).current.history ++ events cursor

theorem accept_history (word : List Action) (prior : HistoryExact cursor) : HistoryExact (cursor.accept word) := by
  have step := (Continuation.financialRun cursor.state word).history_eq
  change (cursor.accept word).state.finance.current.history = _ at step
  unfold HistoryExact at prior ⊢
  rw [step,prior,accept_events,List.append_assoc]

theorem reaction_history (actor : Bool) (prior : HistoryExact cursor) : HistoryExact (Source.reaction cursor actor) := by
  unfold Source.reaction
  split
  · exact prior
  · exact accept_history _ _ prior

theorem advance_history (prior : HistoryExact cursor) : HistoryExact (Source.advance cursor) := by
  have next : HistoryExact cursor.next := accept_history cursor cursor.word prior
  unfold Source.advance
  split
  · exact reaction_history cursor.next _ next
  · exact next
  · exact next

variable (authority inventory fresh original) (count : Nat)
def run := (Registered.Finance.run authority inventory fresh original).concatRuns _
  (Source.runFinancial (Loss.initial authority inventory fresh original) count)
def entries := visits (Loss.cursorAt authority inventory fresh original count)
@[irreducible] def funded := Financial.Family.Migration.Funding.fold sources
  (run authority inventory fresh original count) (Registered.Finance.book authority inventory)
def charge := Financial.Family.Migration.FinancingBook.Posting.nativeCharge sources (funded authority inventory fresh original count)
def account (side : Bool) (actor : Bool) (good : Good) :=
  Registered.Finance.cash (entries authority inventory fresh original count) side false actor good -
    Registered.Finance.cash (entries authority inventory fresh original count) side true actor good +
    charge authority inventory fresh original count side actor good

theorem initial_visits : visits (Loss.initial authority inventory fresh original) = Registered.Finance.entries authority inventory fresh original := by
  change ((Registered.Finance.entries authority inventory fresh original).map Entry.ofVisit).map Entry.visit = _
  rw [List.map_map]
  change (Registered.Finance.entries authority inventory fresh original).map id = _
  exact List.map_id _

theorem every_actual_visit_has_exactly_its_original_native_events :
    ((entries authority inventory fresh original count).map fun receipt => (receipt.native sources).events).flatten =
      (run authority inventory fresh original count).events := by
  have first : HistoryExact (Loss.initial authority inventory fresh original) := by
    have originalHistory := (Registered.Finance.run authority inventory fresh original).history_eq
    change (Loss.initial authority inventory fresh original).state.finance.current.history = _ at originalHistory
    unfold HistoryExact events
    rw [initial_visits,(Registered.Finance.every_visit_and_native_event_is_the_original_actual_interval authority inventory fresh original).2]
    exact originalHistory
  have all : HistoryExact (Loss.cursorAt authority inventory fresh original count) := by
    induction count with
    | zero => exact first
    | succ count ih => exact advance_history _ ih
  have native := (run authority inventory fresh original count).history_eq
  exact List.append_cancel_left (all.symm.trans native)

theorem every_actual_material_item_balances_the_same_original_endpoints (actor : Bool) (good : Good) :
    (Loss.cursorAt authority inventory fresh original count).before.stock actor good +
      Registered.Finance.quantity (entries authority inventory fresh original count) false actor good =
    (PublicFunction.Costs.Visits.rawAt sources (Registered.input authority inventory fresh original) 0).stock actor good +
      Registered.Finance.quantity (entries authority inventory fresh original count) true actor good := by
  have preserved : adjusted (Loss.cursorAt authority inventory fresh original count) actor good =
      adjusted (Loss.initial authority inventory fresh original) actor good := by
    induction count with
    | zero => rfl
    | succ count ih => exact (advance_adjusted _ actor good).trans ih
  have before : (Loss.initial authority inventory fresh original).before = Registered.final authority inventory fresh original :=
    (Loss.initial authority inventory fresh original).before_is_the_same_actual_current
  have originalMaterial := Registered.Finance.all_original_raw_items_balance_the_same_actual_material_endpoints authority inventory fresh original actor good
  simp only [adjusted,initial_visits,before] at preserved
  unfold entries
  linarith only [preserved,originalMaterial]

theorem every_actual_payment_has_one_cash_or_native_leg (incoming : Bool) (actor : Bool) (good : Good) :
    Registered.Finance.cash (entries authority inventory fresh original count) true incoming actor good +
      Registered.Finance.cash (entries authority inventory fresh original count) false incoming actor good +
      runAmount sources (run authority inventory fresh original count) (if incoming then .credit else .debit) actor good =
    Registered.Finance.quantity (entries authority inventory fresh original count) incoming actor good := by
  have originalSum := receipt_sum (entries authority inventory fresh original count) incoming actor good
  have native : total sources ((entries authority inventory fresh original count).map (VisitReceipt.window sources))
      (if incoming then .credit else .debit) actor good = runAmount sources (run authority inventory fresh original count)
        (if incoming then .credit else .debit) actor good := by
    have sumVisits (receipts : List Registered.Finance.Visit) :
        total sources (receipts.map (VisitReceipt.window sources)) (if incoming then .credit else .debit) actor good =
          (receipts.map fun receipt => atVisit sources (receipt.window sources) (if incoming then .credit else .debit) actor good).sum := by
      induction receipts with
      | nil => rfl
      | cons receipt rest ih => simp only [List.map_cons,total,List.sum_cons,ih]
    rw [sumVisits]
    unfold runAmount
    rw [← every_actual_visit_has_exactly_its_original_native_events]
    simp only [List.map_map,List.map_flatten,List.sum_flatten]
    apply congrArg List.sum
    apply List.map_congr_left
    intro receipt _
    exact (receipt.exact_amount sources _ actor good).symm
  rw [native] at originalSum
  exact originalSum

def quotedBefore (actor : Bool) (good : Good) := Registered.Finance.quotedBefore authority inventory fresh original actor good
def quotedAfter (actor : Bool) (good : Good) :=
  (Loss.cursorAt authority inventory fresh original count).before.stock actor good +
  Balance.position sources (Loss.cursorAt authority inventory fresh original count).state.finance.current .credit actor good -
  Balance.position sources (Loss.cursorAt authority inventory fresh original count).state.finance.current .debit actor good

theorem the_complete_continuation_net_has_one_original_start_and_actual_end (actor : Bool) (good : Good) :
    account authority inventory fresh original count true actor good + account authority inventory fresh original count false actor good =
      quotedBefore authority inventory fresh original actor good - quotedAfter authority inventory fresh original count actor good := by
  have debit := every_actual_payment_has_one_cash_or_native_leg authority inventory fresh original count false actor good
  have credit := every_actual_payment_has_one_cash_or_native_leg authority inventory fresh original count true actor good
  have material := every_actual_material_item_balances_the_same_original_endpoints authority inventory fresh original count actor good
  have native := Financial.Family.Migration.FinancingBook.Posting.nativeCharge_partition sources
    (funded authority inventory fresh original count) actor good
  change charge authority inventory fresh original count true actor good + charge authority inventory fresh original count false actor good = _ at native
  simp only [Bool.false_eq_true,if_false,if_true] at debit credit
  unfold account quotedBefore quotedAfter Registered.Finance.quotedBefore
  simp only [Loss.cursorAt] at material ⊢
  linarith only [debit,credit,material,native]

theorem every_original_financial_slot_and_event_is_in_the_same_full_run :
    (funded authority inventory fresh original count).after.cells.map Financial.Family.Migration.FinancingBook.Cell.slot =
      (Loss.cursorAt authority inventory fresh original count).state.finance.current.slots ∧
    (funded authority inventory fresh original count).rows.map Financial.Family.Migration.FinancingBook.Row.native =
      (run authority inventory fresh original count).events :=
  ⟨(funded authority inventory fresh original count).after.slots_exact,(funded authority inventory fresh original count).events_exact⟩

structure Data where
  private mk ::
  first : ResponsibilityState (Financial.Family.vocabulary sources)
  last : ResponsibilityState (Financial.Family.vocabulary sources)
  native : (Financial.Family.process sources).Run first last
  opening : Financial.Family.Migration.FinancingBook.Book sources first
  result : Financial.Family.Migration.FinancingBook.Flow sources native opening

def produce : Data :=
  ⟨(Registered.Finance.before authority inventory).current,
    (Loss.cursorAt authority inventory fresh original count).state.finance.current,
    run authority inventory fresh original count,Registered.Finance.book authority inventory,
    funded authority inventory fresh original count⟩
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Finance
