import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Continuation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.Reparation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
open Financial.Family.Migration.Posting
noncomputable section
local notation "sources" => Pending.Joint.Finance.sources

def occurrence (visit : Finance.Visit) : Raw.Occurrence Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(sources visit.sourceIndex).law,(Finance.origin visit).1,(Finance.origin visit).2⟩

structure Entry where
  private mk ::
  visit : Finance.Visit
  account : Raw.Reparation.Account (occurrence visit)

def Entry.original (entry : Entry) := occurrence entry.visit
def Entry.ofVisit (visit : Finance.Visit) : Entry := ⟨visit,Raw.Reparation.initial (occurrence visit)⟩
def Entry.advance (entry : Entry) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) : Entry :=
  ⟨entry.visit,Raw.Reparation.advance entry.original entry.account law before⟩
def Entry.change (entry : Entry) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) (key : Bool × Good) :=
  (entry.advance law before).account.paid key - entry.account.paid key

abbrev Book := List Entry
def pending (book : Book) := (List.finRange book.length).filter fun index =>
  !(Raw.Reparation.orders (book.get index).original (book.get index).account).isEmpty
def selected (book : Book) := (pending book).head?
def word (book : Book) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) : List Action :=
  match selected book with
  | none => []
  | some index => Raw.Reparation.word (book.get index).original (book.get index).account law before

def update (book : Book) (index : Fin book.length) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) : Book :=
  book.set index.val ((book.get index).advance law before)
def allocate (book : Book) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) : Book :=
  match selected book with
  | none => book
  | some index => update book index law before

private abbrev operationDecidableEq : DecidableEq (Operation Bool Good (State Bool Unit) Unit) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq Action := by
  letI := operationDecidableEq
  intro left right
  cases left
  cases right
  simp only [Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

def accept (book : Book) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) (submitted : List Action) : Book :=
  if submitted = word book law before then allocate book law before else book

theorem allocation_keeps_each_original_visit (book : Book) (index : Fin book.length)
    (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) :
    (update book index law before).map Entry.visit = book.map Entry.visit := by
  simp only [update,List.map_set,Entry.advance]
  have same : (book.get index).visit = (book.map Entry.visit)[index.val]'(by rw [List.length_map]; exact index.isLt) := by simp
  rw [same]
  exact List.set_getElem_self (by rw [List.length_map]; exact index.isLt)

theorem acceptance_keeps_all_original_visits (book : Book)
    (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) (submitted : List Action) :
    (accept book law before submitted).map Entry.visit = book.map Entry.visit := by
  unfold accept
  split
  · unfold allocate
    split
    · rfl
    · exact allocation_keeps_each_original_visit _ _ _ _
  · rfl

theorem every_other_position_is_literal (book : Book) (index other : Fin book.length)
    (different : index.val ≠ other.val) (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) :
    (update book index law before)[other.val]'(by simpa only [update,List.length_set] using other.isLt) = book.get other := by
  simp only [update,List.getElem_set_ne different,List.get_eq_getElem]

theorem the_selected_position_has_its_original_actual_allocation (book : Book) (index : Fin book.length)
    (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current) :
    (update book index law before)[index.val]'(by simpa only [update,List.length_set] using index.isLt) =
      (book.get index).advance law before := by simp only [update,List.getElem_set_self]

theorem every_positive_allocation_has_the_same_actual_transfer (book : Book) (index : Fin book.length)
    (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit) (before : Current)
    (chosen : selected book = some index) (key : Bool × Good)
    (positive : 0 < (book.get index).change law before key) :
    ∃ order : Raw.Reparation.Order (book.get index).original (book.get index).account,
      word book law before = [order.request law before] ∧ key = order.key ∧ law.Valid before (order.request law before) ∧
      (book.get index).change law before key ≤ flowAt (law.actualCredit before (order.request law before)) key.1 key.2 := by
  have amount : (book.get index).change law before key =
      Raw.Reparation.applied (book.get index).original (book.get index).account law before key := by
    simp only [Entry.change,Entry.advance,Raw.Reparation.advance,add_sub_cancel_left]
  rw [amount] at positive ⊢
  obtain ⟨order,selectedOrder,cell,valid,bound⟩ :=
    Raw.Reparation.every_positive_allocation_is_bounded_by_its_same_actual_transfer_credit _ _ _ _ _ positive
  exact ⟨order,by simp only [word,chosen,Raw.Reparation.word,selectedOrder],cell,valid,bound⟩

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (original : List Action)

def initialBook : Book := (Finance.entries authority inventory fresh original).map Entry.ofVisit

variable {authority inventory fresh original}
def visit (saved : Continuation.Inventory authority inventory fresh original) (submitted : List Action) : Finance.Visit :=
  receive sources (Handoff.Continuation.inputAt fresh (saved.inputs ++ [submitted])) (saved.inputs.length+2) saved.finance
    (saved.compatible _) (by
      change Financial.Family.ledgerClaims sources saved.finance.current =
        (OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [submitted]) (saved.inputs.length+2)).claims
      have same : OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [submitted]) (saved.inputs.length+2) =
          Handoff.Continuation.currentAt fresh saved.inputs :=
        Mandate.Challenge.Cross.emitted_word_uses_actual_cut (newBound fresh) saved.inputs submitted
      rw [same]
      exact saved.matrix)

theorem new_visit_is_the_original_actual_law_current_and_input
    (saved : Continuation.Inventory authority inventory fresh original) (submitted : List Action) :
    occurrence (visit saved submitted) = (⟨law fresh,Handoff.Continuation.currentAt fresh saved.inputs,submitted⟩ :
      Raw.Occurrence Bool Good Mandate.Source.Port (State Bool Unit) Unit) := by
  have actual := Continuation.actual_word_and_cut saved submitted
  change (⟨law fresh,(Continuation.actual saved submitted).before,(Continuation.actual saved submitted).submitted⟩ :
    Raw.Occurrence Bool Good Mandate.Source.Port (State Bool Unit) Unit) = _
  rw [actual.1,actual.2]

variable (authority inventory fresh original)
structure Cursor where
  private mk ::
  state : Continuation.Inventory authority inventory fresh original
  book : Book

def initial : Cursor authority inventory fresh original :=
  ⟨Continuation.initial authority inventory fresh original,initialBook authority inventory fresh original⟩

variable {authority inventory fresh original}
namespace Cursor
variable (cursor : Cursor authority inventory fresh original)
def before := (OutstandingSource.History.replay (source fresh) cursor.state.inputs).frame.raw

theorem before_is_the_same_actual_current :
    cursor.before = Handoff.Continuation.currentAt fresh cursor.state.inputs :=
  (OutstandingSource.History.all_finite_inputs_reach_their_own_actual_current
    (source fresh) cursor.state.inputs).1.symm
def word := Loss.word cursor.book (law fresh) cursor.before
def accept (submitted : List Action) : Cursor authority inventory fresh original :=
  ⟨Continuation.submit cursor.state submitted,
    Loss.accept cursor.book (law fresh) cursor.before submitted ++ [Entry.ofVisit (visit cursor.state submitted)]⟩
def next := cursor.accept cursor.word
def actual := Continuation.actual cursor.state cursor.word

theorem selected_reparation_is_the_literal_source_execution :
    cursor.actual.submitted = cursor.word ∧ cursor.actual.before = cursor.before :=
  ⟨(Continuation.actual_word_and_cut _ _).1,
    (Continuation.actual_word_and_cut _ _).2.trans cursor.before_is_the_same_actual_current.symm⟩

theorem every_actual_input_keeps_all_prior_origins_and_adds_its_own (submitted : List Action) :
    (cursor.accept submitted).book.map Entry.visit = cursor.book.map Entry.visit ++ [visit cursor.state submitted] := by
  simp only [accept,List.map_append,List.map_singleton,Entry.ofVisit,acceptance_keeps_all_original_visits]

theorem unmatched_input_does_not_allocate_old_accounts (submitted : List Action) (different : submitted ≠ cursor.word) :
    (cursor.accept submitted).book = cursor.book ++ [Entry.ofVisit (visit cursor.state submitted)] := by
  have mismatch : submitted ≠ Loss.word cursor.book (law fresh) cursor.before := different
  simp only [accept,Loss.accept,if_neg mismatch]

theorem all_original_and_new_cells_keep_their_original_quantities (entry : Entry) (_member : entry ∈ cursor.book) (key : Bool × Good) :
    entry.account.remaining key + entry.account.paid key = Raw.quantity entry.original key := entry.account.balance key

theorem each_actual_reparation_keeps_the_original_paid_past :
    Registered.inputs authority inventory fresh original <+: cursor.next.state.inputs := cursor.next.state.paidPast

def financialRun : (Financial.Family.process sources).Run cursor.state.finance.current cursor.next.state.finance.current :=
  Continuation.financialRun _ _

theorem a_positive_allocation_is_its_actual_accepted_current_law_transfer
    (index : Fin cursor.book.length) (chosen : selected cursor.book = some index) (key : Bool × Good)
    (positive : 0 < (cursor.book.get index).change (law fresh) cursor.before key) :
    ∃ order : Raw.Reparation.Order (cursor.book.get index).original (cursor.book.get index).account,
      cursor.actual.submitted = [order.request (law fresh) cursor.actual.before] ∧ key = order.key ∧
      (law fresh).Valid cursor.actual.before (order.request (law fresh) cursor.actual.before) ∧
      (cursor.book.get index).change (law fresh) cursor.before key ≤
        flowAt ((law fresh).actualCredit cursor.actual.before (order.request (law fresh) cursor.actual.before)) key.1 key.2 := by
  rw [cursor.selected_reparation_is_the_literal_source_execution.1,cursor.selected_reparation_is_the_literal_source_execution.2]
  exact every_positive_allocation_has_the_same_actual_transfer _ _ _ _ chosen key positive
end Cursor

def run (cursor : Cursor authority inventory fresh original) : Nat → Cursor authority inventory fresh original
  | 0 => cursor
  | count+1 => (run cursor count).next

def runFinancial (cursor : Cursor authority inventory fresh original) : (count : Nat) →
    (Financial.Family.process sources).Run cursor.state.finance.current (run cursor count).state.finance.current
  | 0 => .nil
  | count+1 => (runFinancial cursor count).concatRuns _ (run cursor count).financialRun

theorem every_finite_reparation_preserves_every_old_origin (cursor : Cursor authority inventory fresh original) (count : Nat) :
    cursor.book.map Entry.visit <+: (run cursor count).book.map Entry.visit := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ count ih =>
      have step := (run cursor count).every_actual_input_keeps_all_prior_origins_and_adds_its_own (run cursor count).word
      change _ <+: ((run cursor count).next).book.map Entry.visit
      rw [show ((run cursor count).next).book.map Entry.visit =
        (run cursor count).book.map Entry.visit ++ [visit (run cursor count).state (run cursor count).word] from step]
      exact ih.trans (List.prefix_append _ _)
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss
