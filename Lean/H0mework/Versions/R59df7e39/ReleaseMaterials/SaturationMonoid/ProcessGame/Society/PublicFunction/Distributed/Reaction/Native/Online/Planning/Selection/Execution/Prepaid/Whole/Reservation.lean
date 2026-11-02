import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Work
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Reservation
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {baseReference : Term cursor} {actor : Party} {position : Nat}
  (scope : Scope cursor pricing n baseReference actor position) (span : Nat)

structure Ticket where
  private mk ::
  probe : Prefix.Bill (paidPoint scope) actor position
  probe_before : probe.before = scope.continuation.words
  probe_units : probe.units = Work.workBudget scope span
  bill : Prefix.Bill (paidPoint scope) actor position
  bill_before : bill.before = scope.continuation.words
  bill_units : bill.units = max (Work.workBudget scope span)
    (Work.workBudget (Whole.extend scope probe probe_before) span)

namespace Ticket
variable {scope span} (ticket : Ticket scope span)
abbrev reserved := Whole.extend scope ticket.bill ticket.bill_before
abbrev needed := Work.workBudget ticket.reserved span

theorem actual_invoice_is_the_last_native_word_of_the_committed_prefix :
    ((comparisonPoint ticket.reserved).source.val.actualExecution (comparisonPoint scope).depth).submitted =
      ticket.bill.payment.output := by
  have emitted := Prefix.at_word (paidPoint scope)
    (scope.continuation.words ++ [ticket.bill.payment.output]) scope.continuation.words.length (by simp)
  have depth := Prefix.at_depth (paidPoint scope) scope.continuation.words
  have words : ticket.reserved.continuation.words = scope.continuation.words ++ [ticket.bill.payment.output] := by
    exact scope.continuation.append_words ticket.bill ticket.bill_before
  change ((Prefix.pointFor (paidPoint scope) ticket.reserved.continuation.words).source.val.actualExecution
    (comparisonPoint scope).depth).submitted = _
  rw [words,depth]
  simpa only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero] using emitted

end Ticket

def propose : Option (Ticket scope span) :=
  match Prefix.quote (paidPoint scope) actor position scope.continuation.words (Work.workBudget scope span) with
  | none => none
  | some quoted =>
    let units := max (Work.workBudget scope span)
      (Work.workBudget (Whole.extend scope quoted.val quoted.property.1) span)
    some ⟨quoted.val,quoted.property.1,quoted.property.2,quoted.val.reprice units,quoted.property.1,rfl⟩

structure Ready (ticket : Ticket scope span) where
  private mk ::
  paid : ticket.bill.payment.succeeded = true
  covered : ticket.needed ≤ ticket.bill.units
  compilation : Work.Compilation ticket.reserved span .keep
  compiled : compilation = Work.compileFunded ticket.reserved span
  receipt : Work.Receipt ticket.reserved span compilation
  work : List (Work.Operation ticket.reserved)
  work_exact : work = Work.checkedWork ticket.reserved span compilation

namespace Ready
variable {scope span} {ticket : Ticket scope span} (ready : Ready scope span ticket)

theorem the_whole_comparison_and_independent_verifier_fit_the_already_paid_invoice :
    Work.controlSteps ticket.reserved ready.work ≤ ticket.bill.units := by
  rw [ready.work_exact,ready.compiled]
  exact (Work.funded_selection_verification_and_rejection_fit_the_generated_budget _ _).trans ready.covered

theorem the_cached_review_and_actual_release_fit_the_already_paid_invoice :
    Work.controlSteps ticket.reserved ready.receipt.work ≤ ticket.bill.units := by
  rcases ready with ⟨paid,covered,compilation,compiled,receipt,work,work_exact⟩
  subst compilation
  exact (Work.receipt_release_fits_the_same_generated_budget ticket.reserved span .keep
    (Work.fundedOrder ticket.reserved) (Work.fundedOrder_complete ticket.reserved) receipt).trans covered

def endpoint : Cursor seed driver := match ready.receipt.authorized with
  | none => comparisonPoint ticket.reserved
  | some choice => match choice.policy.term with
    | .keep => comparisonPoint ticket.reserved
    | .paid term => Whole.execute ticket.reserved span (.paid term)

theorem the_release_reads_the_same_paid_compilation_and_cached_review :
    ready.receipt.review.value = true ∧
    ready.receipt.comparisonWork = ready.work := by
  exact ⟨ready.receipt.review_accepts_its_generated_result,
    ready.receipt.comparisonWork_exact.trans ready.work_exact.symm⟩

theorem a_kept_result_proves_every_paid_continuation_inadmissible
    (choice : Decision.Choice ticket.reserved span .keep)
    (selected : ready.compilation.result = .selected choice) (kept : choice.policy.term = .keep) :
    ∀ term : Term (paidPoint ticket.reserved),
      ¬ Decision.NoWorse ticket.reserved span (.paid term) .keep := by
  rw [ready.compiled] at selected
  intro term
  exact Work.a_kept_funded_choice_excludes_every_acceptable_paid_continuation _ _ choice selected kept (.control term)

theorem an_unfunded_choice_retains_the_actually_committed_prefix
    (choice : Decision.Choice ticket.reserved span .keep)
    (selected : ready.compilation.result = .selected choice) (kept : choice.policy.term = .keep) :
    ready.endpoint = comparisonPoint ticket.reserved := by
  unfold endpoint
  simp only [ready.receipt.authorized_exact,selected,kept]

theorem every_selected_paid_source_is_exactly_the_full_initial_cut_comparison
    (choice : Decision.Choice ticket.reserved span .keep)
    (selected : ready.compilation.result = .selected choice)
    (term : Continuation ticket.reserved) (funded : choice.policy.term = .paid term) :
    ready.endpoint = Whole.execute ticket.reserved span (.paid term) ∧
    HEq (Window.evaluate ready.endpoint.model cursor.depth
      (ready.endpoint.depth-cursor.depth))
      (tensor ticket.reserved span (.paid term) cursor.input.opponent).present := by
  have actual : ready.endpoint = Whole.execute ticket.reserved span (.paid term) := by
    unfold endpoint
    simp only [ready.receipt.authorized_exact,selected,funded]
  refine ⟨actual,?_⟩
  rw [actual]
  exact actual_installation_is_the_compared_full_initial_cut_window _ _ _
theorem an_open_family_selection_is_an_actual_paid_full_protocol
    (openFamily : ticket.reserved.ownFamily = true)
    (choice : Decision.Choice ticket.reserved span .keep)
    (selected : ready.compilation.result = .selected choice) :
    ∃ plan : Continuation ticket.reserved, choice.policy.term = .paid plan ∧
      ready.endpoint = Whole.execute ticket.reserved span (.paid plan) ∧
      HEq (Window.evaluate ready.endpoint.model cursor.depth
        (ready.endpoint.depth-cursor.depth))
        (tensor ticket.reserved span (.paid plan) cursor.input.opponent).present := by
  have deployable := choice.policy.no_regression.1
  cases same : choice.policy.term with
  | keep => simp [same,Deployable,openFamily] at deployable
  | paid plan => exact ⟨plan,rfl,
      ready.every_selected_paid_source_is_exactly_the_full_initial_cut_comparison choice selected plan same⟩

end Ready

variable (cursor pricing n baseReference actor position)
inductive Result where
  | preparationFailure (header : Prepaid.Protocol cursor pricing n baseReference actor position)
  | unpriced (scope : Scope cursor pricing n baseReference actor position) (absent : propose scope span = none)
  | refused (scope : Scope cursor pricing n baseReference actor position) (ticket : Ticket scope span)
      (unpaid : ticket.bill.payment.succeeded = false)
  | shortfall (scope : Scope cursor pricing n baseReference actor position) (ticket : Ticket scope span)
      (paid : ticket.bill.payment.succeeded = true) (lacks : ticket.bill.units < ticket.needed)
  | ready (scope : Scope cursor pricing n baseReference actor position) (ticket : Ticket scope span)
      (released : Ready scope span ticket)

def resumeFrom (scope : Scope cursor pricing n baseReference actor position) :
    Result cursor pricing n baseReference actor position span :=
  match quoted : propose scope span with
  | none => .unpriced scope quoted
  | some ticket =>
    if paid : ticket.bill.payment.succeeded = true then
      if covered : ticket.needed ≤ ticket.bill.units then
        let compilation := Work.compileFunded ticket.reserved span
        let receipt := Work.certify ticket.reserved span compilation
        let work := receipt.comparisonWork
        .ready scope ticket ⟨paid,covered,compilation,rfl,receipt,work,receipt.comparisonWork_exact⟩
      else .shortfall scope ticket paid (Nat.lt_of_not_ge covered)
    else .refused scope ticket (Bool.eq_false_iff.mpr paid)

def produce : Result cursor pricing n baseReference actor position span :=
  match Whole.prepare cursor pricing n baseReference actor position with
  | .inl header => .preparationFailure header
  | .inr scope => resumeFrom cursor pricing n baseReference actor position span scope

structure Protocol where
  private mk ::
  origin : Option (Scope cursor pricing n baseReference actor position)
  result : Result cursor pricing n baseReference actor position span
  generated : result = match origin with
    | none => produce cursor pricing n baseReference actor position span
    | some scope => resumeFrom cursor pricing n baseReference actor position span scope

def invoke : Protocol cursor pricing n baseReference actor position span :=
  ⟨none,produce cursor pricing n baseReference actor position span,rfl⟩

def resume (scope : Scope cursor pricing n baseReference actor position) :
    Protocol cursor pricing n baseReference actor position span :=
  ⟨some scope,resumeFrom cursor pricing n baseReference actor position span scope,rfl⟩

variable {cursor pricing n baseReference actor position span}
namespace Result
variable (made : Result cursor pricing n baseReference actor position span)
def endpoint : Cursor seed driver := match made with
  | .preparationFailure header => header.endpoint
  | .unpriced scope _ => comparisonPoint scope
  | .refused _ ticket _ | .shortfall _ ticket .. => comparisonPoint ticket.reserved
  | .ready _ _ released => released.endpoint

def status : Nat := match made with
  | .preparationFailure _ => 0 | .unpriced .. => 1 | .refused .. => 2 | .shortfall .. => 3 | .ready .. => 4
end Result
namespace Protocol
variable (made : Protocol cursor pricing n baseReference actor position span)
abbrev endpoint := made.result.endpoint
end Protocol
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Reservation
