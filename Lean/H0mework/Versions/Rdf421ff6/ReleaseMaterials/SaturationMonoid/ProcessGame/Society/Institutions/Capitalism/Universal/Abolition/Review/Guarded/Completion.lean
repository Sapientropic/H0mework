import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Decision

/-! Finite source-code review. Every rejected candidate retains its actual
payment and original issue. The result has no pending constructor; selection
still owes execution to the root, and exhaustion does not settle old debts. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument)
  (request : Request Party Good Port Technology Instrument) (fee : FeeScope request)
  (members : List Party)

inductive CompletedAt (start : RawCurrent Party Good Technology Instrument)
    (candidates : List (RawEvent Party Good Port Technology Instrument)) : Type
  | selected {current word remaining count}
      (prior : PendingRun input origin request fee members start candidates current (word :: remaining) count)
      (payment : PaymentAt input.law request current)
      (checked : Checks input origin payment.microNext members word)
      (generated : evaluateCandidate input origin request fee members current word = .selected payment checked)
  | exhausted {current count}
      (prior : PendingRun input origin request fee members start candidates current [] count)
  | blocked {current word remaining count}
      (prior : PendingRun input origin request fee members start candidates current (word :: remaining) count)
      (obstruction : Blockage input.law request fee current)
      (generated : evaluateCandidate input origin request fee members current word = .blocked obstruction)

def completePending {start candidates}
    (remaining : List (RawEvent Party Good Port Technology Instrument))
    (current : RawCurrent Party Good Technology Instrument) (count : Nat)
    (prior : PendingRun input origin request fee members start candidates current remaining count) :
    CompletedAt input origin request fee members start candidates :=
  match remaining with
  | [] => .exhausted prior
  | word :: tail =>
      match verdict : evaluateCandidate input origin request fee members current word with
      | .selected payment checked => .selected prior payment checked verdict
      | .blocked obstruction => .blocked prior obstruction verdict
      | .rejected payment issue =>
          completePending tail payment.microNext (count + 1) (.snoc prior payment issue verdict)

/-- The only supplied future data are finite candidate instructions. Their
validity, cost and outcome are computed at each resulting physical current. -/
def complete (start : RawCurrent Party Good Technology Instrument)
    (candidates : List (RawEvent Party Good Port Technology Instrument)) :
    CompletedAt input origin request fee members start candidates :=
  completePending input origin request fee members candidates start 0 (.nil start candidates)

namespace CompletedAt

variable {input origin request fee members}
  {start : RawCurrent Party Good Technology Instrument}
  {candidates : List (RawEvent Party Good Port Technology Instrument)}
  (answer : CompletedAt input origin request fee members start candidates)

def current : RawCurrent Party Good Technology Instrument :=
  match answer with
  | .selected _ payment _ _ => payment.microNext
  | .exhausted (current := state) _ => state
  | .blocked (current := state) _ _ _ => state

def paidCount : Nat :=
  match answer with
  | .selected (count := count) _ _ _ _ => count + 1
  | .exhausted (count := count) _ => count
  | .blocked (count := count) _ _ _ => count

noncomputable def payments : PaidMicroRun input.law request start answer.current answer.paidCount :=
  match answer with
  | .selected prior payment _ _ => .snoc prior.payments payment
  | .exhausted prior => prior.payments
  | .blocked prior _ _ => prior.payments

theorem bounded_by_original_material :
    answer.paidCount ≤ physicalBudget request fee start :=
  answer.payments.count_le_original_budget fee

theorem bounded_by_candidate_inventory : answer.paidCount ≤ candidates.length := by
  cases answer with
  | selected prior payment checked generated =>
      have inventory := prior.inventory_exact
      simp only [List.length_cons] at inventory
      simp only [paidCount]
      omega
  | exhausted prior =>
      have inventory := prior.inventory_exact
      simp only [paidCount]
      simp only [List.length_nil, add_zero] at inventory
      omega
  | blocked prior obstruction generated =>
      have inventory := prior.inventory_exact
      simp only [List.length_cons] at inventory
      simp only [paidCount]
      omega

theorem preserves_original_claims : answer.current.claims = start.claims :=
  answer.payments.original_claims_unchanged fee

theorem preserves_period : answer.current.clock = start.clock ∧ answer.current.round = start.round :=
  answer.payments.same_period

theorem material_accounting :
    answer.current.stock fee.payer fee.good + (answer.paidCount : ℚ) * fee.amount =
      start.stock fee.payer fee.good := answer.payments.material_balance fee

end CompletedAt

/-- Any purported indefinitely pending path would have a finite prefix
longer than its original material budget. No completed future is assumed. -/
theorem no_unbounded_pending
    (start : RawCurrent Party Good Technology Instrument)
    (candidates : List (RawEvent Party Good Port Technology Instrument)) :
    ¬ (∀ count, ∃ current remaining,
      Nonempty (PendingRun input origin request fee members start candidates current remaining count)) := by
  intro forever
  obtain ⟨current, remaining, ⟨run⟩⟩ :=
    forever (physicalBudget request fee start + 1)
  have bound := run.finite_pending_bound
  have physical := (le_min_iff.mp bound).1
  omega

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.complete
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.CompletedAt.material_accounting
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.no_unbounded_pending
