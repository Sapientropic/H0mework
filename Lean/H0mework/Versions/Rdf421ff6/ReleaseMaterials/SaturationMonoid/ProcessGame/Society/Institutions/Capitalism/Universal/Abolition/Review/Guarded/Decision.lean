import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.MicroBudget
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Check

/-!
# Source-paid review with fixed original needs

A pending edge is the rejected image of this fixed evaluator, after a real
fee microstep. A selected candidate cannot be left pending. Selection is not
execution of the candidate: its exact period must still be written by the
root before it can be reported as a paid independent period.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument)
  (request : Request Party Good Port Technology Instrument) (fee : FeeScope request)
  (members : List Party)

inductive CandidateDecisionAt (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Type
  | selected (payment : PaymentAt input.law request current)
      (checked : Checks input origin payment.microNext members word)
  | rejected (payment : PaymentAt input.law request current)
      (issue : Issue input origin payment.microNext members word)
  | blocked (obstruction : Blockage input.law request fee current)

def evaluateCandidate (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    CandidateDecisionAt input origin request fee members current word :=
  match attempt input.law request fee current with
  | .inr obstruction => .blocked obstruction
  | .inl payment => match inspect input origin payment.microNext members word with
    | .accepted checked => .selected payment checked
    | .rejected issue => .rejected payment issue

/-- The scheduler may not suppress a candidate after its source checks
succeed. Both the payment and the verdict are computed by this evaluator. -/
theorem selects_checked_candidate
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (payment : PaymentAt input.law request current)
    (paid : attempt input.law request fee current = .inl payment)
    (checked : Checks input origin payment.microNext members word) :
    ∃ proof, evaluateCandidate input origin request fee members current word = .selected payment proof := by
  unfold evaluateCandidate
  rw [paid]
  dsimp only
  cases found : inspect input origin payment.microNext members word with
  | accepted proof => exact ⟨proof, rfl⟩
  | rejected issue => exact (issue.refutes input origin _ members word checked).elim

/-- Only a paid, actually rejected head enters another pending state. The
initial candidate list is source code, not a table of successful futures. -/
inductive PendingRun : RawCurrent Party Good Technology Instrument →
    List (RawEvent Party Good Port Technology Instrument) →
    RawCurrent Party Good Technology Instrument →
    List (RawEvent Party Good Port Technology Instrument) → Nat → Type
  | nil (current candidates) : PendingRun current candidates current candidates 0
  | snoc {start candidates current word remaining count}
      (prior : PendingRun start candidates current (word :: remaining) count)
      (payment : PaymentAt input.law request current)
      (issue : Issue input origin payment.microNext members word)
      (generated : evaluateCandidate input origin request fee members current word = .rejected payment issue) :
      PendingRun start candidates payment.microNext remaining (count + 1)

namespace PendingRun
variable {input origin request fee members}
  {start target : RawCurrent Party Good Technology Instrument}
  {candidates remaining : List (RawEvent Party Good Port Technology Instrument)} {count : Nat}
  (run : PendingRun input origin request fee members start candidates target remaining count)

/-- The progress proof reads the original material payments in the actual
source-decided path. It never assumes endpoint rank descent. -/
noncomputable def payments : PaidMicroRun input.law request start target count := by
  induction run with
  | nil => exact .nil _
  | snoc prior payment _issue _generated previous => exact .snoc previous payment

include run in
theorem inventory_exact : count + remaining.length = candidates.length := by
  induction run with
  | nil => simp
  | snoc prior payment issue generated previous => simp only [List.length_cons] at previous; omega

include run in
theorem finite_pending_bound : count ≤ min
    (physicalBudget request fee start) candidates.length := by
  have physical := run.payments.count_le_original_budget fee
  have inventory := run.inventory_exact
  exact le_min physical (by omega)

include run in
theorem exhausted_stock_forces_obstruction
    (spent : count = physicalBudget request fee start)
    (word : RawEvent Party Good Port Technology Instrument) :
    ∃ shortage : target.stock fee.payer fee.good < fee.amount,
      evaluateCandidate input origin request fee members target word = .blocked (.stock shortage) := by
  have remainingBudget := run.payments.count_add_remaining_budget fee
  have zero : physicalBudget request fee target = 0 := by omega
  have shortage := zero_budget_is_real_shortage request fee target zero
  exact ⟨shortage, by simp only [evaluateCandidate, attempt, dif_neg (not_le_of_gt shortage)]⟩

include run in
theorem cannot_extend_beyond_original_budget
    (spent : count = physicalBudget request fee start)
    (word : RawEvent Party Good Port Technology Instrument) :
    ¬ ∃ payment issue,
      evaluateCandidate input origin request fee members target word = .rejected payment issue := by
  obtain ⟨shortage, blocked⟩ := run.exhausted_stock_forces_obstruction spent word
  rintro ⟨payment, issue, rejected⟩
  rw [blocked] at rejected
  cases rejected

end PendingRun

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.evaluateCandidate
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.selects_checked_candidate
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.PendingRun.finite_pending_bound
