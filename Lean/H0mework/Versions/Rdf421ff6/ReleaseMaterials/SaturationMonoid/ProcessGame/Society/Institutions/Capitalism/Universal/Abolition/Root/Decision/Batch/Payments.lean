import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

def dropFirst {law : RawLaw Party Good Port Technology Instrument}
    {request : Request Party Good Port Technology Instrument}
    {start : RawCurrent Party Good Technology Instrument} (first : Review.PaymentAt law request start) :
    (count : Nat) → {target : RawCurrent Party Good Technology Instrument} →
      Review.PaidMicroRun law request start target (count + 1) →
        Review.PaidMicroRun law request first.microNext target count
  | 0, _, run => by
      cases run with
      | snoc prior payment =>
          cases prior
          exact .nil _
  | count + 1, _, run => by
      cases run with
      | snoc prior payment => exact .snoc (dropFirst first count prior) payment

theorem completePending_keeps_paid_prefix
    (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (origin : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (fee : Review.FeeScope request)
    (members : List Party) {start candidates}
    (remaining : List (RawEvent Party Good Port Technology Instrument))
    (current : RawCurrent Party Good Technology Instrument) (count : Nat)
    (prior : Review.Guarded.PendingRun input origin request fee members start candidates current remaining count) :
    count ≤ (Review.Guarded.completePending input origin request fee members remaining current count prior).paidCount := by
  induction remaining generalizing current count with
  | nil => exact Nat.le_refl _
  | cons word tail induction =>
      unfold Review.Guarded.completePending
      split
      · exact Nat.le_succ _
      · exact Nat.le_refl _
      · exact (Nat.le_succ count).trans (induction _ _ _)

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count)) (limit : Nat)

theorem finishPaidHead_positive (word : RawEvent Party Good Port Technology Instrument)
    (tail : List (RawEvent Party Good Port Technology Instrument))
    (paid : Review.PaymentAt input.law (code input depth count datum).request (origin input depth count))
    (paid_eq : Review.attempt input.law (code input depth count datum).request (code input depth count datum).scope
      (origin input depth count) = .inl paid) :
    1 ≤ (finishPaidHead input depth count datum word tail paid paid_eq).paidCount := by
  unfold finishPaidHead
  split
  · exact Nat.le_refl _
  · exact completePending_keeps_paid_prefix input _ _ _ _ _ _ _ _

theorem completedFor_positive_of_original_payment
    (words : List (RawEvent Party Good Port Technology Instrument)) (nonempty : words ≠ [])
    (paid : Review.PaymentAt input.law (code input depth count datum).request (origin input depth count))
    (paid_eq : Admission.result input depth count datum = .inl paid) :
    1 ≤ (completedFor input depth count datum words nonempty).paidCount := by
  cases words with
  | nil => exact False.elim (nonempty rfl)
  | cons word tail =>
      unfold completedFor
      split
      next actual actual_eq =>
        have same := Sum.inl.inj (actual_eq.symm.trans paid_eq)
        subst actual
        exact finishPaidHead_positive input depth count datum word tail paid actual_eq
      next blocked rejected => cases rejected.symm.trans paid_eq

theorem completed_positive_of_original_payment
    (paid : Review.PaymentAt input.law (code input depth count datum).request (origin input depth count))
    (paid_eq : Admission.result input depth count datum = .inl paid) :
    1 ≤ (completed input depth count datum limit).paidCount :=
  completedFor_positive_of_original_payment input depth count datum
    (candidates input depth count datum limit) (candidates_nonempty input depth count datum limit) paid paid_eq

def paymentsAfterOriginalFee
    (paid : Review.PaymentAt input.law (code input depth count datum).request (origin input depth count))
    (paid_eq : Admission.result input depth count datum = .inl paid) :
    Review.PaidMicroRun input.law (code input depth count datum).request (atFee input depth count datum)
      (completed input depth count datum limit).current ((completed input depth count datum limit).paidCount - 1) := by
  have positive := completed_positive_of_original_payment input depth count datum limit paid paid_eq
  have count_eq := Nat.sub_add_cancel positive
  exact dropFirst paid _ (Eq.mpr (congrArg
    (fun size => Review.PaidMicroRun input.law (code input depth count datum).request (origin input depth count)
      (completed input depth count datum limit).current size) count_eq)
    (completed input depth count datum limit).payments)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch
