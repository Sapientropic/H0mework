import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.Selection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count)) (limit : Nat)

def origin := Continuation.initial input (Admission.frame input depth count)
def atFee := Settlement.initial input depth count datum
def code := Admission.code input depth count datum
def cohort := Settlement.members input depth count
def candidates := Settlement.rawCandidates input depth count datum limit

theorem candidates_nonempty : candidates input depth count datum limit ≠ [] := by
  have emptyWord : [] ∈ candidates input depth count datum limit :=
    (PublicFunction.mem_words_iff _ _ []).mpr ⟨Nat.zero_le _, by simp⟩
  intro empty
  rw [empty] at emptyWord
  cases emptyWord

abbrev Completed := Review.Guarded.CompletedAt input (origin input depth count)
  (code input depth count datum).request (code input depth count datum).scope
  (cohort input depth count) (origin input depth count) (candidates input depth count datum limit)

def finishPaidHead (word : RawEvent Party Good Port Technology Instrument)
    (tail : List (RawEvent Party Good Port Technology Instrument))
    (paid : Review.PaymentAt input.law (code input depth count datum).request (origin input depth count))
    (paid_eq : Review.attempt input.law (code input depth count datum).request (code input depth count datum).scope
      (origin input depth count) = .inl paid) :
    Review.Guarded.CompletedAt input (origin input depth count) (code input depth count datum).request
      (code input depth count datum).scope (cohort input depth count) (origin input depth count) (word :: tail) :=
  match observed : Review.Guarded.inspect input (origin input depth count) paid.microNext (cohort input depth count) word with
  | .accepted checked => .selected (.nil _ _) paid checked (by
      simp only [Review.Guarded.evaluateCandidate, paid_eq, observed])
  | .rejected issue => Review.Guarded.completePending input (origin input depth count)
      (code input depth count datum).request (code input depth count datum).scope (cohort input depth count)
      tail paid.microNext 1 (.snoc (.nil _ _) paid issue (by
        simp only [Review.Guarded.evaluateCandidate, paid_eq, observed]))

def completedFor : (words : List (RawEvent Party Good Port Technology Instrument)) → words ≠ [] →
    Review.Guarded.CompletedAt input (origin input depth count) (code input depth count datum).request
      (code input depth count datum).scope (cohort input depth count) (origin input depth count) words
  | [], nonempty => False.elim (nonempty rfl)
  | word :: tail, _ => match paid_eq : Admission.result input depth count datum with
    | .inl paid => finishPaidHead input depth count datum word tail paid paid_eq
    | .inr blocked => .blocked (.nil _ _) blocked (by
        have rejected : Review.attempt input.law (code input depth count datum).request
            (code input depth count datum).scope (origin input depth count) = .inr blocked := paid_eq
        simp only [Review.Guarded.evaluateCandidate, rejected])

/-- The first payment belongs to the preceding actual Admission write.
Only a rejected head invokes further paid microsteps. -/
def completed : Completed input depth count datum limit :=
  completedFor input depth count datum (candidates input depth count datum limit)
    (candidates_nonempty input depth count datum limit)

def effect := (completed input depth count datum limit).effect

theorem whole_review_cost_is_actual :
    (completed input depth count datum limit).current.stock (code input depth count datum).scope.payer
        (code input depth count datum).scope.good +
      ((completed input depth count datum limit).paidCount : ℚ) * (code input depth count datum).scope.amount =
        (origin input depth count).stock (code input depth count datum).scope.payer (code input depth count datum).scope.good :=
  (completed input depth count datum limit).material_accounting

theorem whole_review_has_original_finite_bound :
    (completed input depth count datum limit).paidCount ≤ min
      (Review.physicalBudget (code input depth count datum).request (code input depth count datum).scope
        (origin input depth count)) (candidates input depth count datum limit).length :=
  le_min (completed input depth count datum limit).bounded_by_original_material
    (completed input depth count datum limit).bounded_by_candidate_inventory

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch
