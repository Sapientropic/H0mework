import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Solver

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {first second : Party} {unit : Good}

local notation "Term" => SafeTerm base scope first second unit

def SafeTerm.ceiling (term : Term) : ℚ :=
  min scope.task.deadline (term.band.upper.getD scope.task.deadline)

theorem SafeTerm.ceiling_bounds (term : Term) {expiry : ℚ} (fit : term.Allows expiry) :
    expiry ≤ term.ceiling := by
  unfold SafeTerm.ceiling
  apply le_min fit.1
  cases ending : term.band.upper with
  | none => simpa only [ending, Option.getD_none] using fit.1
  | some clock =>
    simpa only [ending, Option.getD_some] using (fit.2.2 clock ending).le

theorem SafeTerm.approaches_ceiling (term : Term) (threshold : ℚ) (earlier : threshold < term.ceiling) :
    ∃ expiry, term.Allows expiry ∧ threshold < expiry := by
  have owns := term.at_least_owns_its_review
  have bounded := term.ceiling_bounds owns
  rcases bounded.lt_or_eq with room | top
  · let expiry := (max threshold term.band.lower + term.ceiling) / 2
    have intermediate := max_lt_iff.mpr ⟨earlier, room⟩
    have after : max threshold term.band.lower < expiry := by dsimp [expiry]; linarith
    have before : expiry < term.ceiling := by dsimp [expiry]; linarith
    refine ⟨expiry, ⟨before.le.trans (min_le_left _ _),
      ⟨?_, ?_⟩⟩, (le_max_left _ _).trans_lt after⟩
    · intro _ named
      exact (Option.some.inj named.symm).le.trans ((le_max_right _ _).trans after.le)
    · intro clock ending
      have cap : term.ceiling ≤ clock := by
        unfold SafeTerm.ceiling
        change term.band.upper = some clock at ending
        rw [ending]
        exact min_le_right _ _
      exact before.trans_le cap
  · exact ⟨term.band.lower, owns, top.symm ▸ earlier⟩

theorem SafeTerm.ceiling_attained_iff (term : Term) :
    term.Allows term.ceiling ↔ ∀ clock, term.band.upper = some clock → scope.task.deadline < clock := by
  have bounded := term.ceiling_bounds term.at_least_owns_its_review
  constructor
  · intro fit clock ending
    have before := fit.2.2 clock ending
    unfold SafeTerm.ceiling at before
    rw [ending] at before
    by_contra! atClock
    simp only [Option.getD_some, min_eq_right atClock] at before
    exact (lt_irrefl clock) before
  · intro before
    have upper : term.ceiling ≤ scope.task.deadline := min_le_left _ _
    refine ⟨upper, ⟨?_, fun clock ending => upper.trans_lt (before clock ending)⟩⟩
    intro _ named
    exact (Option.some.inj named.symm).le.trans bounded

theorem exact_envelope (terms : List Term) {term : Term}
    (selected : Threshold.best SafeTerm.ceiling terms = some term) :
    IsLUB {expiry | ∃ candidate ∈ terms, candidate.Allows expiry} term.ceiling ∧
      ∀ earlier < term.ceiling, ∃ expiry, (∃ candidate ∈ terms, candidate.Allows expiry) ∧ earlier < expiry := by
  have best := Threshold.best_spec selected
  have approaches (earlier : ℚ) (before : earlier < term.ceiling) :
      ∃ expiry, (∃ candidate ∈ terms, candidate.Allows expiry) ∧ earlier < expiry := by
    obtain ⟨expiry, fits, after⟩ := term.approaches_ceiling earlier before
    exact ⟨expiry, ⟨term, best.1, fits⟩, after⟩
  refine ⟨⟨?_, ?_⟩, approaches⟩
  · intro expiry
    rintro ⟨other, original, within⟩
    exact (other.ceiling_bounds within).trans (best.2 other original)
  · intro bound above
    apply le_of_not_gt
    intro earlier
    obtain ⟨expiry, fits, after⟩ := approaches bound earlier
    exact (not_lt_of_ge (above fits)) after

variable (base scope first second unit)
  (initial : RawCurrent Party Good (State Party Technology) Instrument)
  (words : List (RawEvent Party Good Port (State Party Technology) Instrument))

def longest? :=
  Threshold.best (SafeTerm.ceiling (base := base) (scope := scope) (first := first) (second := second) (unit := unit))
    (frontier base scope first second unit initial words)

/-- The upper endpoint may be open at an already funded review. The
supremum is exact and can always be approached without changing the
original service or moving the review. -/
theorem longest_exact {term : Term}
    (selected : longest? base scope first second unit initial words = some term) :
    IsLUB {expiry | Feasible base scope first second unit initial words expiry} term.ceiling ∧
      ∀ earlier < term.ceiling, ∃ expiry, Feasible base scope first second unit initial words expiry ∧ earlier < expiry := by
  simpa only [← frontier_is_exact base scope first second unit initial words] using
    exact_envelope (frontier base scope first second unit initial words) selected

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
