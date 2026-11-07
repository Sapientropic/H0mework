import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Resolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term

open Source.Program PublicFunction PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Inputs" => List (RawEvent Party Good Port (State Party Technology) Instrument)

theorem constant_owned_duration_orders_cutoffs_by_paid_word_count
    (bound : BoundSource base scope) (past first second : Inputs) (duration : ℚ) (positive : 0 < duration)
    (owned : ∀ current, (law base scope).duration current = duration) :
    readClock bound past first ≤ readClock bound past second ↔ first.length ≤ second.length := by
  change (((clockAt bound (past ++ first) ((past ++ first).length + 2) : ℚ) : ℝ) : EReal) ≤
    (((clockAt bound (past ++ second) ((past ++ second).length + 2) : ℚ) : ℝ) : EReal) ↔ _
  rw [EReal.coe_le_coe_iff, Rat.cast_le, constant_source_duration_gives_the_literal_clock _ _ _ positive owned,
    constant_source_duration_gives_the_literal_clock _ _ _ positive owned, add_le_add_iff_left,
    mul_le_mul_iff_left₀ positive]
  simp only [Nat.cast_le, List.length_append]
  omega

/-- A genuine discrete clock makes the nonempty paid domain attain its
tight cutoff. Selection ranges over every original continuation. -/
theorem a_discrete_original_mandate_executes_at_its_tight_clock_or_retains_its_blockers
    (bound : BoundSource base scope) (past : Inputs) (duration : ℚ) (positive : 0 < duration)
    (owned : ∀ current, (law base scope).duration current = duration) :
    (∃ suffix, PaidAt bound past suffix ∧ IsLeast (times bound past) (readClock bound past suffix)) ∨
      ∀ suffix, Nonempty (Issue bound past suffix) := by
  classical
  let feasible (n : Nat) := ∃ suffix : Inputs, suffix.length = n ∧ PaidAt bound past suffix
  by_cases some : ∃ n, feasible n
  · obtain ⟨suffix, length, paid⟩ := Nat.find_spec some
    refine .inl ⟨suffix, paid, ⟨⟨suffix, paid, rfl⟩, ?_⟩⟩
    rintro _ ⟨other, otherPaid, rfl⟩
    apply (constant_owned_duration_orders_cutoffs_by_paid_word_count bound past suffix other duration positive owned).mpr
    rw [length]
    exact Nat.find_min' some ⟨other, rfl, otherPaid⟩
  · apply Or.inr
    intro suffix
    cases decide bound past suffix with
    | blocked issue => exact ⟨issue⟩
    | paid actual => exact (some ⟨suffix.length, suffix, rfl, actual⟩).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term
