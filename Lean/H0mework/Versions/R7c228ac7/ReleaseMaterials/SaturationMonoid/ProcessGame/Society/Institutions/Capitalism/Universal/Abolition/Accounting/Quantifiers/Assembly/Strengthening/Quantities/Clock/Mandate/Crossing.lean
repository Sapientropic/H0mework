import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.History
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate

open Source.Program PublicFunction
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Inputs" => List (RawEvent Party Good Port (State Party Technology) Instrument)

structure Crossed (bound : BoundSource base scope) (inputs : Inputs) (ordinal : Nat) : Prop where
  now : scope.task.deadline < clockAt bound inputs ordinal
  before : ∀ earlier < ordinal, clockAt bound inputs earlier ≤ scope.task.deadline
  later : ∀ next ≥ ordinal, scope.task.deadline < clockAt bound inputs next

/-- Zero clock increments and nonuniform actual durations remain visible.
An expiry occurrence exists precisely when the actual source clock crosses. -/
theorem first_crossing_or_actual_clock_obstruction (bound : BoundSource base scope) (inputs : Inputs) :
    (∃ ordinal, Crossed bound inputs ordinal) ∨
      (∀ ordinal, clockAt bound inputs ordinal ≤ scope.task.deadline) := by
  classical
  by_cases occurs : ∃ ordinal, scope.task.deadline < clockAt bound inputs ordinal
  · refine .inl ⟨Nat.find occurs, Nat.find_spec occurs, ?_, ?_⟩
    · intro earlier prior
      exact le_of_not_gt (Nat.find_min occurs prior)
    · intro next after
      exact (Nat.find_spec occurs).trans_le (real_clock_is_monotone bound inputs after)
  · exact .inr fun ordinal => le_of_not_gt fun after => occurs ⟨ordinal, after⟩

def expiryOrdinal (start deadline duration : ℚ) : Nat :=
  if deadline < start then 0 else ⌊(deadline - start) / duration⌋₊ + 1

theorem exact_expiry_for_owned_constant_duration (bound : BoundSource base scope) (inputs : Inputs)
    (duration : ℚ) (positive : 0 < duration)
    (owned : ∀ current, (law base scope).duration current = duration) (ordinal : Nat) :
    scope.task.deadline < clockAt bound inputs ordinal ↔
      expiryOrdinal bound.source.seed.initial.clock scope.task.deadline duration ≤ ordinal := by
  rw [constant_source_duration_gives_the_literal_clock bound inputs duration positive owned]
  unfold expiryOrdinal
  split
  · rename_i expired
    refine ⟨fun _ => Nat.zero_le _, fun _ => ?_⟩
    exact expired.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) positive.le))
  · rename_i before
    have nonnegative : 0 ≤ (scope.task.deadline - bound.source.seed.initial.clock) / duration :=
      div_nonneg (sub_nonneg.mpr (le_of_not_gt before)) positive.le
    rw [Nat.add_one_le_iff, Nat.floor_lt nonnegative, div_lt_iff₀ positive]
    constructor <;> intro bound <;> linarith only [bound]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate
