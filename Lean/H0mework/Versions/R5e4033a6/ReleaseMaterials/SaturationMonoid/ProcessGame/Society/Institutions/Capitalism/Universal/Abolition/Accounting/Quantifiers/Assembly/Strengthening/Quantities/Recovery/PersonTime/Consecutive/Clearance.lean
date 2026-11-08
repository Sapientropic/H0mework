import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TightBound

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive.Clearance

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

private def check (origin : C) (exposure repair : Script) : Bool :=
  match decideAt (Execution.endAt origin exposure) repair with
  | .blocked _ => false
  | .feasible _ => (Recovery.inspect origin exposure repair).isNone

private theorem checked_iff (origin : C) (exposure repair : Script) :
    check origin exposure repair = true ↔ PaidRecovery origin exposure repair := by
  unfold check
  cases decideAt (Execution.endAt origin exposure) repair with
  | blocked issue =>
    simp only [Bool.false_eq_true, false_iff]
    exact fun paid => issue.refutes paid.settled.toFeasible
  | feasible paid =>
    rw [Option.isNone_iff_eq_none, cleared_exactly_when_no_original_actor_loses_stock]
    exact ⟨fun restored => ⟨settle _ _ paid, restored, record origin _⟩, PaidRecovery.restored⟩

/-- Search original prefix positions in order. Clearance may cease to
hold after another actual instruction, so every prefix is examined. -/
def first (origin : C) (exposure repair : Script) : Option Nat :=
  (List.range' 0 (repair.length + 1)).find? fun index => check origin exposure (repair.take index)

def clockAt (origin : C) (exposure repair : Script) (index : Nat) : ℚ :=
  (Execution.endAt origin (exposure ++ repair.take index)).raw.clock

private theorem clock_monotone (origin : C) (exposure repair : Script) {earlier later : Nat}
    (ordered : earlier ≤ later) :
    clockAt origin exposure repair earlier ≤ clockAt origin exposure repair later := by
  have split : repair.take later = repair.take earlier ++ (repair.drop earlier).take (later - earlier) := by
    simpa only [Nat.add_sub_of_le ordered] using (List.take_add (l := repair) (i := earlier) (j := later - earlier))
  unfold clockAt
  rw [split, ← List.append_assoc]
  simpa only [Execution.endAt_append] using Execution.the_actual_script_never_runs_the_clock_backwards
    (Execution.endAt origin (exposure ++ repair.take earlier)) ((repair.drop earlier).take (later - earlier))

theorem first_is_the_earliest_original_paid_clearance
    (origin : C) (exposure repair : Script) (index : Nat) (found : first origin exposure repair = some index) :
    index ≤ repair.length ∧ PaidRecovery origin exposure (repair.take index) ∧
      ∀ position ≤ repair.length, PaidRecovery origin exposure (repair.take position) →
        index ≤ position ∧ clockAt origin exposure repair index ≤ clockAt origin exposure repair position := by
  obtain ⟨paid, listed, earlier⟩ := List.find?_range'_eq_some.mp found
  have inside : index ≤ repair.length := by
    have bound := (List.mem_range'_1.mp listed).2
    omega
  refine ⟨inside, (checked_iff _ _ _).mp paid, ?_⟩
  intro position _ restored
  have order : index ≤ position := by
    by_contra! before
    have missing := earlier position (Nat.zero_le _) before
    have complete := (checked_iff _ _ _).mpr restored
    rw [complete] at missing
    contradiction
  exact ⟨order, clock_monotone origin exposure repair order⟩

theorem no_clearance_records_the_original_issue_at_every_prefix
    (origin : C) (exposure repair : Script) (noneFound : first origin exposure repair = none) :
    ∀ index ≤ repair.length, Recorded origin (exposure ++ repair.take index) ∧
      (Nonempty (Obstruction (Execution.endAt origin exposure) (repair.take index)) ∨
        Nonempty (Loss origin exposure (repair.take index))) := by
  intro index within
  have absent := List.find?_eq_none.mp noneFound index (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  refine ⟨record origin _, ?_⟩
  cases decideAt (Execution.endAt origin exposure) (repair.take index) with
  | blocked issue => exact .inl ⟨issue⟩
  | feasible paid =>
    cases observed : Recovery.inspect origin exposure (repair.take index) with
    | some loss => exact .inr ⟨loss⟩
    | none =>
      exact (absent ((checked_iff _ _ _).mpr ⟨settle _ _ paid,
        (cleared_exactly_when_no_original_actor_loses_stock _ _ _).mp observed, record origin _⟩)).elim

theorem final_payment_generates_an_actual_earliest_clearance (origin : C) (exposure repair : Script)
    (paid : PaidRecovery origin exposure repair) :
    ∃ index, first origin exposure repair = some index := by
  cases found : first origin exposure repair with
  | some index => exact ⟨index, rfl⟩
  | none =>
    obtain ⟨_, failure⟩ := no_clearance_records_the_original_issue_at_every_prefix origin exposure repair
      found repair.length le_rfl
    rw [List.take_length] at failure
    rcases failure with ⟨⟨issue⟩⟩ | ⟨⟨loss⟩⟩
    · exact (issue.refutes paid.settled.toFeasible).elim
    · exact (not_lt_of_ge (paid.restored loss.address.1 loss.address.2) loss.unpaid).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive.Clearance
