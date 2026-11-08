import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Replay
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Resolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm

open Source.Program
open PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument

variable (bound : BoundSource base scope)
  (past suffix : List (RawEvent Party Good Port (State Party Technology) Instrument))

abbrev actualAt (ordinal : Fin suffix.length) :=
  OutstandingSource.History.actualExecution bound.source (past ++ suffix) (past.length + ordinal.val + 1)

theorem actual_at_submits_its_original_word (ordinal : Fin suffix.length) :
    (actualAt bound past suffix ordinal).submitted = suffix[ordinal.val] := by
  have inside : past.length + ordinal.val < (past ++ suffix).length := by
    rw [List.length_append]
    exact Nat.add_lt_add_left ordinal.isLt _
  have actual := OutstandingSource.History.scheduled_input_is_actual bound.source (past ++ suffix)
    (past.length + ordinal.val) inside
  simpa only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using actual

def Payable (cutoff : ℚ) : Prop :=
  ∀ ordinal : Fin suffix.length, PaidItems base (withCutoff scope cutoff)
    (actualAt bound past suffix ordinal).before 0 (actualAt bound past suffix ordinal).submitted

def periodGuards : List Guard :=
  (List.finRange suffix.length).flatMap fun ordinal =>
    let actual := actualAt bound past suffix ordinal
    itemGuards base scope actual.before 0 actual.submitted

abbrev payments :=
  (OutstandingSource.History.trailAt bound.source (past ++ suffix) ((past ++ suffix).length + 2)).frame.payments

def serviceGuards : List Guard :=
  (List.finRange bound.source.seed.task.slots.length).filterMap fun slot =>
    (payments bound past suffix slot).map fun ordinal =>
      .atLeast (clockAt bound (past ++ suffix) (ordinal + 1))

/-- The exact clock interval for retaining the submitted action effects
and each original recorded service settlement on this schedule. -/
def sourceWindow : Interval :=
  Interval.ofGuards (periodGuards bound past suffix ++ serviceGuards bound past suffix)

def KeepSettlements (cutoff : ℚ) : Prop :=
  ∀ slot ordinal, payments bound past suffix slot = some ordinal →
    clockAt bound (past ++ suffix) (ordinal + 1) ≤ cutoff

theorem source_window_exact (cutoff : ℚ) (paid : Payable bound past suffix scope.task.deadline) :
    (sourceWindow bound past suffix).Holds cutoff ↔
      Payable bound past suffix cutoff ∧ KeepSettlements bound past suffix cutoff := by
  have period : (∀ one ∈ periodGuards bound past suffix, one.Holds cutoff) ↔
      Payable bound past suffix cutoff := by
    constructor
    · intro fits ordinal
      let actual := actualAt bound past suffix ordinal
      have original : PaidItems base scope actual.before 0 actual.submitted := paid ordinal
      apply (replays_paid_word_exactly base scope actual.before 0 actual.submitted cutoff original).1.mpr
      exact (Interval.of_guards_holds_iff _ _).mpr fun one inside =>
        fits one (List.mem_flatMap.mpr ⟨ordinal, List.mem_finRange _, inside⟩)
    · intro fits one inside
      obtain ⟨ordinal, _, guarded⟩ := List.mem_flatMap.mp inside
      let actual := actualAt bound past suffix ordinal
      have original : PaidItems base scope actual.before 0 actual.submitted := paid ordinal
      have checked := (replays_paid_word_exactly base scope actual.before 0 actual.submitted cutoff original).1.mp (fits ordinal)
      exact (Interval.of_guards_holds_iff _ _).mp checked one guarded
  have service : (∀ one ∈ serviceGuards bound past suffix, one.Holds cutoff) ↔
      KeepSettlements bound past suffix cutoff := by
    constructor
    · intro fits slot ordinal recorded
      apply fits (.atLeast (clockAt bound (past ++ suffix) (ordinal + 1)))
      apply List.mem_filterMap.mpr
      exact ⟨slot, List.mem_finRange _, by simp [recorded]⟩
    · intro fits one inside
      obtain ⟨slot, _, checked⟩ := List.mem_filterMap.mp inside
      cases recorded : payments bound past suffix slot with
      | none => simp [recorded] at checked
      | some ordinal =>
        have same : Guard.atLeast (clockAt bound (past ++ suffix) (ordinal + 1)) = one := by
          simpa [recorded] using checked
        rw [← same]
        exact fits slot ordinal recorded
  rw [sourceWindow, Interval.of_guards_holds_iff, ← period, ← service]
  simp only [List.forall_mem_append]

theorem kept_paid_settlement_has_its_original_clock
    (slot : bound.source.Slot) (ordinal : Nat) (recorded : payments bound past suffix slot = some ordinal) :
    0 < ordinal ∧ ordinal < (past ++ suffix).length + 2 ∧
      clockAt bound (past ++ suffix) (ordinal + 1) ≤ bound.source.seed.task.deadline := by
  obtain ⟨positive, earlier, paid⟩ := OutstandingSource.History.recorded_payment_is_own_actual
    bound.source (past ++ suffix) ((past ++ suffix).length + 2) slot ordinal recorded
  refine ⟨positive, earlier, ?_⟩
  rw [clock_succ_is_its_original_paid_period_duration, ← bound.law_exact]
  exact paid.2.1

theorem outside_source_window_names_original_instruction_or_settlement (cutoff : ℚ)
    (paid : Payable bound past suffix scope.task.deadline)
    (failed : ¬ (sourceWindow bound past suffix).Holds cutoff) :
    (∃ (period : Fin suffix.length) (item : Item),
      item ∈ (law base scope).rawItems (actualAt bound past suffix period).before
        (actualAt bound past suffix period).submitted ∧
      ¬ (guard base scope item.before item.request).Holds cutoff) ∨
    (∃ slot ordinal, payments bound past suffix slot = some ordinal ∧
      cutoff < clockAt bound (past ++ suffix) (ordinal + 1)) := by
  classical
  by_cases keep : KeepSettlements bound past suffix cutoff
  · left
    have denied : ¬ Payable bound past suffix cutoff := fun fits =>
      failed ((source_window_exact bound past suffix cutoff paid).mpr ⟨fits, keep⟩)
    obtain ⟨period, denied⟩ := not_forall.mp denied
    let actual := actualAt bound past suffix period
    have original : PaidItems base scope actual.before 0 actual.submitted := paid period
    have outside := fun fits => denied ((replays_paid_word_exactly
      base scope actual.before 0 actual.submitted cutoff original).1.mpr fits)
    obtain ⟨item, inside, violated⟩ := outside_guard_names_an_original_item
      base scope actual.before 0 actual.submitted cutoff outside
    exact ⟨period, item, inside, violated⟩
  · right
    obtain ⟨slot, failed⟩ := not_forall.mp keep
    obtain ⟨ordinal, failed⟩ := not_forall.mp failed
    exact ⟨slot, ordinal, (Classical.not_imp.mp failed).1, lt_of_not_ge (Classical.not_imp.mp failed).2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
