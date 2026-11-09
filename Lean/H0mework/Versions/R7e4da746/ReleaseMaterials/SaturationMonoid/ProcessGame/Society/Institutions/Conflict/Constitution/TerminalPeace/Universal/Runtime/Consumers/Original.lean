import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Consumers.WordReplay
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers.Stocked
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.OriginalProgramme

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual (StateAt)
open Supply.Consumers (the_original_ordered_period_is_paid the_original_personal_period_is_paid)

noncomputable section

abbrev input := TerminalPeace.Supply.revisedInput
abbrev people : List Bool := [false, true]

abbrev joint (first : Bool) := TerminalPeace.Supply.personalWord first ++ TerminalPeace.Supply.personalWord (!first)

def orderedMenus (first : Bool) : Menus Bool Bool Bool Unit Unit :=
  fun _ _ => [joint first, TerminalPeace.Supply.personalWord false, TerminalPeace.Supply.personalWord true]

abbrev menus := orderedMenus false

variable {cut : Conflict.Consumers.Evolving.C}
  (prior : StateAt Original.seed Original.community cut) (first : Bool)

private theorem cycle_pays_at_stock (attempt : Attempt input cut.raw people)
    (enough : TerminalPeace.Supply.Stocked attempt.before.raw)
    (menu : attempt.offers = orderedMenus first 0 cut.raw) :
    attempt.Succeeds ∧
      attempt.after.raw =
        { attempt.before.raw with clock := attempt.before.raw.clock + 1, round := attempt.before.raw.round + 1 } ∧
      attempt.items = TerminalPeace.Supply.physical.rawItems attempt.before.raw (joint first) := by
  have due : Supply.Period input cut.raw attempt.before.raw people (joint first) :=
    the_original_ordered_period_is_paid cut.raw attempt.before.raw enough first
  have paid := attempt.first_paid_word_controls_the_actual_effect (joint first) _ menu due
  have actual := (due.native_write attempt.before).2
  have literal := TerminalPeace.Supply.the_native_renewal_can_start_with_either_person attempt.before enough first
  exact ⟨paid.1,
    paid.2.1.trans ((congrArg (fun next : Native Bool Bool Bool Unit Unit => next.raw) actual.2).symm.trans literal.2.2.2),
    paid.2.2.trans ((congrArg ExecutionResult.items actual.1).symm.trans literal.2.1)⟩

private theorem event_menu (n : Nat) :
    (eventAt prior input cut.raw people (orderedMenus first) n).offers = orderedMenus first 0 cut.raw :=
  the_original_root_records_each_new_menu prior input cut.raw people (orderedMenus first) n

theorem the_ordered_source_reserve_survives (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    TerminalPeace.Supply.Stocked (eventAt prior input cut.raw people (orderedMenus first) n).before.raw := by
  induction n with
  | zero => exact enough
  | succ n stocked =>
    rw [the_next_attempt_reads_the_same_generated_physical_current]
    rw [(cycle_pays_at_stock first (eventAt prior input cut.raw people (orderedMenus first) n)
      stocked (event_menu prior first n)).2.1]
    exact stocked

theorem the_ordered_renewal_keeps_its_exact_successor
    (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    let attempt := eventAt prior input cut.raw people (orderedMenus first) n
    attempt.after.raw =
      { attempt.before.raw with clock := attempt.before.raw.clock + 1, round := attempt.before.raw.round + 1 } :=
  (cycle_pays_at_stock first _ (the_ordered_source_reserve_survives prior first enough n)
    (event_menu prior first n)).2.1

theorem every_ordered_due_visit_and_personal_exit_are_generated
    (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    ReadyAt prior input cut.raw people (orderedMenus first) n := by
  let attempt := eventAt prior input cut.raw people (orderedMenus first) n
  have stocked := the_ordered_source_reserve_survives prior first enough n
  refine ⟨(cycle_pays_at_stock first attempt stocked (event_menu prior first n)).1, ?_⟩
  intro person _
  rcases (attempt.personal person).pays_or_refuses with yes | no
  · exact yes
  · have listed : TerminalPeace.Supply.personalWord person ∈ (attempt.personal person).offers := by
      change TerminalPeace.Supply.personalWord person ∈ attempt.offers
      rw [event_menu prior first n]
      cases person <;> simp [orderedMenus]
    have paid := the_original_personal_period_is_paid cut.raw attempt.before.raw person
      (stocked person).1 (stocked person).2
    exact (((attempt.personal person).fails_iff.mp no) _ listed paid).elim

theorem the_ordered_source_clock_is_exact
    (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    clockAt prior input cut.raw people (orderedMenus first) n = cut.raw.clock + (n : ℚ) := by
  induction n with
  | zero => change cut.raw.clock = cut.raw.clock + (0 : ℚ); exact (add_zero _).symm
  | succ n previous =>
    have before := the_ordered_source_reserve_survives prior first enough n
    have paid := (cycle_pays_at_stock first (eventAt prior input cut.raw people (orderedMenus first) n)
      before (event_menu prior first n)).2.1
    unfold clockAt at previous ⊢
    rw [the_next_attempt_reads_the_same_generated_physical_current, paid, Nat.cast_succ]
    change (eventAt prior input cut.raw people (orderedMenus first) n).before.raw.clock + 1 = _
    rw [previous, add_assoc]

theorem the_ordered_source_hours_are_cofinal (enough : TerminalPeace.Supply.Stocked cut.raw) :
    ClockCofinal prior input cut.raw people (orderedMenus first) := by
  intro start bound
  obtain ⟨n, greater⟩ := exists_nat_gt (bound - cut.raw.clock)
  refine ⟨max start n, Nat.le_max_left _ _, ?_⟩
  have past : bound < clockAt prior input cut.raw people (orderedMenus first) n := by
    rw [the_ordered_source_clock_is_exact prior first enough n]
    linarith only [greater]
  exact past.trans_le (clock_mono prior input cut.raw people (orderedMenus first) (Nat.le_max_right _ _))

theorem the_ordered_renewal_keeps_its_exact_written_items
    (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    let attempt := eventAt prior input cut.raw people (orderedMenus first) n
    attempt.items = TerminalPeace.Supply.personalItems attempt.before.raw first 0 ++
      TerminalPeace.Supply.personalItems attempt.before.raw (!first) 2 := by
  let attempt := eventAt prior input cut.raw people (orderedMenus first) n
  have stocked := the_ordered_source_reserve_survives prior first enough n
  change attempt.items = _
  rw [(cycle_pays_at_stock first attempt stocked (event_menu prior first n)).2.2,
    RawLaw.rawItems, TerminalPeace.Supply.the_ordered_renewal_inventory_is_exact _ stocked first]

theorem every_due_visit_and_each_personal_exit_are_generated
    (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    ReadyAt prior input cut.raw people menus n :=
  every_ordered_due_visit_and_personal_exit_are_generated prior false enough n

theorem the_cofinal_clock_is_the_literal_original_paid_hour
    (enough : TerminalPeace.Supply.Stocked cut.raw) (n : Nat) :
    clockAt prior input cut.raw people menus n = cut.raw.clock + (n : ℚ) :=
  the_ordered_source_clock_is_exact prior false enough n

theorem the_original_paid_hours_are_cofinal_from_each_real_cut
    (enough : TerminalPeace.Supply.Stocked cut.raw) :
    ClockCofinal prior input cut.raw people menus :=
  the_ordered_source_hours_are_cofinal prior false enough

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.OriginalProgramme
