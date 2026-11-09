import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Ledger
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append)
open Reparation.Actual

noncomputable section

abbrev Proposal := Input Bool Bool Bool Unit Unit

/-- A single external script repeats the old command and the payer's
return, consuming each existing native head before the next proposal. -/
def inputAt (tick : Nat) : Proposal :=
  match tick % 4 with
  | 0 => Original.attack
  | 2 => returned
  | _ => none

def historyAt : Nat → Original.Word
  | 0 => Settlement.settledHistory
  | tick + 1 => historyAt tick ++ [inputAt tick]

def visitAt : (tick : Nat) → ExternalState (historyAt tick)
  | 0 => Settlement.settled
  | tick + 1 => advance (visitAt tick) (inputAt tick)

theorem every_external_input_consumes_the_retained_original_visit (tick : Nat) :
    visitAt (tick + 1) = advance (visitAt tick) (inputAt tick) :=
  rfl

theorem history_length (tick : Nat) : (historyAt tick).length = Settlement.settledHistory.length + tick := by
  induction tick with
  | zero => simp only [historyAt, Nat.add_zero]
  | succ tick earlier => simp only [historyAt, List.length_append, List.length_singleton, earlier, Nat.add_succ]

theorem history_extends {first later : Nat} (order : first ≤ later) :
    (historyAt first).IsPrefix (historyAt later) := by
  induction order with
  | refl => exact List.prefix_rfl
  | step _ earlier => exact earlier.trans (List.prefix_append _ _)

theorem starts_with_levy (n : Nat) : inputAt (4 * n) = Original.attack := by
  unfold inputAt
  rw [show (4 * n) % 4 = 0 by omega]
  rfl

private theorem drains_levy (n : Nat) : inputAt (4 * n + 1) = none := by
  unfold inputAt
  rw [show (4 * n + 1) % 4 = 1 by omega]
  rfl

private theorem returns_stock (n : Nat) : inputAt (4 * n + 1 + 1) = returned := by
  unfold inputAt
  rw [show (4 * n + 1 + 1) % 4 = 2 by omega]
  rfl

private theorem drains_return (n : Nat) : inputAt (4 * n + 1 + 1 + 1) = none := by
  unfold inputAt
  rw [show (4 * n + 1 + 1 + 1) % 4 = 3 by omega]
  rfl

private theorem four_ticks (n : Nat) : 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 := by omega

abbrev roundPast (n : Nat) := historyAt (4 * n)
abbrev roundState (n : Nat) := visitAt (4 * n)
abbrev roundCut (n : Nat) := before (roundPast n)

theorem history_of_a_cycle (n : Nat) : roundPast (n + 1) = nextPast (roundPast n) := by
  change historyAt (4 * (n + 1)) = _
  rw [four_ticks]
  simp only [historyAt, starts_with_levy, drains_levy, returns_stock, drains_return,
    nextPast, afterReturn, afterAttackHead, afterAttack]

private theorem four_advances_congr {past : Original.Word} (state : ExternalState past)
    {a b c d a' b' c' d' : Proposal}
    (first : a = a') (second : b = b') (third : c = c') (last : d = d') :
    HEq (advance (advance (advance (advance state a) b) c) d)
      (advance (advance (advance (advance state a') b') c') d') := by
  cases first
  cases second
  cases third
  cases last
  rfl

theorem four_actual_visits_are_the_original_cycle (n : Nat) :
    HEq (roundState (n + 1)) (advanceCycle (roundState n)) := by
  change HEq (visitAt (4 * (n + 1))) _
  rw [four_ticks]
  exact four_advances_congr (roundState n)
    (starts_with_levy n) (drains_levy n) (returns_stock n) (drains_return n)

private theorem balances_of_heq {left right : Original.Word} (histories : left = right)
    {prior : ExternalState left} {next : ExternalState right} (compared : HEq prior next) :
    prior.stack.balances = next.stack.balances := by
  subst right
  exact congrArg (fun state : ExternalState left => state.stack.balances) (eq_of_heq compared)

theorem rounds_follow_their_same_whole_account (n : Nat) :
    (roundState (n + 1)).stack.balances = (advanceCycle (roundState n)).stack.balances :=
  balances_of_heq (history_of_a_cycle n) (four_actual_visits_are_the_original_cycle n)

theorem recurring_cuts_use_the_same_original_material (n : Nat) : CycleAt (roundCut n) := by
  induction n with
  | zero => exact actual_opening_cycle
  | succ n earlier =>
    change CycleAt (endAt Original.seed (roundPast (n + 1)))
    rw [history_of_a_cycle, nextPast_eq, endAt_append]
    exact the_real_cycle_restores_its_original_material_state earlier

theorem recurring_cuts_admit_both_material_legs (n : Nat) :
    SourceAuthority (roundCut n) cycle :=
  the_original_law_admits_both_material_legs (recurring_cuts_use_the_same_original_material n)

private theorem clock_monotone {i j : Nat} (order : i ≤ j) :
    (before (historyAt i)).raw.clock ≤ (before (historyAt j)).raw.clock := by
  obtain ⟨tail, exactHistory⟩ := history_extends order
  change (endAt Original.seed (historyAt i)).raw.clock ≤ (endAt Original.seed (historyAt j)).raw.clock
  rw [← exactHistory, endAt_append]
  exact Quantities.Execution.the_actual_script_never_runs_the_clock_backwards _ _

theorem physical_clock_is_four_at_every_external_visit (tick : Nat) :
    (before (historyAt tick)).raw.clock = 4 := by
  have opening : (before (historyAt 0)).raw.clock = 4 :=
    congrArg (fun raw : Original.Raw => raw.clock) Settlement.settled_raw
  have later : (before (historyAt (4 * tick))).raw.clock = 4 :=
    congrArg (fun raw : Original.Raw => raw.clock) (recurring_cuts_use_the_same_original_material tick).physical
  have low := clock_monotone (Nat.zero_le tick)
  have high := clock_monotone (i := tick) (j := 4 * tick) (by omega)
  rw [opening] at low
  rw [later] at high
  exact le_antisymm high low

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
