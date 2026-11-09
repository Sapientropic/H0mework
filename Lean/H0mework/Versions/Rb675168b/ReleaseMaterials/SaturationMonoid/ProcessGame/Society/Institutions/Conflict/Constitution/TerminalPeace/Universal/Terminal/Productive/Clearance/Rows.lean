import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Budget
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Monotone
import Mathlib.Data.List.Forall2

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next)
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions)
open private live_motion_never_increases from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Monotone

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Proposal" => Reparation.Actual.Input Party Good Port Technology Instrument

def BalancesDecrease (before after : List Row) : Prop :=
  List.Forall₂ (fun old new => old.1 = new.1 ∧ new.2.remaining ≤ old.2.remaining) before after

private theorem balances_decrease_refl (rows : List Row) : BalancesDecrease rows rows := by
  induction rows with
  | nil => exact .nil
  | cons row rest prior => exact .cons ⟨rfl, le_rfl⟩ prior

private theorem balances_decrease_trans {before middle after : List Row}
    (first : BalancesDecrease before middle) (last : BalancesDecrease middle after) :
    BalancesDecrease before after := by
  induction first generalizing after with
  | nil => cases last; exact .nil
  | cons head _ earlier =>
    cases last with
    | cons here tail => exact .cons ⟨head.1.trans here.1, here.2.trans head.2⟩ (earlier tail)

private theorem stack_balances_decrease {N J : WorldRelationNetwork}
    {before after : Stack seed community N J} (motion : Stack.Move before after) :
    BalancesDecrease before.balances after.balances := by
  induction motion with
  | base => exact .nil
  | add move original view payment earlier =>
    unfold BalancesDecrease at earlier ⊢
    rw [Stack.balances, Stack.balances]
    exact List.rel_append earlier (.cons ⟨rfl, live_motion_never_increases original payment⟩ .nil)

theorem BalancesDecrease.cellDue_le {before after : List Row} (changed : BalancesDecrease before after)
    (cell : MaterialCell Party Good) : cellDue after cell ≤ cellDue before cell := by
  induction changed with
  | nil => exact le_rfl
  | cons head _ older =>
    rw [cellDue, cellDue, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, head.1]
    split
    · exact add_le_add head.2 older
    · exact add_le_add_right older _

variable (answers : ReceiptAnswers seed) {past : Reparation.Actual.Script Party Good Port Technology Instrument}
  {input : Reparation.Actual.Input Party Good Port Technology Instrument}

private theorem all_positions_decrease
    (positions : List (Position seed past input))
    (state : StateAt seed community (next (endAt seed past) input)) :
    BalancesDecrease state.stack.balances
      (Settlement.writePositions answers past input positions state).stack.balances := by
  induction positions generalizing state with
  | nil => exact balances_decrease_refl _
  | cons site tail older =>
    apply balances_decrease_trans ?_ (older (Settlement.writePosition answers past input site state))
    rw [Settlement.writePosition_balances]
    exact stack_balances_decrease (Settlement.atPosition answers past input site state).move

theorem tick_decreases_the_same_balances (state : State seed community past)
    (safe : Boundary.Actual.damages (endAt seed past) input community = []) :
    BalancesDecrease state.stack.balances (Settlement.writeTick answers state input).stack.balances := by
  have changed := all_positions_decrease answers (itemPositions past input) (posted state input)
  have unchanged : (posted state input).stack.balances = state.stack.balances := by
    rw [posted_balances]
    simp [openings, safe]
  rw [Settlement.writeTick_balances, ← unchanged]
  exact changed

variable (anchor : Reparation.Actual.Script Party Good Port Technology Instrument)

theorem eligible_append {front tail : Word} :
    Occurrence.EligibleFrom community answers anchor past (front ++ tail) ↔
      Occurrence.EligibleFrom community answers anchor past front ∧
      Occurrence.EligibleFrom community answers anchor (past ++ front) tail := by
  induction front generalizing past with
  | nil => simp [Occurrence.EligibleFrom]
  | cons head rest older =>
    change (Occurrence.EligibleAt community answers anchor past head ∧
      Occurrence.EligibleFrom community answers anchor (past ++ [head]) (rest ++ tail)) ↔ _
    rw [older, ← and_assoc]
    simp only [Occurrence.EligibleFrom, List.append_assoc, List.singleton_append]

/-- A safe funding word can already discharge some debt. Each original
row follows its actual settlement motion throughout the generated prefix. -/
theorem a_safe_suffix_can_only_decrease_the_original_balances (state : State seed community past)
    (word : Word) (safe : Occurrence.EligibleFrom community answers anchor past word) :
    BalancesDecrease state.stack.balances (Occurrence.writeAfter answers state word).stack.balances := by
  induction word using List.reverseRecOn with
  | nil =>
    rw [Occurrence.writeAfter_nil_balances]
    exact balances_decrease_refl _
  | append_singleton front input earlier =>
    have pieces := (eligible_append answers anchor (past := past) (front := front) (tail := [input])).mp safe
    rw [Occurrence.writeAfter_snoc_balances]
    exact balances_decrease_trans (earlier pieces.1)
      (tick_decreases_the_same_balances answers (Occurrence.writeAfter answers state front) pieces.2.1.2)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
