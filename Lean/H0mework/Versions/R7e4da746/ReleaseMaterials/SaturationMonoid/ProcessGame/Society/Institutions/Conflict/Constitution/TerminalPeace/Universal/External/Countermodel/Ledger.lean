import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Liability

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt_append next)
open Reparation.Actual Reparation.Actual.Allocation

noncomputable section

abbrev afterAttack (past : Original.Word) := past ++ [Original.attack]
abbrev afterAttackHead (past : Original.Word) := afterAttack past ++ [none]
abbrev afterReturn (past : Original.Word) := afterAttackHead past ++ [returned]
abbrev nextPast (past : Original.Word) := afterReturn past ++ [none]

theorem nextPast_eq (past : Original.Word) : nextPast past = past ++ cycle := by
  simp only [afterReturn, afterAttackHead, afterAttack, nextPast, List.append_assoc]
  rfl

private theorem middle_eq (past : Original.Word) : before (afterAttackHead past) = middle (before past) := by
  exact (congrArg before (List.append_assoc past [Original.attack] [none])).trans
    (endAt_append Original.seed past firstLeg)

private theorem native_cut (past : Original.Word) (input : Input Bool Bool Bool Unit Unit) :
    before (past ++ [input]) = next (before past) input :=
  endAt_append Original.seed past [input]

private theorem no_charge_without_original_signatures
    {past : Original.Word} (state : ExternalState past) (input : Input Bool Bool Bool Unit Unit)
    (body : Original.Item) (literal : Boundary.Actual.items (before past) input = [body])
    (signer : body.request.signer = true)
    (oldVictims : ∀ row ∈ state.stack.balances ++
      (openings Original.seed Original.community past input).map (fun origin => (origin, Reparation.Actual.opening origin)),
      row.1.key.1 = false) :
    (advance state input).stack.balances = state.stack.balances ++
      (openings Original.seed Original.community past input).map (fun origin => (origin, Reparation.Actual.opening origin)) := by
  let rows := state.stack.balances ++
    (openings Original.seed Original.community past input).map (fun origin => (origin, Reparation.Actual.opening origin))
  have width : (Boundary.Actual.items (before past) input).length = 1 := congrArg List.length literal
  obtain ⟨site, positions⟩ := List.length_eq_one_iff.mp (List.length_finRange.trans width)
  have sites : itemPositions (seed := Original.seed) past input = [site] := positions
  rw [written_balances]
  unfold atInput
  rw [sites]
  let plan := atItem Original.seed past input site rows
  change plan.changes.result = rows
  have actualItem : originalItem Original.seed past input site = body := by
    apply List.mem_singleton.mp
    rw [← literal]
    exact List.getElem_mem _
  have kept := Changes.kept_without_the_original_victim_signatures past input site plan.changes plan.original (by
    intro row old
    rw [actualItem, signer, oldVictims row old]
    decide)
  rw [kept, Changes.unchanged_result]

private theorem an_empty_native_write_keeps_every_balance
    {past : Original.Word} (state : ExternalState past) (input : Input Bool Bool Bool Unit Unit)
    (empty : Boundary.Actual.items (before past) input = []) :
    (advance state input).stack.balances = state.stack.balances := by
  have noOpening : openings Original.seed Original.community past input = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ empty]
    rfl
  rw [written_balances, noOpening, List.map_nil, List.append_nil]
  exact (no_original_items_keeps_rows past input state.stack.balances empty).1

/-- Both material moves and their accounting writes consume the last actual
joint state, including the original cleared balance. -/
def advanceCycle {past : Original.Word} (state : ExternalState past) : ExternalState (nextPast past) :=
  advance (advance (advance (advance state Original.attack) none) returned) none

theorem the_cycle_writes_exactly_one_new_unpaid_row
    {past : Original.Word} (state : ExternalState past) (actual : CycleAt (before past))
    (oldVictims : ∀ row ∈ state.stack.balances, row.1.key.1 = false) :
    let loss := levyOccurrence past actual
    (advanceCycle state).stack.balances = state.stack.balances ++ [(loss, Reparation.Actual.opening loss)] := by
  let loss := levyOccurrence past actual
  let rows := state.stack.balances ++ [(loss, Reparation.Actual.opening loss)]
  have allVictims : ∀ row ∈ rows, row.1.key.1 = false := by
    intro row listed
    rcases List.mem_append.mp listed with old | new
    · exact oldVictims row old
    · rcases List.mem_singleton.mp new with rfl
      rfl
  let attack := advance state Original.attack
  have attackWrites : attack.stack.balances = rows := by
    have kept := no_charge_without_original_signatures state Original.attack _
      (original_levy_items actual) rfl (by
        rw [the_levy_opens_exactly_its_original_loss past actual]
        exact allVictims)
    rw [the_levy_opens_exactly_its_original_loss past actual] at kept
    exact kept
  let drained := advance attack none
  have drainKeeps : drained.stack.balances = rows := by
    have empty : Boundary.Actual.items (before (afterAttack past)) none = [] := by
      rw [native_cut]
      exact original_levy_drain actual
    exact (an_empty_native_write_keeps_every_balance attack none empty).trans attackWrites
  let paid := advance drained returned
  have returnedKeeps : paid.stack.balances = rows := by
    have actualReturn : Boundary.Actual.items (before (afterAttackHead past)) returned =
        [⟨0, (middle (before past)).raw, Conflict.Consumers.Evolving.returnAt 6⟩] := by
      rw [middle_eq]
      exact original_return_items actual
    have noOpening : openings Original.seed Original.community (afterAttackHead past) returned = [] := by
      have safe : Boundary.Actual.damages (before (afterAttackHead past)) returned Original.community = [] := by
        rw [middle_eq]
        exact the_payers_material_return_opens_no_reverse_loss actual
      unfold openings
      rw [safe]
      rfl
    have kept := no_charge_without_original_signatures drained returned _ actualReturn rfl (by
      rw [noOpening, List.map_nil, List.append_nil, drainKeeps]
      exact allVictims)
    rw [noOpening, List.map_nil, List.append_nil] at kept
    exact kept.trans drainKeeps
  have empty : Boundary.Actual.items (before (afterReturn past)) none = [] := by
    rw [native_cut, middle_eq]
    exact original_return_drain actual
  exact (an_empty_native_write_keeps_every_balance paid none empty).trans returnedKeeps

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
