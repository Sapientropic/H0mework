import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Receipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Gate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next)
open ExposureGuard ExposureGuard.Receipts
open Reparation Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Reparation.Actual.Script Party Good Port Technology Instrument}
  {input : Reparation.Actual.Input Party Good Port Technology Instrument}

private theorem a_damage_free_position_has_no_cross_boundary_offer
    (answers : OwnerAnswers seed) (position : Position seed past input)
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (key : Key Party Good) (foreign : community key.1 ≠ community key.2.1) :
    personalOffer answers past input position key = none := by
  cases offered : personalOffer answers past input position key with
  | none => rfl
  | some receipt =>
    have signed := (a_selected_receipt_reads_the_original_victim_lane answers past input position key receipt offered).2
    have positive : 0 < receiptCredit seed.native.input.law (originalItem seed past input position) key := by
      rw [← item_offer_is_the_actual_signed_credit, Offer.quantity, signed]
      exact receipt.positive
    let literal : SignedReceipt seed key := ⟨past, input, position, positive⟩
    obtain ⟨damage, _, _, _⟩ := Material.every_cross_community_receipt_opens_its_equal_reverse_damage literal foreign
    have listed := Boundary.Actual.every_actual_debit_is_assessed damage
    rw [safe] at listed
    exact (List.not_mem_nil listed).elim

private theorem moves_keep_all_rows_when_cross_boundary_offers_are_absent
    {offer : Offer seed} {rows : List (Occurrence seed community × Balance)}
    (moves : Changes rows) (uses : moves.uses offer)
    (absent : ∀ key : Key Party Good, community key.1 ≠ community key.2.1 → offer key = none) :
    moves.result = rows := by
  induction moves with
  | nil => rfl
  | @cons row _ head tail earlier =>
    have actual : head.uses offer ∧ tail.uses offer := uses
    have nextRows := earlier actual.2
    cases head with
    | keep => exact congrArg (row :: ·) nextRows
    | pay share within =>
      have offered : offer row.1.key = some share.receipt := actual.1
      have foreign := row.1.damage.actual_foreign_debit.1.1
      rw [absent _ foreign] at offered
      cases offered

private theorem original_position_fold_keeps_balances
    (answers : OwnerAnswers seed) (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (positions : List (Position seed past input)) (state : StateAt seed community (next (endAt seed past) input)) :
    (consumePositions answers past input positions state).stack.balances = state.stack.balances := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest earlier =>
    rw [consumePositions, earlier, StateAt.consume_balances]
    exact moves_keep_all_rows_when_cross_boundary_offers_are_absent _ (atPersonalItem answers past input position
      state.stack.balances).original (fun key => a_damage_free_position_has_no_cross_boundary_offer answers position safe key)

/-- With the installed receipt interpretation, any positive payment
on an original cross-community row would open a new reverse loss. -/
theorem a_damage_free_original_write_keeps_every_balance
    (answers : OwnerAnswers seed) (state : State seed community past)
    (safe : Boundary.Actual.damages (endAt seed past) input community = []) :
    (writeTick answers state input).stack.balances = state.stack.balances := by
  rw [writeTick_balances, original_position_fold_keeps_balances answers safe, posted_balances]
  simp [openings, safe]

theorem the_revised_visit_keeps_the_exact_original_reparation_portfolio
    {anchor : Word} {viable : Word → Prop} (prior : Visit seed community anchor viable)
    (answers : OwnerAnswers seed) (check : Probe viable) (input : Input) :
    (prior.step answers (damageGate community) check input).state.stack.balances = prior.state.stack.balances := by
  let selected := prior.verdict answers (damageGate community) check input
  change (writeAfter answers prior.state selected.emitted).stack.balances = prior.state.stack.balances
  have harmless (written : Input) (safe : Boundary.Actual.damages (endAt seed prior.history) written community = []) :
      (writeAfter answers prior.state [written]).stack.balances = prior.state.stack.balances := by
    change (writeAfter answers prior.state ([] ++ [written])).stack.balances = prior.state.stack.balances
    rw [writeAfter_snoc, history_cast_preserves_balances]
    exact (a_damage_free_original_write_keeps_every_balance answers _ (by rwa [List.append_nil])).trans
      (by rw [writeAfter, List.reverseRecOn_nil, history_cast_preserves_balances])
  generalize selected = outcome
  cases outcome with
  | retained => rw [Selection.emitted, writeAfter, List.reverseRecOn_nil, history_cast_preserves_balances]
  | stopped _ empty _ =>
    exact harmless stop (Boundary.Actual.no_material_write_has_no_damage _ _ _ empty)
  | accepted _ additional _ =>
    exact harmless input ((passes_exactly_the_original_damage_free_inputs _ _ _ _ _).mp additional)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
