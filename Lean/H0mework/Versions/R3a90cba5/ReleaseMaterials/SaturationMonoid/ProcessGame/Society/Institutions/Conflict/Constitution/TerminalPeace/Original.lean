import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Cut
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Consumers.Joint.Opening
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Protection

set_option autoImplicit false
set_option maxRecDepth 8192

open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence
open private no_foreign_loss_when_every_debit_is_own from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Consumers.Joint.Opening
open private forPositions from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Input

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (compact oldRaw destroy levy sourceInput sourceRead)
open Reparation.Consumers (address)
open Reparation.Actual Reparation.Actual.Allocation
open Quantities.Execution (endAt inventory)

noncomputable section

def state : State seed community history := run seed community history

def balance : Balance := opening occurrence

theorem balance_six : balance.remaining = 6 := loss_six

private theorem prior_has_no_loss : (run seed community prior).stack.balances = [] := by
  apply List.map_eq_nil_iff.mp
  rw [the_live_ledger_contains_exactly_the_original_losses]
  apply no_foreign_loss_when_every_debit_is_own
  have original := Conflict.Root.trace_before_prefix seed _ [destroy] [levy] actual_trace
  have items : inventory seed prior = [⟨0, seed.raw, destroy⟩] :=
    (Quantities.Execution.primitive_inventory original 0).trans rfl
  intro item listed entry debited
  rw [items] at listed
  rcases List.mem_singleton.mp listed with rfl
  change entry ∈ (Physical.Public.interpreter seed.native.input).actualDebit seed.raw destroy at debited
  rw [sourceInput, sourceRead] at debited
  exact (by decide +kernel : ∀ part ∈ (Physical.Public.interpreter compact).actualDebit oldRaw destroy,
    part.1.1 = destroy.signer) entry debited

private theorem the_levy_has_one_harmed_address (original : Boundary.Actual.DamageAt before attack community) :
    original.key = address := by
  have item : original.item = ⟨0, before.raw, levy⟩ := item_is_literal _
  have valid := original.actual_foreign_debit.2.1
  have key := original_key original
  rw [item] at valid key
  unfold keysAt at key
  rw [RawLaw.actualDebit, if_pos valid] at key
  change original.key ∈ [address] at key
  exact List.mem_singleton.mp key

private theorem the_levy_has_only_the_original_damage : Boundary.Actual.damages before attack community = [damage] := by
  let losses := Boundary.Actual.damages before attack community
  have width : (Boundary.Actual.items before attack).length = 1 :=
    congrArg List.length original_levy_items
  have unique (original : Boundary.Actual.DamageAt before attack community) : original = damage := by
    have first : original.position.val < 1 := original.position.isLt.trans_eq width
    have second : damage.position.val < 1 := damage.position.isLt.trans_eq width
    have same : original.position = damage.position := Fin.ext (by omega)
    apply Subtype.ext
    exact Prod.ext same (the_levy_has_one_harmed_address original)
  have present : damage ∈ losses := Boundary.Actual.every_actual_debit_is_assessed damage
  have distinct : losses.Nodup := Boundary.Actual.each_damage_address_occurs_once _ _ _
  change losses = [damage]
  cases exactLosses : losses with
  | nil => exact (List.not_mem_nil (exactLosses ▸ present)).elim
  | cons first rest =>
    have empty : rest = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro next listed
      exact (List.nodup_cons.mp (exactLosses ▸ distinct)).1 ((unique next).trans (unique first).symm ▸ listed)
    rw [unique first, empty]

theorem exact_opening : openings seed community prior attack = [occurrence] := by
  unfold openings
  rw [the_levy_has_only_the_original_damage]
  rfl

private theorem levy_positions : itemPositions (seed := seed) prior attack = [position] := by
  have width : (Boundary.Actual.items before attack).length = 1 :=
    congrArg List.length original_levy_items
  obtain ⟨site, only⟩ := List.length_eq_one_iff.mp (List.length_finRange.trans width)
  change List.finRange (Boundary.Actual.items before attack).length = [position]
  rw [only]
  congr 1
  have first := site.isLt.trans_eq width
  have second := position.isLt.trans_eq width
  exact Fin.ext (by omega)

private theorem the_levy_cannot_sign_its_victims_receipt :
    (atInput prior attack [(occurrence, balance)]).result = [(occurrence, balance)] := by
  unfold atInput
  rw [levy_positions]
  let plan := atItem seed prior attack position [(occurrence, balance)]
  change plan.changes.result = _
  have noSignature := Changes.kept_without_the_original_victim_signatures prior attack position
    plan.changes plan.original (by
      intro row listed
      rcases List.mem_singleton.mp listed with rfl
      change (Boundary.Actual.items before attack)[position].request.signer ≠ occurrence.key.1
      rw [item_is_literal]
      decide)
  rw [noSignature, Changes.unchanged_result]

theorem at_its_birth_the_whole_ledger_opens_six :
    (run seed community born).stack.balances = [(occurrence, balance)] := by
  unfold born
  rw [run_snoc, written_balances, prior_has_no_loss, exact_opening]
  exact the_levy_cannot_sign_its_victims_receipt

theorem balances_exact : state.stack.balances = [(occurrence, balance)] := by
  unfold state
  rw [exact_history, run_snoc, written_balances]
  have noOpening : openings seed community born none = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ levy_native_has_no_second_item]
    rfl
  rw [noOpening, List.map_nil, List.append_nil]
  exact (no_original_items_keeps_rows born none _ levy_native_has_no_second_item).1.trans
    at_its_birth_the_whole_ledger_opens_six

theorem the_original_loss_is_the_only_filed_occurrence : originalLosses seed community history = [occurrence] := by
  rw [← the_live_ledger_contains_exactly_the_original_losses]
  change state.stack.balances.map Prod.fst = _
  rw [balances_exact]
  rfl

theorem terminal_original_six_is_a_live_row : ∃ row, state.read row = .inr (occurrence, balance) :=
  state.every_balance_is_a_row_of_the_current _ (by rw [balances_exact]; exact List.mem_singleton_self _)

theorem whole : Quantities.Recorded seed history := Quantities.record seed history

theorem authority : SourceAuthority seed history := by
  obtain ⟨checked, _, _⟩ := Consumers.the_original_approved_material_word_is_refused_at_settlement
  exact checked

theorem refusal_preserves_the_whole_six :
    let written := publish seed community history
    (∃ checked issue, written.result = .settlementRefused checked issue) ∧
      written.next = state ∧ written.next.stack.balances = [(occurrence, balance)] ∧
      Quantities.Recorded seed history :=
  ⟨Consumers.the_original_approved_material_word_is_refused_at_settlement, rfl, balances_exact, whole⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original

-- The suggestion index unfolds the full dependent ledger type of this row.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "terminal_original_six_is_a_live_row"
