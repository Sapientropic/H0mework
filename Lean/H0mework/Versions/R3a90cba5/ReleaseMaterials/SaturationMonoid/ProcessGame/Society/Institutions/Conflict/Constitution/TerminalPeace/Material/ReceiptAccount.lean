import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Bilateral
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts.Writer

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (compact)
open ExposureGuard ExposureGuard.Receipts
open Reparation Reparation.Actual Reparation.Actual.Allocation
open Reparation.Consumers (receipt)
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence
open private the_original_item_at_the_receipt_position from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Bilateral

noncomputable section

private abbrev ReverseDamage := Boundary.Actual.DamageAt Original.cut receiptInput Original.community

private theorem reverse_exists : ∃ damage : ReverseDamage,
    damage.position = receiptPosition ∧ damage.key = (true, false, false) ∧ damage.quantity = 6 := by
  have actual := every_cross_community_receipt_opens_its_equal_reverse_damage
    (community := Original.community) originalReceiptSix (by decide)
  rw [the_original_receipt_delivers_exactly_six] at actual
  exact actual

def reverseDamage : ReverseDamage := Classical.choose reverse_exists

private theorem reverse_exact : reverseDamage.position = receiptPosition ∧
    reverseDamage.key = (true, false, false) ∧ reverseDamage.quantity = 6 :=
  Classical.choose_spec reverse_exists

def reverseOccurrence : Occurrence Original.seed Original.community :=
  ⟨Original.history, receiptInput, reverseDamage⟩

theorem the_reverse_row_has_the_original_key_and_quantity :
    reverseOccurrence.key = (true, false, false) ∧ reverseOccurrence.quantity = 6 :=
  reverse_exact.2

private theorem receipt_width : (Boundary.Actual.items Original.cut receiptInput).length = 1 :=
  congrArg List.length the_six_receipt_is_an_actual_instruction

private theorem one_position (position : Fin (Boundary.Actual.items Original.cut receiptInput).length) :
    position = receiptPosition := by
  apply Fin.ext
  have inside := position.isLt.trans_eq receipt_width
  change position.val = 0
  omega

private theorem receipt_positions :
    itemPositions (seed := Original.seed) Original.history receiptInput = [receiptPosition] := by
  have width : (List.finRange (Boundary.Actual.items Original.cut receiptInput).length).length = 1 :=
    List.length_finRange.trans receipt_width
  obtain ⟨position, same⟩ := List.length_eq_one_iff.mp width
  change List.finRange (Boundary.Actual.items Original.cut receiptInput).length = [receiptPosition]
  rw [same, one_position position]

private theorem the_receipt_can_open_only_its_reverse_row (damage : ReverseDamage) :
    damage = reverseDamage := by
  have keys := original_key damage
  unfold keysAt at keys
  have literal : damage.item = ⟨0, Original.cut.raw, receipt 6⟩ :=
    the_original_item_at_the_receipt_position damage.position
  rw [literal] at keys
  change damage.key ∈ ((Physical.Public.interpreter Original.cut.native.input).actualDebit
    Original.cut.raw (receipt 6)).map (fun entry => (entry.1.1, (receipt 6).signer, entry.1.2)) at keys
  rw [Original.same_source, Original.cut_raw] at keys
  have actualKeys : ((Physical.Public.interpreter compact).actualDebit (Original.snapshot 111 113)
      (receipt 6)).map (fun entry => (entry.1.1, (receipt 6).signer, entry.1.2)) =
        [(true, false, false)] := by decide +kernel
  rw [actualKeys] at keys
  apply Subtype.ext
  exact Prod.ext ((one_position damage.position).trans reverse_exact.1.symm)
    ((List.mem_singleton.mp keys).trans reverse_exact.2.1.symm)

private theorem reverse_opening :
    openings Original.seed Original.community Original.history receiptInput = [reverseOccurrence] := by
  let damages := Boundary.Actual.damages Original.cut receiptInput Original.community
  have inside : reverseDamage ∈ damages := Boundary.Actual.every_actual_debit_is_assessed _
  have noCopies : damages.Nodup := Boundary.Actual.each_damage_address_occurs_once _ _ _
  have one : damages = [reverseDamage] := by
    cases exact : damages with
    | nil => exact (List.not_mem_nil (exact ▸ inside)).elim
    | cons first rest =>
      have empty : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other listed
        have same := (the_receipt_can_open_only_its_reverse_row other).trans
          (the_receipt_can_open_only_its_reverse_row first).symm
        exact (List.nodup_cons.mp (exact ▸ noCopies)).1 (same ▸ listed)
      rw [empty, the_receipt_can_open_only_its_reverse_row first]
  change damages.map (fun damage => (⟨Original.history, receiptInput, damage⟩ :
    Occurrence Original.seed Original.community)) = [reverseOccurrence]
  rw [one]
  rfl

private abbrev Row := Occurrence Original.seed Original.community × Balance
private abbrev old : Row := (Original.occurrence, Original.balance)
private abbrev fresh : Row := (reverseOccurrence, opening reverseOccurrence)

private theorem signed_offer_pays_old_and_keeps_reverse
    (answers : OwnerAnswers Original.seed)
    (victim : answers Original.history receiptInput receiptPosition false = true) :
    ((atPersonalItem answers Original.history receiptInput receiptPosition [old, fresh]).changes.result.map
      fun row => (row.1, row.2.remaining)) =
        [(Original.occurrence, 0), (reverseOccurrence, 6)] := by
  let offer := personalOffer answers Original.history receiptInput receiptPosition
  have originalOffer : offer old.1.key = some originalReceiptSix := by
    change (if answers Original.history receiptInput receiptPosition false then
      itemOffer Original.seed Original.history receiptInput receiptPosition old.1.key else none) = _
    rw [if_pos victim]
    have positive : 0 < receiptCredit Original.seed.native.input.law
      (originalItem Original.seed Original.history receiptInput receiptPosition) old.1.key :=
      originalReceiptSix.positive
    simp only [itemOffer, dif_pos positive]
    rfl
  have noReverseOffer : offer fresh.1.key = none := by
    apply another_signer_cannot_supply_a_receipt
    change (Boundary.Actual.items Original.cut receiptInput)[receiptPosition].request.signer ≠ reverseOccurrence.key.1
    rw [the_original_item_at_the_receipt_position, the_reverse_row_has_the_original_key_and_quantity.1]
    decide
  have onOld : later Original.occurrence originalReceiptSix := by
    left
    exact ⟨[none], Original.exact_history⟩
  have oldQuantity : ((Capacity.full offer).balance old.1.key).remaining = 6 := by
    change offer.quantity old.1.key = 6
    rw [Offer.quantity, originalOffer]
    exact the_original_receipt_delivers_exactly_six
  have eligibleOld : eligible offer old = 6 := by
    classical
    simp [eligible, originalOffer, onOld, Original.balance_six]
  have eligibleReverse : eligible offer fresh = 0 := by
    classical
    simp [eligible, noReverseOffer]
  let first := allot offer (Capacity.full offer) old
  let second := allot offer first.remainder fresh
  have paid : first.change.amount = 6 := by
    rw [first.amount_exact, oldQuantity, eligibleOld, min_self]
  have untouched : second.change.amount = 0 := by
    rw [second.amount_exact, eligibleReverse, min_eq_right (first.remainder.balance fresh.1.key).nonnegative]
  change [(old.1, first.change.after.remaining), (fresh.1, second.change.after.remaining)] = _
  rw [first.change.after_exact, second.change.after_exact, paid, untouched]
  change [(Original.occurrence, Original.balance.remaining - 6),
    (reverseOccurrence, reverseOccurrence.quantity - 0)] = _
  rw [Original.balance_six, the_reverse_row_has_the_original_key_and_quantity.2, sub_self, sub_zero]

theorem the_victims_receipt_really_closes_the_old_six_and_writes_the_reverse_six
    (answers : OwnerAnswers Original.seed)
    (victim : answers Original.history receiptInput receiptPosition false = true)
    (debtor : answers Original.history receiptInput receiptPosition true = true) :
    Admitted [false, true] answers Original.history receiptInput ∧
      ((writeTick answers Original.state receiptInput).stack.balances.map fun row => (row.1, row.2.remaining)) =
        [(Original.occurrence, 0), (reverseOccurrence, 6)] := by
  refine ⟨(the_original_six_transfer_requires_exactly_the_two_personal_answers answers).mpr ⟨victim, debtor⟩, ?_⟩
  rw [writeTick_balances, receipt_positions, consumePositions, consumePositions, StateAt.consume_balances]
  have exactRows : (posted Original.state receiptInput).stack.balances = [old, fresh] := by
    rw [posted_balances, Original.balances_exact, reverse_opening]
    rfl
  rw [exactRows]
  exact signed_offer_pays_old_and_keeps_reverse answers victim

#print axioms the_victims_receipt_really_closes_the_old_six_and_writes_the_reverse_six

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
