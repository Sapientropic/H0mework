import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Balance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (compact returnAt)
open Quantities.Execution
open Reparation Reparation.Actual
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

def payerInput : Input Bool Bool Bool Unit Unit := some (.primitive (returnAt 6))
def payerScript : Original.Word := primitiveScript [returnAt 6]

private theorem valid_payer : (Physical.Public.interpreter Original.cut.native.input).Valid
    Original.cut.raw (returnAt 6) := by
  rw [Original.same_source, Original.cut_raw]
  decide +kernel

theorem the_payer_returns_six_at_the_original_root :
    Trace Original.cut [returnAt 6] (endAt Original.cut payerScript) := by
  apply (pay_checked_primitives Original.cut [returnAt 6] 0 Original.ready Original.review _ _).1
  · intro instruction listed
    rw [List.mem_singleton.mp listed]
    rfl
  · intro item listed
    change item ∈ [⟨0, Original.cut.raw, returnAt 6⟩] at listed
    rw [List.mem_singleton.mp listed]
    exact valid_payer

/-- The payer's actual delivery restores the six physical units, and the
separate old financial principal stays at its original address. -/
theorem payer_returns_the_six_without_changing_the_original_financial_claim :
    (endAt Original.cut payerScript).raw = Original.snapshot 117 107 := by
  rw [the_payer_returns_six_at_the_original_root.raw_is_the_complete_original_execution 0,
    Original.same_source, Original.cut_raw]
  apply RawCurrent.ext
  · funext bearer good
    cases bearer <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

theorem the_payer_transfer_is_its_literal_original_item :
    Boundary.Actual.items Original.cut payerInput = [⟨0, Original.cut.raw, returnAt 6⟩] :=
  (the_selected_primitive_is_paid_by_the_original_root (queued Original.cut (returnAt 6)) (returnAt 6)
    Original.ready (the_available_review_forwards_the_actual_requested_primitive _ _ Original.review)
    rfl valid_payer).2.2

theorem the_payers_own_signature_adds_no_damage :
    Boundary.Actual.damages Original.cut payerInput Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have literal := damage.source_item
  rw [the_payer_transfer_is_its_literal_original_item] at literal
  have item := List.mem_singleton.mp literal
  have keys := original_key damage
  unfold keysAt at keys
  rw [item] at keys
  change damage.key ∈ ((Physical.Public.interpreter Original.cut.native.input).actualDebit
    Original.cut.raw (returnAt 6)).map (fun entry => (entry.1.1, (returnAt 6).signer, entry.1.2)) at keys
  rw [Original.same_source, Original.cut_raw] at keys
  have actualKeys : ((Physical.Public.interpreter compact).actualDebit (Original.snapshot 111 113)
      (returnAt 6)).map (fun entry => (entry.1.1, (returnAt 6).signer, entry.1.2)) =
        [(true, true, false)] := by decide +kernel
  rw [actualKeys] at keys
  have exactAddress := List.mem_singleton.mp keys
  have foreign := damage.actual_foreign_debit.1.1
  rw [exactAddress] at foreign
  exact foreign rfl

theorem the_payers_own_signature_cannot_credit_the_original_victims_receipt
    (position : Fin (Boundary.Actual.items Original.cut payerInput).length) :
    receiptCredit Original.seed.native.input.law (Boundary.Actual.items Original.cut payerInput)[position]
      Original.occurrence.key = 0 := by
  have literal : (Boundary.Actual.items Original.cut payerInput)[position] ∈
      Boundary.Actual.items Original.cut payerInput := List.getElem_mem _
  have sameItem := List.mem_singleton.mp ((congrArg (fun items =>
    (Boundary.Actual.items Original.cut payerInput)[position] ∈ items)
      the_payer_transfer_is_its_literal_original_item).mp literal)
  rw [sameItem]
  change receiptCredit Original.seed.native.input.law ⟨0, Original.cut.raw, returnAt 6⟩ (false, true, false) = 0
  simp [receiptCredit, returnAt]

theorem after_the_payer_returns_six_the_original_six_is_still_in_the_whole_account
    (answers : ExposureGuard.OwnerAnswers Original.seed) :
    (ExposureGuard.Receipts.writeTick answers Original.state payerInput).stack.balances =
      [(Original.occurrence, Original.balance)] :=
  (a_damage_free_original_write_keeps_every_balance answers Original.state
    the_payers_own_signature_adds_no_damage).trans Original.balances_exact

#print axioms payer_returns_the_six_without_changing_the_original_financial_claim
#print axioms after_the_payer_returns_six_the_original_six_is_still_in_the_whole_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
