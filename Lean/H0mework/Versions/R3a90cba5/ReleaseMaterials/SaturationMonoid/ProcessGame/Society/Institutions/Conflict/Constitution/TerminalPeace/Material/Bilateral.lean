import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Receipt
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Dispatch

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (compact)
open Quantities.Execution
open ExposureGuard
open Reparation Reparation.Actual
open Reparation.Consumers (receipt)

noncomputable section

def receiptInput : Input Bool Bool Bool Unit Unit := some (.primitive (receipt 6))

private theorem valid_receipt : Original.cut.native.input.law.Valid Original.cut.raw (receipt 6) := by
  rw [Original.same_source, Original.cut_raw]
  decide +kernel

theorem the_six_receipt_is_an_actual_instruction :
    Boundary.Actual.items Original.cut receiptInput = [⟨0, Original.cut.raw, receipt 6⟩] := by
  exact (the_selected_primitive_is_paid_by_the_original_root (queued Original.cut (receipt 6)) (receipt 6)
    Original.ready (the_available_review_forwards_the_actual_requested_primitive _ _ Original.review)
    rfl (PublicFunction.valid_physical _ _ _ valid_receipt)).2.2

def receiptPosition : Fin (Boundary.Actual.items Original.cut receiptInput).length :=
  ⟨0, by rw [the_six_receipt_is_an_actual_instruction]; decide⟩

private theorem the_original_item_at_the_receipt_position
    (position : Fin (Boundary.Actual.items Original.cut receiptInput).length) :
    (Boundary.Actual.items Original.cut receiptInput)[position] = ⟨0, Original.cut.raw, receipt 6⟩ := by
  have inside : (Boundary.Actual.items Original.cut receiptInput)[position] ∈
      Boundary.Actual.items Original.cut receiptInput := List.getElem_mem _
  exact List.mem_singleton.mp ((congrArg (fun items =>
    (Boundary.Actual.items Original.cut receiptInput)[position] ∈ items)
      the_six_receipt_is_an_actual_instruction).mp inside)

def originalReceiptSix : SignedReceipt Original.seed Original.occurrence.key where
  past := Original.history
  input := receiptInput
  position := receiptPosition
  positive := by
    change 0 < receiptCredit Original.seed.native.input.law
      (Boundary.Actual.items Original.cut receiptInput)[receiptPosition] (false, true, false)
    rw [the_original_item_at_the_receipt_position, Conflict.Consumers.Evolving.sourceInput, Original.cut_raw]
    decide +kernel

theorem the_original_receipt_delivers_exactly_six : originalReceiptSix.quantity = 6 := by
  change receiptCredit Original.seed.native.input.law
    (Boundary.Actual.items Original.cut receiptInput)[receiptPosition] (false, true, false) = 6
  rw [the_original_item_at_the_receipt_position, Conflict.Consumers.Evolving.sourceInput, Original.cut_raw]
  decide +kernel

/-- The payee's signature and the payer's material exposure are both read
at the unique literal position. -/
theorem the_original_six_transfer_requires_exactly_the_two_personal_answers
    (answers : OwnerAnswers Original.seed) :
    Admitted [false, true] answers Original.history receiptInput ↔
      answers Original.history receiptInput receiptPosition false = true ∧
        answers Original.history receiptInput receiptPosition true = true := by
  constructor
  · intro approved
    have who := signer_is_asked Original.cut (Boundary.Actual.items Original.cut receiptInput)[receiptPosition]
    have signer : (Boundary.Actual.items Original.cut receiptInput)[receiptPosition].request.signer = false := by
      rw [the_original_item_at_the_receipt_position]; rfl
    rw [signer] at who
    have charged : 0 < flowAt ((physical Original.cut).actualDebit
        (Boundary.Actual.items Original.cut receiptInput)[receiptPosition].before
        (Boundary.Actual.items Original.cut receiptInput)[receiptPosition].request) true false := by
      rw [the_original_item_at_the_receipt_position]
      change 0 < flowAt ((Physical.Public.interpreter Original.cut.native.input).actualDebit
        Original.cut.raw (receipt 6)) true false
      rw [Original.same_source, Original.cut_raw]
      decide +kernel
    exact ⟨approved.2 receiptPosition (false, .signature) who (by simp),
      approved.2 receiptPosition _
        (a_positive_actual_debit_asks_its_actual_bearer _ _ true false charged) (by simp)⟩
  · rintro ⟨victim, debtor⟩
    constructor
    · intro item inside
      change item ∈ Boundary.Actual.items Original.cut receiptInput at inside
      rw [the_six_receipt_is_an_actual_instruction] at inside
      rw [List.mem_singleton.mp inside]
      exact valid_receipt
    · intro position question _ _
      have only : position = receiptPosition := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < (Boundary.Actual.items Original.cut receiptInput).length at bound
        rw [the_six_receipt_is_an_actual_instruction] at bound
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      subst position
      cases question.1
      · exact victim
      · exact debtor

theorem the_confirmed_six_receipt_opens_the_reverse_six
    (answers : OwnerAnswers Original.seed)
    (victim : answers Original.history receiptInput receiptPosition false = true)
    (debtor : answers Original.history receiptInput receiptPosition true = true) :
    Admitted [false, true] answers Original.history receiptInput ∧
      ∃ damage : Boundary.Actual.DamageAt Original.cut receiptInput Original.community,
        damage.position = receiptPosition ∧ damage.key = (true, false, false) ∧ damage.quantity = 6 := by
  have reverse := every_cross_community_receipt_opens_its_equal_reverse_damage
    (community := Original.community) originalReceiptSix (by decide)
  rw [the_original_receipt_delivers_exactly_six] at reverse
  exact ⟨(the_original_six_transfer_requires_exactly_the_two_personal_answers answers).mpr ⟨victim, debtor⟩, reverse⟩

#print axioms the_confirmed_six_receipt_opens_the_reverse_six

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
