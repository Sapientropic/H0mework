import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Item

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance
local notation "History" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem positive_credit_has_the_same_payer_and_payee
    (law : RawLaw Party Good Port Technology Instrument) (item : Item) (key : Key Party Good)
    (positive : 0 < receiptCredit law item key) (payer payee : Party) (goods : Bundle Good)
    (transfer : item.request.operation = .transfer payer payee goods) :
    key = (payee, payer, key.2.2) := by
  obtain ⟨_, _, _, original, _⟩ := positive_receipt_has_the_original_signature_and_delivery law item key positive
  have same := original.symm.trans transfer
  injection same with payerEq payeeEq
  exact Prod.ext payeeEq (Prod.ext payerEq rfl)

def unitQuantity (past : History) (input : Proposal) (position : Position seed past input) (good : Good) : ℚ :=
  let item := originalItem seed past input position
  match item.request.operation with
  | .transfer payer payee _ => receiptCredit seed.native.input.law item (payee, payer, good)
  | _ => 0

variable (past : List (Input Party Good Port Technology Instrument))
  (input : Input Party Good Port Technology Instrument) (position : Position seed past input)

private theorem positive_of_original_share {key : Key Party Good} (receipt : SignedReceipt seed key)
    (selected : itemOffer seed past input position key = some receipt) :
    0 < receiptCredit seed.native.input.law (originalItem seed past input position) key := by
  rw [← item_offer_is_the_actual_signed_credit seed past input position key, Offer.quantity, selected]
  exact receipt.positive

theorem one_material_good_has_one_transfer_address
    {rows : List Row} (moves : Changes rows) (uses : moves.uses (itemOffer seed past input position))
    (payer payee : Party) (goods : Bundle Good)
    (transfer : (originalItem seed past input position).request.operation = .transfer payer payee goods)
    (good : Good) :
    moves.assignedForGood good = moves.assignedFor (payee, payer, good) := by
  induction moves with
  | nil => rfl
  | @cons row rows head tail prior =>
    have shares : head.uses (itemOffer seed past input position) ∧ tail.uses (itemOffer seed past input position) := uses
    have remaining := prior shares.2
    cases head with
    | keep =>
      simp only [Changes.assignedWhere, Change.amount, ite_self, zero_add]
      exact remaining
    | pay share within =>
      have positive := positive_of_original_share past input position share.receipt shares.1
      have address := positive_credit_has_the_same_payer_and_payee seed.native.input.law
        (originalItem seed past input position) row.1.key positive payer payee goods transfer
      have equivalent : row.1.key.2.2 = good ↔ row.1.key = (payee, payer, good) :=
        ⟨fun exactGood => address.trans (congrArg (fun lot => (payee, payer, lot)) exactGood),
          fun same => congrArg (fun key : Key Party Good => key.2.2) same⟩
      simp only [Changes.assignedWhere, equivalent, remaining]

private theorem a_nontransfer_carries_no_credit
    (notTransfer : ¬ ∃ payer payee goods,
      (originalItem seed past input position).request.operation = .transfer payer payee goods)
    (good : Good) {rows : List Row} (moves : Changes rows)
    (uses : moves.uses (itemOffer seed past input position)) :
    moves.assignedForGood good = 0 := by
  induction moves with
  | nil => rfl
  | @cons row rows head tail prior =>
    have shares : head.uses (itemOffer seed past input position) ∧ tail.uses (itemOffer seed past input position) := uses
    cases head with
    | keep => simpa only [Changes.assignedWhere, Change.amount, ite_self, zero_add] using prior shares.2
    | pay share within =>
      have positive := positive_of_original_share past input position share.receipt shares.1
      obtain ⟨_, _, goods, transfer, _⟩ := positive_receipt_has_the_original_signature_and_delivery
        seed.native.input.law (originalItem seed past input position) row.1.key positive
      exact (notTransfer ⟨row.1.key.2.1, row.1.key.1, goods, transfer⟩).elim

/-- Summation ranges over every old liability row and every address for this
good. The actual transfer supplies its one signed physical cap. -/
theorem one_material_good_cannot_be_spent_twice (rows : List Row) (good : Good) :
    (atItem seed past input position rows).changes.assignedForGood good ≤ unitQuantity past input position good := by
  let plan := atItem seed past input position rows
  by_cases transfer : ∃ payer payee goods,
      (originalItem seed past input position).request.operation = .transfer payer payee goods
  · obtain ⟨payer, payee, goods, original⟩ := transfer
    have assigned := one_material_good_has_one_transfer_address past input position plan.changes plan.original
      payer payee goods original good
    change plan.changes.assignedForGood good ≤ _
    rw [assigned, unitQuantity, original]
    have bound := allocated_is_within_the_original_quantity (itemOffer seed past input position) rows
      (payee, payer, good)
    exact bound.trans_eq (item_offer_is_the_actual_signed_credit seed past input position _)
  · have zero := a_nontransfer_carries_no_credit past input position transfer good plan.changes plan.original
    change plan.changes.assignedForGood good ≤ _
    rw [zero]
    dsimp only [unitQuantity]
    split
    · rename_i payer payee goods original
      exact (transfer ⟨payer, payee, goods, original⟩).elim
    · exact le_rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
