import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Physical

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (past : Script Party Good Port Technology Instrument) (input : Input Party Good Port Technology Instrument)
  (position : Position seed past input)

local notation "Row" => Occurrence seed community × Balance

theorem Change.kept_without_the_original_victim_signature
    {origin : Occurrence seed community} {balance : Balance} (move : Change origin balance)
    (actual : move.uses (itemOffer seed past input position))
    (noSignature : (originalItem seed past input position).request.signer ≠ origin.key.1) :
    move = .keep := by
  cases move with
  | keep => rfl
  | pay share within =>
    have chosen : itemOffer seed past input position origin.key = some share.receipt := actual
    have positive : 0 < receiptCredit seed.native.input.law (originalItem seed past input position) origin.key := by
      rw [← item_offer_is_the_actual_signed_credit seed past input position origin.key, Offer.quantity, chosen]
      exact share.receipt.positive
    exact (noSignature (positive_receipt_has_the_original_signature_and_delivery _ _ _ positive).1).elim

theorem Changes.kept_without_the_original_victim_signatures
    {rows : List Row} (moves : Changes rows) (actual : moves.uses (itemOffer seed past input position))
    (noSignature : ∀ row ∈ rows, (originalItem seed past input position).request.signer ≠ row.1.key.1) :
    moves = unchanged rows := by
  induction moves with
  | nil => rfl
  | @cons row remaining head tail prior =>
    have actualParts : head.uses (itemOffer seed past input position) ∧
        tail.uses (itemOffer seed past input position) := actual
    have first := head.kept_without_the_original_victim_signature past input position actualParts.1
      (noSignature row List.mem_cons_self)
    have rest := prior actualParts.2 (fun entry member => noSignature entry (List.mem_cons_of_mem _ member))
    rw [first, rest]
    rfl

/-- Debtor-community signatures retain each original liability row, including
an earlier partially paid row, with the keep motion on the whole write. -/
theorem debtor_community_signatures_leave_every_old_row_in_place (rows : List Row)
    (unilateral : ∀ row ∈ rows,
      community (originalItem seed past input position).request.signer = community row.1.key.2.1) :
    (atItem seed past input position rows).changes = Changes.unchanged rows := by
  let planned := atItem seed past input position rows
  apply Changes.kept_without_the_original_victim_signatures past input position planned.changes planned.original
  intro row present signed
  have foreign := row.1.damage.actual_foreign_debit.1.1
  exact foreign ((congrArg community signed).symm.trans (unilateral row present))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
