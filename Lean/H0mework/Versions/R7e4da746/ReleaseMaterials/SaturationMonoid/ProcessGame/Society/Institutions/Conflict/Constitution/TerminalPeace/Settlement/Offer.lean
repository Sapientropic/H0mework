import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.CoSigned
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Item

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument}

local notation "Address" => Key Party Good

variable (answers : ReceiptAnswers seed) (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)
  (position : Position seed past input)

/-- Both personal replies and the actual payer-signed material quantity
are checked at the one original item, independently of its stated purpose. -/
def jointOffer (key : Address) : Option (JointReceipt seed key) :=
  if actual : answers past input position key.2.1 = true ∧
      answers past input position key.1 = true ∧
      0 < payerCredit seed.native.input.law (originalItem seed past input position) key then
    some ⟨past, input, position, answers, actual.1, actual.2.1, actual.2.2⟩
  else none

theorem the_joint_offer_is_issued_at_the_exact_position (key : Address) (receipt : JointReceipt seed key)
    (selected : jointOffer answers past input position key = some receipt) :
    ∃ (payer : answers past input position key.2.1 = true)
      (victim : answers past input position key.1 = true)
      (positive : 0 < payerCredit seed.native.input.law (originalItem seed past input position) key),
      receipt = ⟨past, input, position, answers, payer, victim, positive⟩ := by
  unfold jointOffer at selected
  split at selected
  · rename_i actual
    exact ⟨actual.1, actual.2.1, actual.2.2, (Option.some.inj selected).symm⟩
  · cases selected

theorem a_joint_offer_requires_both_original_replies (key : Address) (receipt : JointReceipt seed key)
    (selected : jointOffer answers past input position key = some receipt) :
    answers past input position key.2.1 = true ∧ answers past input position key.1 = true ∧
      receipt.address = (past.length, position.val) := by
  obtain ⟨payer, victim, _, rfl⟩ :=
    the_joint_offer_is_issued_at_the_exact_position answers past input position key receipt selected
  exact ⟨payer, victim, rfl⟩

theorem the_original_victims_refusal_prevents_a_receipt (key : Address)
    (refused : answers past input position key.1 = false) :
    jointOffer answers past input position key = none := by
  simp [jointOffer, refused]

theorem the_original_payers_refusal_prevents_a_receipt (key : Address)
    (refused : answers past input position key.2.1 = false) :
    jointOffer answers past input position key = none := by
  simp [jointOffer, refused]

/-- One physical delivery supplies the budget for its original good.
An unaccepted delivery may have stock and still offer no payable receipt. -/
def limitAt (good : Good) : ℚ :=
  let item := originalItem seed past input position
  match item.request.operation with
  | .transfer _ payee _ =>
    max 0 (flowAt (seed.native.input.law.actualCredit item.before item.request) payee good)
  | _ => 0

theorem limitAt_nonnegative (good : Good) : 0 ≤ limitAt past input position good := by
  unfold limitAt
  dsimp only
  split
  · exact le_max_left _ _
  all_goals exact le_rfl

theorem the_original_limit_is_the_selected_quantity (key : Address) (receipt : JointReceipt seed key)
    (selected : jointOffer answers past input position key = some receipt) :
    limitAt past input position key.2.2 = receipt.quantity := by
  obtain ⟨payer, victim, positive, rfl⟩ :=
    the_joint_offer_is_issued_at_the_exact_position answers past input position key receipt selected
  obtain ⟨_, _, _, goods, form, exactFlow⟩ :=
    positive_payer_credit_has_the_original_payer_and_delivery _ _ key positive
  unfold limitAt
  dsimp only
  rw [form]
  change max 0 (flowAt (seed.native.input.law.actualCredit
    (originalItem seed past input position).before (originalItem seed past input position).request)
    key.1 key.2.2) = _
  rw [exactFlow, max_eq_right positive.le]

theorem a_receipt_cannot_move_to_a_different_position (key : Address) (receipt : JointReceipt seed key)
    (selected : jointOffer answers past input position key = some receipt)
    (other : Position seed past input) (distinct : other ≠ position) :
    jointOffer answers past input other key ≠ some receipt := by
  intro same
  have first := (a_joint_offer_requires_both_original_replies answers past input position key receipt selected).2.2
  have second := (a_joint_offer_requires_both_original_replies answers past input other key receipt same).2.2
  exact distinct (Fin.ext (congrArg Prod.snd (second.symm.trans first)))

#print axioms the_joint_offer_is_issued_at_the_exact_position
#print axioms a_receipt_cannot_move_to_a_different_position

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
