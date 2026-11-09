import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Writer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Source.Program
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument}

variable (answers : ReceiptAnswers seed) (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)
  (position : Position seed past input)

theorem a_joint_receipt_has_its_actual_distinct_original_parties
    (key : Key Party Good) (receipt : JointReceipt seed key)
    (offered : jointOffer answers past input position key = some receipt) :
    key.1 ≠ key.2.1 ∧ (originalItem seed past input position).request.signer = key.2.1 ∧
      answers past input position key.2.1 = true ∧ answers past input position key.1 = true := by
  obtain ⟨payer, victim, positive, _⟩ :=
    the_joint_offer_is_issued_at_the_exact_position answers past input position key receipt offered
  have actual := positive_payer_credit_has_the_original_payer_and_delivery _ _ key positive
  exact ⟨actual.1, actual.2.1, payer, victim⟩

theorem a_proxy_cannot_supply_the_debtors_signed_delivery (key : Key Party Good)
    (proxy : (originalItem seed past input position).request.signer ≠ key.2.1) :
    jointOffer answers past input position key = none := by
  cases issued : jointOffer answers past input position key with
  | none => rfl
  | some receipt =>
    exact (proxy (a_joint_receipt_has_its_actual_distinct_original_parties
      answers past input position key receipt issued).2.1).elim

theorem two_joint_offers_of_one_original_good_must_share_one_claim_key
    (left right : Key Party Good) (first : JointReceipt seed left) (second : JointReceipt seed right)
    (offerLeft : jointOffer answers past input position left = some first)
    (offerRight : jointOffer answers past input position right = some second)
    (sameGood : left.2.2 = right.2.2) : left = right := by
  obtain ⟨_, _, leftPositive, _⟩ :=
    the_joint_offer_is_issued_at_the_exact_position answers past input position left first offerLeft
  obtain ⟨_, _, rightPositive, _⟩ :=
    the_joint_offer_is_issued_at_the_exact_position answers past input position right second offerRight
  obtain ⟨_, _, _, leftBundle, leftForm, _⟩ :=
    positive_payer_credit_has_the_original_payer_and_delivery _ _ left leftPositive
  obtain ⟨_, _, _, rightBundle, rightForm, _⟩ :=
    positive_payer_credit_has_the_original_payer_and_delivery _ _ right rightPositive
  have same := leftForm.symm.trans rightForm
  injection same with payer recipient
  exact Prod.ext recipient (Prod.ext payer sameGood)

theorem the_same_joint_receipt_cannot_be_reused_at_a_later_tick
    (key : Key Party Good) (receipt : JointReceipt seed key)
    (first : jointOffer answers past input position key = some receipt)
    (later : Reparation.Actual.Script Party Good Port Technology Instrument)
    (laterInput : Reparation.Actual.Input Party Good Port Technology Instrument)
    (laterPosition : Position seed later laterInput) (laterAnswers : ReceiptAnswers seed)
    (strict : past.length < later.length) :
    jointOffer laterAnswers later laterInput laterPosition key ≠ some receipt := by
  intro again
  have before := (a_joint_offer_requires_both_original_replies answers past input position key receipt first).2.2
  have after := (a_joint_offer_requires_both_original_replies laterAnswers later laterInput
    laterPosition key receipt again).2.2
  exact (ne_of_lt strict) (congrArg Prod.fst (before.symm.trans after))

#print axioms a_proxy_cannot_supply_the_debtors_signed_delivery
#print axioms the_same_joint_receipt_cannot_be_reused_at_a_later_tick

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
