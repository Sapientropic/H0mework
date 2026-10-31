import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Receipt
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem selected_review_origin (claim : Claim input depth count) (item : ActualItem input depth count)
    (review : Review input depth count claim) (selected : readReview input depth count claim item = some review) :
    review.origin = item := by
  unfold readReview at selected
  repeat' first
    | contradiction
    | split at selected
    | (cases Option.some.inj selected; rfl)

theorem selected_payment_review_keys (claim : Claim input depth count) (item : ActualItem input depth count)
    (review : Review input depth count claim) (selected : readReview input depth count claim item = some review)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity) :
    claim.instrument input depth count = instrument ∧ claim.debtor input depth count = debtor ∧
      review.kind = .payment holder ∧ review.quantity = quantity := by
  have original := review.operation
  rw [selected_review_origin input depth count claim item review selected,operation] at original
  cases kind : review.kind with
  | payment actor =>
      simp only [reviewOperation,kind] at original
      cases original
      exact ⟨rfl,rfl,rfl,rfl⟩
  | assignment sender receiver =>
      simp only [reviewOperation,kind] at original
      cases original

theorem payment_source_quantity (item : ActualItem input depth count)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity) :
    ReviewQuantityAt input depth count item quantity := by
  intro claim review selected
  exact (selected_payment_review_keys input depth count claim item review selected instrument debtor holder quantity operation).2.2.2

theorem payment_capacity (item : ActualItem input depth count)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (slot : ObligationSlot (vocabulary input depth count)) :
    reviewCapacity input depth count item slot = slotClaims input depth count slot instrument debtor holder := by
  cases slot with
  | terminal archive => simp [reviewCapacity]
  | live obligation =>
      cases selected : readReview input depth count obligation.content item with
      | none =>
          by_cases sameInstrument : obligation.content.instrument input depth count = instrument
          · by_cases sameDebtor : obligation.content.debtor input depth count = debtor
            · obtain ⟨review,found,_,_,_⟩ := an_actual_matching_payment_generates_its_original_review
                input depth count obligation.content item holder quantity
                (by rw [sameInstrument,sameDebtor]; exact operation) accepted
              rw [selected] at found
              contradiction
            · simp [reviewCapacity,selected,slotClaims,slotClaim,slotObligation,sameDebtor]
          · simp [reviewCapacity,selected,slotClaims,slotClaim,slotObligation,sameInstrument]
      | some review =>
          obtain ⟨sameInstrument,sameDebtor,sameKind,_⟩ :=
            selected_payment_review_keys input depth count obligation.content item review selected
              instrument debtor holder quantity operation
          simp only [reviewCapacity,selected,slotClaims,slotClaim,slotObligation,slotBalance,
            sameInstrument,sameDebtor,and_self,↓reduceIte,Review.fromHolder,sameKind]

theorem payment_full_capacity (item : ActualItem input depth count)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (state : ResponsibilityState (vocabulary input depth count)) :
    suffixCapacity input depth count item state 0 = ledgerClaims input depth count state instrument debtor holder := by
  simp only [suffixCapacity,List.drop_zero,ledgerClaims]
  congr 1
  apply List.map_congr_left
  intro slot _
  exact payment_capacity input depth count item instrument debtor holder quantity operation accepted slot

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
