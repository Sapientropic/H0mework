import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Origin
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Protection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts

open Capitalism.Universal.Source.Program
open Reparation Reparation.Actual Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

variable (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)
  (position : Position seed past input)

omit [DecidableEq Community] in
/-- Keep the actual receipt only on its original victim's accepted lane. -/
def personalOffer : Offer seed :=
  fun key =>
    if answers past input position key.1 then itemOffer seed past input position key else none

omit [DecidableEq Community] in
theorem a_selected_receipt_reads_the_original_victim_lane (key : Key Party Good)
    (receipt : SignedReceipt seed key) (selected : personalOffer answers past input position key = some receipt) :
    answers past input position key.1 = true ∧ itemOffer seed past input position key = some receipt := by
  unfold personalOffer at selected
  split at selected
  · rename_i yes
    exact ⟨yes, selected⟩
  · cases selected

omit [DecidableEq Community] in
theorem a_withheld_lane_has_no_receipt (person : Party) (key : Key Party Good) (victim : key.1 = person) :
    personalOffer (withhold answers person) past input position key = none := by
  simp [personalOffer, victim, withholding_uses_the_original_personal_lane]

omit [DecidableEq Community] in
theorem another_signer_cannot_supply_a_receipt (key : Key Party Good)
    (other : (originalItem seed past input position).request.signer ≠ key.1) :
    personalOffer answers past input position key = none := by
  cases got : personalOffer answers past input position key with
  | none => rfl
  | some receipt =>
    have original := (a_selected_receipt_reads_the_original_victim_lane answers past input position key receipt got).2
    have positive : 0 < receiptCredit seed.native.input.law (originalItem seed past input position) key := by
      rw [← item_offer_is_the_actual_signed_credit seed past input position key, Offer.quantity, original]
      exact receipt.positive
    exact (other (positive_receipt_has_the_original_signature_and_delivery _ _ _ positive).1).elim

def atPersonalItem (rows : List Row) : Plan (personalOffer answers past input position) rows :=
  allocate (personalOffer answers past input position) rows

theorem a_personally_signed_offer_has_the_exact_tight_allocation (rows : List Row) (key : Key Party Good)
    (signed : answers past input position key.1 = true) :
    (atPersonalItem answers past input position rows).changes.assignedFor key =
      min (receiptCredit seed.native.input.law (originalItem seed past input position) key)
        (demand (itemOffer seed past input position) key rows) := by
  let offer := personalOffer answers past input position
  have exactOffer : offer key = itemOffer seed past input position key := by
    simp [offer, personalOffer, signed]
  have exactDemand : demand offer key rows = demand (itemOffer seed past input position) key rows := by
    unfold demand
    congr 1
    apply List.map_congr_left
    intro row _
    by_cases same : row.1.key = key
    · have reads : answers past input position row.1.key.1 = true := by rwa [same]
      have exactRow : offer row.1.key = itemOffer seed past input position row.1.key := by
        simp [offer, personalOffer, reads]
      simp only [if_pos same, eligible, exactRow]
    · simp only [if_neg same]
  calc
    _ = min (offer.quantity key) (demand offer key rows) :=
      allocation_attains_the_joint_tight_bound offer (Capacity.full offer) rows key
    _ = _ := by
      rw [exactDemand, ← item_offer_is_the_actual_signed_credit seed past input position key, Offer.quantity, exactOffer]
      rfl

omit [DecidableEq Community] in
theorem if_every_real_receipt_is_accepted_the_offer_is_original
    (accepted : ∀ key (receipt : SignedReceipt seed key), itemOffer seed past input position key = some receipt →
      answers past input position key.1 = true) :
    personalOffer answers past input position = itemOffer seed past input position := by
  funext key
  cases got : itemOffer seed past input position key with
  | none => simp [personalOffer, got]
  | some receipt => simp [personalOffer, got, accepted key receipt got]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Receipts
