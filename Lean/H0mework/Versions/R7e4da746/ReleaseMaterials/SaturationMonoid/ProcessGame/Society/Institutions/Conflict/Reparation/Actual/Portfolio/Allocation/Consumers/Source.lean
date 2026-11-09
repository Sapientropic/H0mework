import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Item
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.Occurrence
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution

set_option autoImplicit false
set_option maxRecDepth 8192

open private executed from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.Occurrence
open private a_paid_suffix_preserves_its_original_head from
  H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (R W front levy compact oldRaw sourceInput sourceRead)
open Reparation.Consumers (warCut address receipt)
open Quantities.Execution (primitiveScript)

noncomputable section

def levyOf (quantity : ℚ) : R :=
  { levy with operation := .transfer false true [(false, quantity)] }

def beforeFirst : W := front
def beforeSecond : W := beforeFirst ++ [levyOf 2]
def beforeReceipt : W := beforeSecond ++ [levyOf 4]
def word : W := beforeReceipt ++ [receipt 3]

abbrev script := primitiveScript word
abbrev tick (request : R) : Input Bool Bool Bool Unit Unit := some (.primitive request)

theorem initialPaid : Conflict.Root.Paid warCut beforeFirst :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem firstPaid : Conflict.Root.Paid warCut beforeSecond :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem secondPaid : Conflict.Root.Paid warCut beforeReceipt :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem paid : Conflict.Root.Paid warCut word :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem original_body_is_single (earlier : W) (request : R)
    (whole : Conflict.Root.Paid warCut (earlier ++ [request])) :
    Boundary.Actual.items (Conflict.Root.terminal warCut earlier) (tick request) =
      [⟨0, (Conflict.Root.terminal warCut earlier).raw, request⟩] := by
  let cut := Conflict.Root.terminal warCut earlier
  have suffix := Conflict.Root.trace_after_prefix warCut _ earlier [request] whole.trace
  obtain ⟨ready, review, consent, valid, _⟩ := a_paid_suffix_preserves_its_original_head suffix
  change Optimality.Programme.Epoch.materialItems (queued cut request) ++ [] = _
  rw [List.append_nil, Optimality.Programme.Epoch.materialItems, if_neg ((queued_is_ready_iff cut request).mpr ready)]
  exact (the_original_root_executes_the_generated_request cut request ready review consent valid).2.1

def bodyPosition (earlier : W) (request : R) (whole : Conflict.Root.Paid warCut (earlier ++ [request])) :
    Position warCut (primitiveScript earlier) (tick request) :=
  ⟨0, by rw [original_body_is_single earlier request whole]; exact Nat.zero_lt_succ _⟩

private theorem item_exact (earlier : W) (request : R)
    (prefixPaid : Conflict.Root.Paid warCut earlier) (whole : Conflict.Root.Paid warCut (earlier ++ [request])) :
    originalItem warCut (primitiveScript earlier) (tick request) (bodyPosition earlier request whole) =
      ⟨0, (compact.law.execute oldRaw 0 earlier).final, request⟩ := by
  have item := List.getElem_of_eq (original_body_is_single earlier request whole) (bodyPosition earlier request whole).isLt
  change originalItem warCut (primitiveScript earlier) (tick request) (bodyPosition earlier request whole) =
    ⟨0, (Conflict.Root.terminal warCut earlier).raw, request⟩ at item
  rw [item, prefixPaid.original_raw_exact, sourceInput, sourceRead]

private def lossAt (earlier : W) (request : R) (whole : Conflict.Root.Paid warCut (earlier ++ [request])) : ℚ :=
  loss (Boundary.Actual.materialLaw (Conflict.Root.terminal warCut earlier)) id
    (originalItem warCut (primitiveScript earlier) (tick request) (bodyPosition earlier request whole)) address

theorem firstLoss : lossAt beforeFirst (levyOf 2) firstPaid = 2 := by
  unfold lossAt
  rw [item_exact beforeFirst (levyOf 2) initialPaid firstPaid]
  change loss (Physical.Public.interpreter (Conflict.Root.terminal warCut beforeFirst).native.input) id _ _ = _
  rw [initialPaid.whole.sameInput, sourceInput]
  decide +kernel

theorem secondLoss : lossAt beforeSecond (levyOf 4) secondPaid = 4 := by
  unfold lossAt
  rw [item_exact beforeSecond (levyOf 4) firstPaid secondPaid]
  change loss (Physical.Public.interpreter (Conflict.Root.terminal warCut beforeSecond).native.input) id _ _ = _
  rw [firstPaid.whole.sameInput, sourceInput]
  decide +kernel

def firstOrigin : Occurrence warCut id :=
  ⟨primitiveScript beforeFirst, tick (levyOf 2), ⟨(bodyPosition beforeFirst (levyOf 2) firstPaid, address),
    by change 0 < lossAt beforeFirst (levyOf 2) firstPaid; rw [firstLoss]; decide⟩⟩

def secondOrigin : Occurrence warCut id :=
  ⟨primitiveScript beforeSecond, tick (levyOf 4), ⟨(bodyPosition beforeSecond (levyOf 4) secondPaid, address),
    by change 0 < lossAt beforeSecond (levyOf 4) secondPaid; rw [secondLoss]; decide⟩⟩

theorem first_original_quantity : firstOrigin.quantity = 2 := firstLoss
theorem second_original_quantity : secondOrigin.quantity = 4 := secondLoss

theorem the_two_attacks_have_distinct_original_visits : firstOrigin.address ≠ secondOrigin.address := by
  intro equal
  have same := congrArg Prod.fst equal
  change (primitiveScript beforeFirst).length = (primitiveScript beforeSecond).length at same
  exact (by decide +kernel : (primitiveScript beforeFirst).length ≠ (primitiveScript beforeSecond).length) same

abbrev receiptPosition := bodyPosition beforeReceipt (receipt 3) paid

theorem the_original_signed_receipt_is_three :
    receiptCredit warCut.native.input.law
      (originalItem warCut (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition) address = 3 := by
  rw [item_exact beforeReceipt (receipt 3) secondPaid paid, sourceInput]
  decide +kernel

def signedReceipt : SignedReceipt warCut address :=
  ⟨primitiveScript beforeReceipt, tick (receipt 3), receiptPosition,
    by rw [show receiptCredit warCut.native.input.law
      (originalItem warCut (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition) address = 3 from
      the_original_signed_receipt_is_three]; decide⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation.Consumers
