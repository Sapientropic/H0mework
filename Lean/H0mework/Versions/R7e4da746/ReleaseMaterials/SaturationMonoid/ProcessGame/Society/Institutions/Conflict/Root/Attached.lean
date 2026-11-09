import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Incidence
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Menus

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

variable {source : Cut Party Good Port Technology Instrument}
  {front : RawEvent Party Good Port Technology Instrument}
  {levy settlement : Request Party Good Port Technology Instrument} {index : Nat}

namespace Shift

abbrev originalWord (_shift : Shift source front levy settlement index) : Word :=
  front ++ [levy, settlement]

abbrev unit (shift : Shift source front levy settlement index) : Good :=
  source.native.input.law.settlementUnit shift.funding.position.instrument

def returnRequest (shift : Shift source front levy settlement index) (rate : ℚ) : Req :=
  let payer := shift.funding.position.debtor
  let cut := terminal source shift.originalWord
  ⟨payer, [], source.native.input.law.stockPort cut.raw.technology payer shift.unit, [],
    .transfer payer shift.funding.bearer [(shift.unit, rate * shift.funding.quantity)]⟩

def returnedWord (shift : Shift source front levy settlement index) (rate : ℚ) : Word :=
  if rate = 0 then shift.originalWord else shift.originalWord ++ [shift.returnRequest rate]

def atRate (shift : Shift source front levy settlement index) (rate : ℚ) :
    Decision source (shift.returnedWord rate) :=
  inspect source (shift.returnedWord rate)

/-- In the original settlement good the two addresses move by exactly the
executed return. The paid destruction and the native debt disposition stay. -/
theorem actual_return_is_charged_to_the_original_debtor
    (shift : Shift source front levy settlement index) (rate : ℚ)
    (paid : Paid source (shift.returnedWord rate)) :
    let old := terminal source shift.originalWord
    let new := terminal source (shift.returnedWord rate)
    let debtor := shift.funding.position.debtor
    let bearer := shift.funding.bearer
    let restored := rate * shift.funding.quantity
    new.raw.stock debtor shift.unit = old.raw.stock debtor shift.unit - restored ∧
      new.raw.stock bearer shift.unit = old.raw.stock bearer shift.unit + restored ∧
      new.raw.claims = old.raw.claims ∧ HEq (nativeAccount new) (nativeAccount old) := by
  dsimp only
  by_cases zero : rate = 0
  · subst rate
    simp [returnedWord]
  have sameWord : shift.returnedWord rate = shift.originalWord ++ [shift.returnRequest rate] := by
    simp only [returnedWord, if_neg zero]
  rw [sameWord] at paid
  have sameCut := congrArg (terminal source) sameWord
  obtain ⟨physical, claims, ledger⟩ := a_paid_return_has_its_exact_original_effect paid
    shift.funding.position.debtor shift.funding.bearer shift.unit (rate * shift.funding.quantity) rfl
  have separate := shift.funding.exposed
  refine ⟨?_, ?_, ?_, (nativeAccount_heq_of_eq sameCut).trans ledger⟩
  · rw [sameCut]
    simpa [separate] using physical shift.funding.position.debtor shift.unit
  · rw [sameCut]
    simpa [Ne.symm separate] using physical shift.funding.bearer shift.unit
  · rw [sameCut]
    exact claims

def debtorStock (shift : Shift source front levy settlement index) (cut : C) : ℚ :=
  cut.raw.stock shift.funding.position.debtor shift.unit

theorem exact_change_of_paid_gap (shift : Shift source front levy settlement index)
    (peace : Admitted source) (rate : ℚ) (paid : Paid source (shift.returnedWord rate)) :
    shift.debtorStock (terminal source (shift.returnedWord rate)) - shift.debtorStock (terminal source peace.val) =
      (shift.debtorStock (terminal source shift.originalWord) - shift.debtorStock (terminal source peace.val)) -
        rate * shift.funding.quantity := by
  unfold debtorStock
  rw [(shift.actual_return_is_charged_to_the_original_debtor rate paid).1]
  ring

/-- Exact causal flip on a fixed paid comparison, in the native unit.
The optimized comparison separately checks both regimes' entire menus. -/
theorem full_return_strictly_flips_iff
    (shift : Shift source front levy settlement index) (peace : Admitted source)
    (paid : Paid source (shift.returnedWord 1)) :
    let old := shift.debtorStock (terminal source shift.originalWord) -
      shift.debtorStock (terminal source peace.val)
    let restored := shift.debtorStock (terminal source (shift.returnedWord 1)) -
      shift.debtorStock (terminal source peace.val)
    (0 < old ∧ restored < 0) ↔ (0 < old ∧ old < shift.funding.quantity) := by
  dsimp only
  rw [shift.exact_change_of_paid_gap peace 1 paid, one_mul]
  exact and_congr_right (fun _ => sub_neg)

end Shift

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
