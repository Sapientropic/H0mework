import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

/-!
# Original-event financial deltas

This is the exact aggregate readout consumed by original-slot accounting.
It does not replace the liability origins or allocate a payment to a debt.
Those consumers must retain the native admission slots and actual receipts.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace RawLaw

def claimDelta (request : Request Party Good Port Technology Instrument)
    (code : Instrument) (debtor creditor : Party) : ℚ :=
  match request.operation with
  | .issue instrument issuer beneficiary quantity =>
      if (code, debtor, creditor) = (instrument, issuer, beneficiary) then quantity else 0
  | .assign instrument issuer sender recipient quantity =>
      -(if (code, debtor, creditor) = (instrument, issuer, sender) then quantity else 0) +
        (if (code, debtor, creditor) = (instrument, issuer, recipient) then quantity else 0)
  | .settle instrument originalDebtor originalCreditor quantity =>
      -(if (code, debtor, creditor) = (instrument, originalDebtor, originalCreditor) then quantity else 0)
  | _ => 0

variable (law : RawLaw Party Good Port Technology Instrument)

def actualClaimDelta (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (code : Instrument) (debtor creditor : Party) : ℚ :=
  if law.Valid current request then claimDelta request code debtor creditor else 0

theorem step_financial_balance (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (code : Instrument) (debtor creditor : Party) :
    (law.step current request).claims code debtor creditor =
      current.claims code debtor creditor + law.actualClaimDelta current request code debtor creditor := by
  by_cases paid : law.Valid current request
  · simp only [step, actualClaimDelta, if_pos paid, paidStep]
    cases kind : request.operation <;> simp only [nextClaims, claimDelta, kind] <;> ring
  · simp [step, actualClaimDelta, paid]

def totalFinancialDelta (items : List (ExecutionItem Party Good Port Technology Instrument))
    (code : Instrument) (debtor creditor : Party) : ℚ :=
  (items.map (fun item => law.actualClaimDelta item.before item.request code debtor creditor)).sum

theorem execute_financial_balance (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (code : Instrument) (debtor creditor : Party) :
    (law.execute current index event).final.claims code debtor creditor =
      current.claims code debtor creditor +
        law.totalFinancialDelta (law.execute current index event).items code debtor creditor := by
  induction event generalizing current index with
  | nil => simp [execute, totalFinancialDelta]
  | cons request tail ih =>
      have first := law.step_financial_balance current request code debtor creditor
      have later := ih (law.step current request) (index + 1)
      simp only [execute, totalFinancialDelta, List.map_cons, List.sum_cons]
      simp only [totalFinancialDelta] at later
      linarith

theorem accepted_delta (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (accepted : law.Valid current request) (code : Instrument) (debtor creditor : Party) :
    law.actualClaimDelta current request code debtor creditor = claimDelta request code debtor creditor := by
  simp only [actualClaimDelta, if_pos accepted]

theorem accepted_inventory_financial_total
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (event : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ (law.execute current index event).items,
      law.Valid item.before item.request)
    (code : Instrument) (debtor creditor : Party) :
    law.totalFinancialDelta (law.execute current index event).items code debtor creditor =
      (event.map (fun request => claimDelta request code debtor creditor)).sum := by
  have same : ((law.execute current index event).items.map
      (fun item => law.actualClaimDelta item.before item.request code debtor creditor)) =
        ((law.execute current index event).items.map
          (fun item => claimDelta item.request code debtor creditor)) := by
    apply List.map_congr_left
    intro item inside
    exact law.accepted_delta item.before item.request (accepted item inside) code debtor creditor
  unfold totalFinancialDelta
  rw [same]
  have requests := law.inventory_requests_exact current index event
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun requests =>
      (requests.map (fun request => claimDelta request code debtor creditor)).sum) requests

theorem accepted_next_financial_balance
    (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ law.rawItems current event, law.Valid item.before item.request)
    (code : Instrument) (debtor creditor : Party) :
    (law.next current event).claims code debtor creditor = current.claims code debtor creditor +
      (event.map (fun request => claimDelta request code debtor creditor)).sum := by
  have balance := law.execute_financial_balance current 0 event code debtor creditor
  rw [law.accepted_inventory_financial_total current 0 event accepted code debtor creditor] at balance
  exact balance

end RawLaw

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
