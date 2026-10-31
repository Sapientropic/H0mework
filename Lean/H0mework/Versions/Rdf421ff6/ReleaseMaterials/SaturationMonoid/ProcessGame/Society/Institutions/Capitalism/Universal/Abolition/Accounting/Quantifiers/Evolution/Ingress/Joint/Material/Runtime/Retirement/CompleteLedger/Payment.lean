import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.SourceFacts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Movement
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

open private allocateAt allocateLive allocateFrom Allocation.idle Allocation.append from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

def paymentDelta (instrument : Instrument) (debtor holder : Party) (amount : ℚ)
    (observed : Instrument) (bearer creditor : Party) : ℚ :=
  if instrument = observed ∧ debtor = bearer ∧ holder = creditor then -amount else 0

theorem paymentDelta_zero (instrument observed : Instrument) (debtor holder bearer creditor : Party) :
    paymentDelta instrument debtor holder 0 observed bearer creditor = 0 := by
  simp [paymentDelta]

theorem paymentDelta_add (instrument observed : Instrument) (debtor holder bearer creditor : Party) (left right : ℚ) :
    paymentDelta instrument debtor holder (left + right) observed bearer creditor =
      paymentDelta instrument debtor holder left observed bearer creditor +
      paymentDelta instrument debtor holder right observed bearer creditor := by
  unfold paymentDelta
  split_ifs <;> ring

theorem selected_payment_delta (item : ActualItem input depth count) (claim : Claim input depth count)
    (review : Review input depth count claim) (selected : readReview input depth count claim item = some review)
    (instrument observed : Instrument) (debtor holder bearer creditor : Party) (quantity amount : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity) :
    reviewDelta input depth count review amount observed bearer creditor =
      paymentDelta instrument debtor holder amount observed bearer creditor := by
  obtain ⟨sameInstrument,sameDebtor,sameKind,_⟩ := selected_payment_review_keys
    input depth count claim item review selected instrument debtor holder quantity operation
  simp only [reviewDelta,sameInstrument,sameDebtor,sameKind,Financial.holderParty,paymentDelta]
  split_ifs <;> simp_all

theorem allocateAt_payment (item : ActualItem input depth count)
    (instrument observed : Instrument) (debtor holder bearer creditor : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (state : (process input depth count).GeneratedState) (position : Nat)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    ledgerClaims input depth count (allocateAt input depth count item state position available nonnegative).after.current
        observed bearer creditor =
      ledgerClaims input depth count state.current observed bearer creditor +
        paymentDelta instrument debtor holder
          ((allocateAt input depth count item state position available nonnegative).used input depth count)
          observed bearer creditor := by
  unfold allocateAt
  split_ifs
  · split
    · simp only [Allocation.idle,Allocation.used,sub_self,paymentDelta_zero,add_zero]
    · split
      · simp only [Allocation.idle,Allocation.used,sub_self,paymentDelta_zero,add_zero]
      next review selected =>
        rw [allocateLive_ledgerClaims,selected_payment_delta input depth count item _ review selected
          instrument observed debtor holder bearer creditor quantity _ operation]
  · simp only [Allocation.idle,Allocation.used,sub_self,paymentDelta_zero,add_zero]

theorem allocateFrom_payment (item : ActualItem input depth count)
    (instrument observed : Instrument) (debtor holder bearer creditor : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (fuel position : Nat) (state : (process input depth count).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    ledgerClaims input depth count
        (allocateFrom input depth count item position fuel state available nonnegative).after.current observed bearer creditor =
      ledgerClaims input depth count state.current observed bearer creditor +
        paymentDelta instrument debtor holder
          ((allocateFrom input depth count item position fuel state available nonnegative).used input depth count)
          observed bearer creditor := by
  induction fuel generalizing position state available with
  | zero => simp only [allocateFrom,Allocation.idle,Allocation.used,sub_self,paymentDelta_zero,add_zero]
  | succ fuel ih =>
      let first := allocateAt input depth count item state position available nonnegative
      let rest := allocateFrom input depth count item (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative
      change ledgerClaims input depth count rest.after.current observed bearer creditor =
        ledgerClaims input depth count state.current observed bearer creditor +
          paymentDelta instrument debtor holder ((Allocation.append input depth count first rest).used input depth count)
            observed bearer creditor
      rw [allocation_used_append,paymentDelta_add]
      have later := ih (position + 1) first.after first.remaining first.remaining_nonnegative
      have earlier := allocateAt_payment input depth count item instrument observed debtor holder bearer creditor quantity
        operation state position available nonnegative
      change ledgerClaims input depth count rest.after.current observed bearer creditor = _ at later
      change ledgerClaims input depth count first.after.current observed bearer creditor = _ at earlier
      linarith

theorem one_actual_payment_clears_exactly_its_original_aggregate_share
    (item : ActualItem input depth count) (instrument observed : Instrument) (debtor holder bearer creditor : Party)
    (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (state : (process input depth count).GeneratedState)
    (funded : quantity ≤ ledgerClaims input depth count state.current instrument debtor holder) :
    ∃ movement : Movement input depth count item,
      readMovement input depth count item = some movement ∧ movement.quantity = quantity ∧
      (allocate input depth count item movement state).remaining = 0 ∧
      ledgerClaims input depth count (allocate input depth count item movement state).after.current observed bearer creditor =
        ledgerClaims input depth count state.current observed bearer creditor +
          paymentDelta instrument debtor holder quantity observed bearer creditor := by
  obtain ⟨movement,parsed,_,amount⟩ := an_actual_payment_generates_its_original_movement
    input depth count item instrument debtor holder quantity operation accepted
  have empty : (allocate input depth count item movement state).remaining = 0 := by
    rw [allocate_remaining input depth count item movement
      (by rw [amount]; exact payment_source_quantity input depth count item instrument debtor holder quantity operation),
      payment_full_capacity input depth count item instrument debtor holder quantity operation accepted state.current,amount]
    exact max_eq_right (sub_nonpos.mpr funded)
  have used : (allocate input depth count item movement state).used input depth count = quantity := by
    rw [Allocation.used,empty,sub_zero,amount]
  refine ⟨movement,parsed,amount,empty,?_⟩
  have effect := allocateFrom_payment input depth count item instrument observed debtor holder bearer creditor quantity
    operation state.current.slots.length 0 state movement.quantity (movement.quantity_nonnegative input depth count)
  change ledgerClaims input depth count (allocate input depth count item movement state).after.current observed bearer creditor =
    ledgerClaims input depth count state.current observed bearer creditor +
      paymentDelta instrument debtor holder ((allocate input depth count item movement state).used input depth count)
        observed bearer creditor at effect
  rw [used] at effect
  exact effect

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
