import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic

open Source.Program Abolition.Completion.Actual.Dividend

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]
  (law : RawLaw Party Good Port Technology Instrument)

def claimLeg (instrument : Instrument) (holder : Party) (quantity : ℚ) (person : Party) (good : Good) : ℚ :=
  if (holder, law.settlementUnit instrument) = (person, good) then quantity * law.settlementRate instrument else 0

def rawClaimIncome (request : Request Party Good Port Technology Instrument) (person : Party) (good : Good) : ℚ :=
  match request.operation with
  | .issue instrument debtor creditor quantity =>
      claimLeg law instrument creditor quantity person good - claimLeg law instrument debtor quantity person good
  | .assign instrument _debtor sender recipient quantity =>
      claimLeg law instrument recipient quantity person good - claimLeg law instrument sender quantity person good
  | .settle instrument debtor creditor quantity =>
      claimLeg law instrument debtor quantity person good - claimLeg law instrument creditor quantity person good
  | _ => 0

def completeItemIncome (item : ExecutionItem Party Good Port Technology Instrument) (person : Party) (good : Good) : ℚ :=
  flowAt (law.actualCredit item.before item.request) person good -
    flowAt (law.actualDebit item.before item.request) person good +
    if law.Valid item.before item.request then rawClaimIncome law item.request person good else 0

def completeIncome (items : List (ExecutionItem Party Good Port Technology Instrument)) (person : Party) (good : Good) : ℚ :=
  (items.map fun item => completeItemIncome law item person good).sum

theorem raw_claim_income_is_the_complete_original_financial_position
    (request : Request Party Good Port Technology Instrument) (person : Party) (good : Good) :
    rawClaimIncome law request person good = Financial.value law (Financial.rawClaimChange request) (person, good) := by
  cases operation : request.operation <;>
    simp only [rawClaimIncome, Financial.rawClaimChange, operation, map_add, map_neg, map_zero,
      Financial.value_single, Finsupp.add_apply, Finsupp.neg_apply, Finsupp.sub_apply,
      Finsupp.zero_apply, Finsupp.single_apply, claimLeg] <;> ring

theorem complete_item_income_is_the_original_full_change
    (item : ExecutionItem Party Good Port Technology Instrument) (person : Party) (good : Good) :
    completeItemIncome law item person good = Financial.fullChange law item.before item.request (person, good) := by
  rw [Financial.fullChange, Finsupp.add_apply,
    Financial.material_change_is_the_original_net_flow]
  unfold completeItemIncome Financial.claimChange
  by_cases accepted : law.Valid item.before item.request
  · simp only [if_pos accepted, raw_claim_income_is_the_complete_original_financial_position]
  · simp only [if_neg accepted, map_zero, Finsupp.zero_apply]

theorem complete_income_is_the_original_full_account
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (person : Party) (good : Good) :
    completeIncome law items person good = Accounting.Profit.fullIncome law items (person, good) := by
  induction items with
  | nil => simp [completeIncome, Accounting.Profit.fullIncome, Financial.inventoryMaterial, Financial.inventoryClaims]
  | cons item later inherited =>
      simp only [completeIncome, List.map_cons, List.sum_cons] at inherited ⊢
      rw [complete_item_income_is_the_original_full_change, inherited]
      simp only [Accounting.Profit.fullIncome, Financial.fullChange, Financial.inventoryMaterial,
        Financial.inventoryClaims, List.map_cons, List.sum_cons, map_add, Finsupp.add_apply]
      ring

theorem completeIncome_append
    (first second : List (ExecutionItem Party Good Port Technology Instrument)) (person : Party) (good : Good) :
    completeIncome law (first ++ second) person good =
      completeIncome law first person good + completeIncome law second person good := by
  simp only [completeIncome, List.map_append, List.sum_append]

theorem complete_income_of_claims_neutral_word [DecidableEq Instrument]
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (neutral : (law.next before word).claims = before.claims) (person : Party) (good : Good) :
    completeIncome law (law.rawItems before word) person good =
      (law.next before word).stock person good - before.stock person good := by
  have zero : Financial.inventoryClaims law (law.rawItems before word) = 0 := by
    ext ⟨instrument, debtor, creditor⟩
    rw [Financial.inventory_claims_are_the_original_financial_delta]
    have actual := law.execute_financial_balance before 0 word instrument debtor creditor
    change (law.next before word).claims instrument debtor creditor = _ at actual
    rw [neutral] at actual
    simp only [Finsupp.zero_apply]
    change law.totalFinancialDelta (law.execute before 0 word).items instrument debtor creditor = 0
    linarith
  rw [complete_income_is_the_original_full_account, Accounting.Profit.fullIncome,
    zero, map_zero, add_zero, Financial.inventory_material_is_the_original_net_flow]
  have actual := law.actual_next_material_balance before word person good
  linarith

theorem completeIncome_rawItems_index_invariant [DecidableEq Instrument]
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (first second : Nat) (person : Party) (good : Good) :
    completeIncome law (law.execute before first word).items person good =
      completeIncome law (law.execute before second word).items person good := by
  induction word generalizing before first second with
  | nil => rfl
  | cons request tail inherited =>
      simpa only [RawLaw.execute, completeIncome, List.map_cons, List.sum_cons, completeItemIncome] using
        congrArg (fun value => completeItemIncome law ⟨first, before, request⟩ person good + value)
          (inherited (law.step before request) (first + 1) (second + 1))

theorem completeIncome_word_append [DecidableEq Instrument]
    (before : RawCurrent Party Good Technology Instrument)
    (first second : RawEvent Party Good Port Technology Instrument) (person : Party) (good : Good) :
    completeIncome law (law.rawItems before (first ++ second)) person good =
      completeIncome law (law.rawItems before first) person good +
        completeIncome law (law.rawItems (law.execute before 0 first).final second) person good := by
  unfold RawLaw.rawItems
  rw [law.execute_append, completeIncome_append]
  rw [completeIncome_rawItems_index_invariant law _ second (0 + first.length) 0]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic
