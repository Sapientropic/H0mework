import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements.Passive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements

open Source.Program PublicFunction.Financing

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Candidate terms are decoded from the original issued operation, not from
an appraisal or an externally supplied return amount. -/
def termsOf (item : ExecutionItem Party Good Port Technology Instrument) : Option (Terms Party Instrument) :=
  match item.request.operation with
  | .issue instrument borrower lender principal => some ⟨borrower,lender,instrument,principal⟩
  | _ => none

def fundedSource (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Option (Σ terms : Terms Party Instrument,Disbursement law before word terms) :=
  (law.rawItems before word).findSome? fun item =>
    (termsOf item).bind fun terms =>
      (readDisbursement? law before word terms).map fun receipt => ⟨terms,receipt⟩

theorem every_decoded_financing_claim_has_its_real_bearers_material_and_finite_source_amount
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (source : Σ terms : Terms Party Instrument,Disbursement law before word terms) :
    let terms := source.1
    let receipt := source.2
    0 < terms.principal ∧
      law.actualClaimDelta receipt.issue.before receipt.issue.request terms.instrument terms.borrower terms.lender = terms.principal ∧
      (law.step receipt.payout.before receipt.payout.request).stock terms.borrower (law.settlementUnit terms.instrument) =
        receipt.payout.before.stock terms.borrower (law.settlementUnit terms.instrument) +
          terms.principal * law.settlementRate terms.instrument ∧
      (law.step receipt.payout.before receipt.payout.request).stock terms.lender (law.settlementUnit terms.instrument) =
        receipt.payout.before.stock terms.lender (law.settlementUnit terms.instrument) -
          terms.principal * law.settlementRate terms.instrument ∧
      receipt.payout.request.signer = terms.lender ∧
      (law.step receipt.payout.before receipt.payout.request).claims = receipt.payout.before.claims ∧
      (law.step receipt.payout.before receipt.payout.request).technology = receipt.payout.before.technology := by
  refine ⟨source.2.principal_positive,source.2.actual_principal_created,source.2.borrower_received_material,
    source.2.lender_paid_material,source.2.lender_signed,?_,?_⟩
  all_goals
    simp only [RawLaw.step,if_pos source.2.payout_accepted,RawLaw.paidStep,RawLaw.nextClaims,source.2.payout_kind]

theorem possession_and_appraisal_cannot_pass_the_real_funding_producer
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (passive : Passive word) :
    fundedSource law before word = none := by
  have absent : ∀ item ∈ law.rawItems before word,
      (termsOf item).bind (fun terms =>
        (readDisbursement? law before word terms).map fun receipt => ⟨terms,receipt⟩) =
      (none : Option (Σ terms : Terms Party Instrument,Disbursement law before word terms)) := by
    intro item member
    have actual := passive_execution_items_are_still_presentations law before word passive item member
    simp only [termsOf,actual,Option.bind_none]
  unfold fundedSource
  generalize law.rawItems before word = items at absent ⊢
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rw [List.findSome?_cons,absent item List.mem_cons_self]
      exact ih (fun next member => absent next (List.mem_cons_of_mem item member))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements
