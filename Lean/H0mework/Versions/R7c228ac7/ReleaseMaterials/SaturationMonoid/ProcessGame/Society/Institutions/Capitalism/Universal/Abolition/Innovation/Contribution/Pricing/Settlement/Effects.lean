import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument)
  (payer provider : Party) (instrument : Instrument) (purpose : Port) (net : ℚ)

variable (issued : law.Valid before (issue law payer provider instrument purpose net))
  (settled : law.Valid (afterIssue law payer provider instrument purpose net before)
    (settle law payer provider instrument purpose net))

include issued in
theorem the_first_actual_issue_keeps_material_and_adds_its_exact_claim :
    (afterIssue law payer provider instrument purpose net before).stock = before.stock ∧
      ∀ code oldDebtor oldCreditor,
        (afterIssue law payer provider instrument purpose net before).claims code oldDebtor oldCreditor =
          before.claims code oldDebtor oldCreditor +
            if (code,oldDebtor,oldCreditor) =
              (instrument,debtor payer provider net,creditor payer provider net)
            then units law instrument net else 0 := by
  constructor
  · exact law.issuance_creates_no_material before _ instrument _ _ _ rfl
  · intro code oldDebtor oldCreditor
    unfold afterIssue
    rw [RawLaw.step, if_pos issued]
    rfl

include issued settled in
theorem actual_payment_retains_the_entire_original_claim_matrix :
    (afterPayment law payer provider instrument purpose net before).claims = before.claims := by
  funext code oldDebtor oldCreditor
  unfold afterPayment
  rw [RawLaw.step, if_pos settled]
  change (afterIssue law payer provider instrument purpose net before).claims code oldDebtor oldCreditor -
    (if (code,oldDebtor,oldCreditor) = (instrument,debtor payer provider net,creditor payer provider net)
      then units law instrument net else 0) = _
  rw [(the_first_actual_issue_keeps_material_and_adds_its_exact_claim law before payer provider instrument purpose net issued).2]
  ring

include issued settled in
theorem actual_payment_has_the_same_technology_and_microclock :
    (afterPayment law payer provider instrument purpose net before).technology = before.technology ∧
      (afterPayment law payer provider instrument purpose net before).clock = before.clock ∧
      (afterPayment law payer provider instrument purpose net before).round = before.round := by
  unfold afterPayment
  rw [RawLaw.step, if_pos settled]
  change (afterIssue law payer provider instrument purpose net before).technology = before.technology ∧
    (afterIssue law payer provider instrument purpose net before).clock = before.clock ∧
    (afterIssue law payer provider instrument purpose net before).round = before.round
  unfold afterIssue
  rw [RawLaw.step, if_pos issued]
  exact ⟨rfl,rfl,rfl⟩

include issued settled in
theorem actual_payment_has_its_exact_original_debit_and_credit
    (positive : 0 < law.settlementRate instrument) (person : Party) (good : Good) :
    (afterPayment law payer provider instrument purpose net before).stock person good =
      before.stock person good -
        flowAt (locate (debtor payer provider net) [(law.settlementUnit instrument, |net|)]) person good +
        flowAt (locate (creditor payer provider net) [(law.settlementUnit instrument, |net|)]) person good := by
  have amount := the_claim_units_pay_the_exact_material_amount law instrument net positive
  unfold afterPayment
  rw [RawLaw.step, if_pos settled]
  change (afterIssue law payer provider instrument purpose net before).stock person good -
    flowAt (locate (debtor payer provider net) [(law.settlementUnit instrument, units law instrument net * law.settlementRate instrument)]) person good +
    flowAt (locate (creditor payer provider net) [(law.settlementUnit instrument, units law instrument net * law.settlementRate instrument)]) person good = _
  rw [(the_first_actual_issue_keeps_material_and_adds_its_exact_claim law before payer provider instrument purpose net issued).1,amount]

include issued settled in
theorem actual_payment_pays_the_generated_signed_net
    (positive : 0 < law.settlementRate instrument) (different : payer ≠ provider) :
    (afterPayment law payer provider instrument purpose net before).stock provider (law.settlementUnit instrument) =
        before.stock provider (law.settlementUnit instrument) + net ∧
      (afterPayment law payer provider instrument purpose net before).stock payer (law.settlementUnit instrument) =
        before.stock payer (law.settlementUnit instrument) - net := by
  constructor
  · rw [actual_payment_has_its_exact_original_debit_and_credit law before payer provider instrument purpose net issued settled positive]
    by_cases sign : 0 ≤ net
    · simp [debtor, creditor, sign, flowAt, locate, amount, different, abs_of_nonneg sign]
    · have negative : net ≤ 0 := (lt_of_not_ge sign).le
      simp [debtor, creditor, sign, flowAt, locate, amount, different, abs_of_nonpos negative]
  · rw [actual_payment_has_its_exact_original_debit_and_credit law before payer provider instrument purpose net issued settled positive]
    by_cases sign : 0 ≤ net
    · simp [debtor, creditor, sign, flowAt, locate, amount, Ne.symm different, abs_of_nonneg sign]
    · have negative : net ≤ 0 := (lt_of_not_ge sign).le
      simpa [debtor, creditor, sign, flowAt, locate, amount, Ne.symm different, abs_of_nonpos negative] using
        (sub_eq_add_neg (before.stock payer (law.settlementUnit instrument)) net).symm

include issued settled in
theorem every_other_original_material_coordinate_is_retained
    (positive : 0 < law.settlementRate instrument) (person : Party) (good : Good)
    (outside : good ≠ law.settlementUnit instrument ∨ (person ≠ payer ∧ person ≠ provider)) :
    (afterPayment law payer provider instrument purpose net before).stock person good = before.stock person good := by
  rw [actual_payment_has_its_exact_original_debit_and_credit law before payer provider instrument purpose net issued settled positive]
  rcases outside with otherGood | ⟨notPayer,notProvider⟩
  · simp [flowAt,locate,amount,Ne.symm otherGood]
  · by_cases sign : 0 ≤ net <;>
      simp [debtor,creditor,sign,flowAt,locate,amount,Ne.symm notPayer,Ne.symm notProvider]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement
