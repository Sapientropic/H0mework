import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Syntax

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument)
  (payer provider : Party) (instrument : Instrument) (purpose : Port) (net : ℚ)

/-- Checks are generated on the original two successive currents. A failed
settlement keeps the already issued liability in that same current. -/
inductive Result where
  | noPayment (zero : net = 0)
  | invalidRate (nonzero : net ≠ 0) (failed : ¬ 0 < law.settlementRate instrument)
  | issueRefused (nonzero : net ≠ 0) (rate : 0 < law.settlementRate instrument)
      (failed : ¬ law.Valid before (issue law payer provider instrument purpose net))
  | settlementRefused (nonzero : net ≠ 0) (rate : 0 < law.settlementRate instrument)
      (issued : law.Valid before (issue law payer provider instrument purpose net))
      (failed : ¬ law.Valid (afterIssue law payer provider instrument purpose net before)
        (settle law payer provider instrument purpose net))
  | paid (nonzero : net ≠ 0) (rate : 0 < law.settlementRate instrument)
      (issued : law.Valid before (issue law payer provider instrument purpose net))
      (settled : law.Valid (afterIssue law payer provider instrument purpose net before)
        (settle law payer provider instrument purpose net))

def compile : Result law before payer provider instrument purpose net :=
  if zero : net = 0 then .noPayment zero
  else if rate : 0 < law.settlementRate instrument then
    if issued : law.Valid before (issue law payer provider instrument purpose net) then
      if settled : law.Valid (afterIssue law payer provider instrument purpose net before)
          (settle law payer provider instrument purpose net) then
        .paid zero rate issued settled
      else .settlementRefused zero rate issued settled
    else .issueRefused zero rate issued
  else .invalidRate zero rate

namespace Result

variable {law before payer provider instrument purpose net}

def word : Result law before payer provider instrument purpose net → RawEvent Party Good Port Technology Instrument
  | .noPayment _ | .invalidRate .. => []
  | .issueRefused .. => [issue law payer provider instrument purpose net]
  | .settlementRefused .. | .paid .. =>
      [issue law payer provider instrument purpose net,settle law payer provider instrument purpose net]

def execution (result : Result law before payer provider instrument purpose net) :=
  law.execute before 0 result.word

def next (result : Result law before payer provider instrument purpose net) := result.execution.final

theorem the_inventory_is_the_actual_submitted_prefix (result : Result law before payer provider instrument purpose net) :
    result.execution.items.map ExecutionItem.request = result.word :=
  law.inventory_requests_exact before 0 result.word

theorem no_payment_has_no_actual_effect (zero : net = 0) :
    (Result.noPayment zero : Result law before payer provider instrument purpose net).next = before := rfl

theorem a_refused_issue_does_not_send_the_settlement
    (nonzero : net ≠ 0) (rate : 0 < law.settlementRate instrument)
    (failed : ¬ law.Valid before (issue law payer provider instrument purpose net)) :
    (Result.issueRefused nonzero rate failed : Result law before payer provider instrument purpose net).next = before := by
  exact law.rejected_preserves_current before _ failed

theorem a_refused_settlement_keeps_the_original_issued_debt
    (nonzero : net ≠ 0) (rate : 0 < law.settlementRate instrument)
    (issued : law.Valid before (issue law payer provider instrument purpose net))
    (failed : ¬ law.Valid (afterIssue law payer provider instrument purpose net before)
      (settle law payer provider instrument purpose net)) :
    (Result.settlementRefused nonzero rate issued failed : Result law before payer provider instrument purpose net).next =
      afterIssue law payer provider instrument purpose net before := by
  exact law.rejected_preserves_current _ _ failed

end Result
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement
