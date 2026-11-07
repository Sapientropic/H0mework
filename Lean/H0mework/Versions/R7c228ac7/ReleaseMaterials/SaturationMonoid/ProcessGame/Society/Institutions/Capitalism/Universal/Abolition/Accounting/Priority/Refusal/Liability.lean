import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (before : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

/-- This is a read of the existing row after its actual word. It contains no
new claim, debt quantity, ledger, or alleged harm from the act of refusing. -/
structure LiabilityAt : Type where
  payment : Responsibility.Family.PaymentStatus claim (Responsibility.Family.State.advance claim before law word)
    (Responsibility.Family.positiveScope mechanism past nature response)
  needs : Responsibility.Family.NeedDisposition law before.raw
    (Responsibility.Family.State.attempt claim before law word).actualWord members
  original_financial_claims : (Responsibility.Family.State.advance claim before law word).raw.claims = before.raw.claims

def carryLiability : LiabilityAt claim before law members word where
  payment := Responsibility.Family.inspectPayment claim (Responsibility.Family.State.advance claim before law word)
    (Responsibility.Family.positiveScope mechanism past nature response)
  needs := Responsibility.Family.inspectActualNeeds claim before law word members
  original_financial_claims := Responsibility.Family.State.actual_advance_retains_every_original_financial_claim claim before law word

theorem a_carried_positive_cell_is_an_original_actual_residual
    (liability : LiabilityAt claim before law members word) :
    match liability.payment with
    | .paid _ => Responsibility.Family.State.isPaid claim (Responsibility.Family.State.advance claim before law word)
    | .unpaid key _ _ => key ∈ Responsibility.Family.positiveScope mechanism past nature response ∧
        0 < (Responsibility.Family.State.advance claim before law word).remaining key := by
  cases liability.payment with
  | paid complete => exact complete
  | unpaid key original positive => exact ⟨original,positive⟩

theorem an_already_paid_row_cannot_generate_a_new_positive_liability
    (paid : Responsibility.Family.State.isPaid claim before) (_liability : LiabilityAt claim before law members word) :
    Responsibility.Family.State.isPaid claim (Responsibility.Family.State.advance claim before law word) := by
  intro key original
  exact le_antisymm
    (by simpa only [paid key original] using
      Responsibility.Family.State.actual_advance_never_refills_any_original_cell claim before law word key)
    ((Responsibility.Family.State.advance claim before law word).nonnegative key)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal
