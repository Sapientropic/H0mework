import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Preflight

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {input : Root.ProgrammeSource.Input Party Good Port Technology Instrument}
  {current : RawCurrent Party Good Technology Instrument} {members : List Party}
  {budget : Nat} {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  (schedule : Schedule input current members budget mechanism)

inductive Submission (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ) where
  | noQuote (decision : NatureOutcome schedule nature)
  | excessive (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal))
      (amount : ℚ) (submitted : proposed = some amount)
      (safe : accountsSafe schedule.programme schedule.provider.amount schedule.payer.amount signal amount)
      (more : |plan.transfer| < |amount|)
  | providerShortfall (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal))
      (amount : ℚ) (submitted : proposed = some amount) (failed : amount < plan.bounds.1)
  | payerShortfall (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal))
      (amount : ℚ) (submitted : proposed = some amount) (failed : plan.bounds.2 < amount)
  | compensation (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal))
      (original : PublicFunction.Distributed.Event.adversary nature ∈ schedule.programme.code.eventAlphabet)
      (observed : schedule.programme.paidSignal nature = some signal)
      (exactAmount : ∀ amount, proposed = some amount → amount = plan.transfer)

def submit (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ) :
    Submission schedule nature proposed :=
  match schedule.select nature with
  | .priced signal original observed plan =>
      match proposed with
      | none => .compensation signal plan original observed (by intro amount impossible; cases impossible)
      | some amount => match classifyAmount schedule signal plan amount with
        | .compensation same => .compensation signal plan original observed (by
            intro other equality; cases Option.some.inj equality; exact same)
        | .surplus safe more => .excessive signal plan amount rfl safe more
        | .providerShortfall failed => .providerShortfall signal plan amount rfl failed
        | .payerShortfall failed => .payerShortfall signal plan amount rfl failed
  | decision => .noQuote decision

def Submission.net {nature : Request Party Good Port Technology Instrument} {proposed : Option ℚ} :
    Submission schedule nature proposed → Option ℚ
  | .compensation _ plan _ _ _ => some plan.transfer
  | _ => none

def Submission.word {nature : Request Party Good Port Technology Instrument} {proposed : Option ℚ}
    (decision : Submission schedule nature proposed) (purpose : Port) : RawEvent Party Good Port Technology Instrument :=
  match decision with
  | .compensation _ plan _ _ _ =>
      (Settlement.compile input.law (schedule.programme.after nature) mechanism.terms.borrower
        mechanism.terms.lender mechanism.terms.instrument purpose plan.transfer).word
  | _ => []

omit [DecidableEq Technology] in
theorem every_written_risk_claim_uses_exactly_the_generated_compensation
    (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ)
    (decision : Submission schedule nature proposed) (amount : ℚ)
    (written : decision.net schedule = some amount) :
    ∃ signal, ∃ plan : Quote (schedule.rows signal), amount = plan.transfer ∧
      (∀ submitted, proposed = some submitted → submitted = amount) := by
  cases decision with
  | compensation signal plan original observed exactAmount =>
      cases Option.some.inj written
      exact ⟨signal,plan,rfl,exactAmount⟩
  | _ => cases written

omit [DecidableEq Technology] in
theorem a_safe_surplus_cannot_be_written_through_the_required_risk_channel
    (nature : Request Party Good Port Technology Instrument) (proposed : Option ℚ)
    (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal))
    (amount : ℚ) (submitted : proposed = some amount)
    (safe : accountsSafe schedule.programme schedule.provider.amount schedule.payer.amount signal amount)
    (more : |plan.transfer| < |amount|) (purpose : Port) :
    (Submission.excessive signal plan amount submitted safe more : Submission schedule nature proposed).word schedule purpose = [] := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source
