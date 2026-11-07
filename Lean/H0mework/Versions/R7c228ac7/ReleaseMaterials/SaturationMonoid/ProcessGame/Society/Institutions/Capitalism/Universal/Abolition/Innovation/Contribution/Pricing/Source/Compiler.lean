import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Branches
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Pricing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (budget : Nat) (mechanism : Trials.Mechanism Party Good Port Technology Instrument)

structure Schedule where
  private mk ::
  provider : Outside.Witness input current members budget mechanism.terms.lender
    (input.law.settlementUnit mechanism.terms.instrument)
  payer : Outside.Witness input current members budget mechanism.terms.borrower
    (input.law.settlementUnit mechanism.terms.instrument)

inductive ScheduleOutcome where
  | ready (schedule : Schedule input current members budget mechanism)
  | providerBlocked (failures : ∀ word ∈ Material.Migration.sourceWords input current budget,
      Outside.Issue input current members word)
  | payerBlocked (failures : ∀ word ∈ Material.Migration.sourceWords input current budget,
      Outside.Issue input current members word)

/-- Only original programmes, actual account coordinates and an execution
budget enter. There is no outside amount, belief, loading or profit multiple. -/
def compileSchedule : ScheduleOutcome input current members budget mechanism :=
  match Outside.generate input current members budget mechanism.terms.lender
      (input.law.settlementUnit mechanism.terms.instrument) with
  | .obstructed failures => .providerBlocked failures
  | .found provider =>
    match Outside.generate input current members budget mechanism.terms.borrower
        (input.law.settlementUnit mechanism.terms.instrument) with
    | .obstructed failures => .payerBlocked failures
    | .found payer => .ready ⟨provider,payer⟩

variable {input current members budget mechanism}

abbrev Schedule.programme (_schedule : Schedule input current members budget mechanism) :=
  atCut input current mechanism

def Schedule.rows (schedule : Schedule input current members budget mechanism)
    (signal : Fin mechanism.code.signals) :=
  riskRows schedule.programme schedule.provider.amount schedule.payer.amount signal

def Schedule.table (schedule : Schedule input current members budget mechanism)
    (signal : Fin mechanism.code.signals) := quote (schedule.rows signal)

inductive NatureOutcome (schedule : Schedule input current members budget mechanism)
    (nature : Request Party Good Port Technology Instrument) where
  | unpriced (outside : PublicFunction.Distributed.Event.adversary nature ∉ schedule.programme.code.eventAlphabet)
  | unread (original : PublicFunction.Distributed.Event.adversary nature ∈ schedule.programme.code.eventAlphabet)
      (unpaid : schedule.programme.paidSignal nature = none)
  | incompatible (signal : Fin mechanism.code.signals)
      (original : PublicFunction.Distributed.Event.adversary nature ∈ schedule.programme.code.eventAlphabet)
      (observed : schedule.programme.paidSignal nature = some signal)
      (issue : QuoteIssue (schedule.rows signal))
  | priced (signal : Fin mechanism.code.signals)
      (original : PublicFunction.Distributed.Event.adversary nature ∈ schedule.programme.code.eventAlphabet)
      (observed : schedule.programme.paidSignal nature = some signal)
      (plan : Quote (schedule.rows signal))

omit [DecidableEq Port] in
theorem original_nature_iff (programme : Trials.Mechanism Party Good Port Technology Instrument)
    (nature : Request Party Good Port Technology Instrument) :
    nature ∈ programme.natureRequests ↔
      PublicFunction.Distributed.Event.adversary nature ∈ programme.code.eventAlphabet := by
  constructor
  · intro member
    obtain ⟨event,original,same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only at same
    case adversary request => cases Option.some.inj same; exact original
    all_goals cases same
  · intro member
    exact List.mem_filterMap.mpr ⟨_,member,rfl⟩

def Schedule.select [DecidableEq Technology] (schedule : Schedule input current members budget mechanism)
    (nature : Request Party Good Port Technology Instrument) : NatureOutcome schedule nature :=
  if supported : nature ∈ schedule.programme.natureRequests then
    let original := (original_nature_iff schedule.programme nature).mp supported
    match observed : schedule.programme.paidSignal nature with
    | none => .unread original observed
    | some signal => match schedule.table signal with
      | .priced plan => .priced signal original observed plan
      | .obstructed issue => .incompatible signal original observed issue
  else .unpriced (fun original => supported ((original_nature_iff schedule.programme nature).mpr original))

def Schedule.payment [DecidableEq Technology] (schedule : Schedule input current members budget mechanism)
    (nature : Request Party Good Port Technology Instrument) (purpose : Port) :
    Option (Σ net : ℚ, Settlement.Result input.law (schedule.programme.after nature)
      mechanism.terms.borrower mechanism.terms.lender mechanism.terms.instrument purpose net) :=
  match schedule.select nature with
  | .priced _ _ _ plan => some ⟨plan.transfer, Settlement.compile input.law
      (schedule.programme.after nature) mechanism.terms.borrower mechanism.terms.lender
      mechanism.terms.instrument purpose plan.transfer⟩
  | _ => none

def Schedule.requests [DecidableEq Technology] (schedule : Schedule input current members budget mechanism)
    (nature : Request Party Good Port Technology Instrument) (purpose : Port) : RawEvent Party Good Port Technology Instrument :=
  schedule.programme.word nature ++
    match schedule.payment nature purpose with
    | some payment => payment.2.word
    | none => []

theorem a_generated_price_preserves_every_matching_original_risk_branch
    (schedule : Schedule input current members budget mechanism)
    (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal)) :
    accountsSafe schedule.programme schedule.provider.amount schedule.payer.amount signal plan.transfer :=
  every_priced_branch_keeps_both_original_accounts _ _ _ _ plan

theorem a_generated_price_is_least_among_all_rules_using_that_local_information
    (schedule : Schedule input current members budget mechanism)
    (signal : Fin mechanism.code.signals) (plan : Quote (schedule.rows signal)) (other : ℚ)
    (safe : accountsSafe schedule.programme schedule.provider.amount schedule.payer.amount signal other) :
    |plan.transfer| ≤ |other| :=
  every_safe_branch_rule_pays_at_least_the_generated_compensation _ _ _ _ plan other safe

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source
