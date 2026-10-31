import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Material.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Material.Safety

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (nature : mechanism.Nature)

def investmentLoss (person : Party) (good : Good) : ℚ :=
  if mechanism.funded then flowAt
    (mechanism.code.law.actualDebit mechanism.fundingAfter mechanism.investmentRequest) person good else 0

def ProductiveItem (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
  match item.request.operation with
  | .produce _ => mechanism.code.law.Valid item.before item.request ∧
      ∃ entry ∈ mechanism.code.law.actualCredit item.before item.request, 0 < entry.2
  | _ => False

instance (item : ExecutionItem Party Good Port Technology Instrument) : Decidable (ProductiveItem mechanism item) := by
  unfold ProductiveItem
  cases item.request.operation <;> infer_instance

def Productive : Prop := ∃ item ∈ mechanism.code.law.rawItems (mechanism.after nature) (mechanism.proposal nature),
  ProductiveItem mechanism item

instance : Decidable (Productive mechanism nature) := by
  unfold Productive
  infer_instance

def ContinuationChecks : Prop :=
  (∀ item ∈ mechanism.code.law.rawItems (mechanism.after nature) (mechanism.proposal nature),
    mechanism.code.law.Valid item.before item.request) ∧
    ServiceAdequate mechanism.code.law (mechanism.after nature) mechanism.code.task (mechanism.proposal nature) ∧
      Exit.Necessity.AllNeedsPaid mechanism.code.law (mechanism.after nature) mechanism.code.parties
        (mechanism.proposal nature) ∧ Productive mechanism nature

instance : Decidable (ContinuationChecks mechanism nature) := by
  unfold ContinuationChecks
  infer_instance

def Ready : Prop := mechanism.funded = true ∧ mechanism.invested = true ∧ mechanism.observed nature = true ∧
  Safety.Safe mechanism nature ∧ ContinuationChecks mechanism nature

inductive Failure where
  | unfunded (original : mechanism.fundingReceipt = none)
  | investment (unpaid : mechanism.invested = false)
  | observation (unpaid : mechanism.observed nature = false)
  | budgetViolation (issue : Safety.Issue mechanism nature)
  | refused (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ mechanism.code.law.rawItems (mechanism.after nature) (mechanism.proposal nature))
      (failed : ¬ mechanism.code.law.Valid item.before item.request)
  | service (unpaid : ¬ ServiceAdequate mechanism.code.law (mechanism.after nature)
      mechanism.code.task (mechanism.proposal nature))
  | unpaidNecessity (person : Party) (original : person ∈ mechanism.code.parties)
      (unpaid : ¬ Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
        person (mechanism.code.law.necessities (mechanism.after nature) person) .necessity)
  | unpaidMaintenance (person : Party) (original : person ∈ mechanism.code.parties)
      (unpaid : ¬ Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
        person (mechanism.code.law.mandatoryMaintenance (mechanism.after nature) person) .maintenance)
  | noProduction (absent : ¬ Productive mechanism nature)

theorem Failure.excludes_ready (failure : Failure mechanism nature) : ¬ Ready mechanism nature := by
  intro ready
  cases failure with
  | unfunded original =>
      have funded := ready.1
      change mechanism.fundingReceipt.isSome = true at funded
      rw [original] at funded
      cases funded
  | investment unpaid => cases unpaid.symm.trans ready.2.1
  | observation unpaid => cases unpaid.symm.trans ready.2.2.1
  | budgetViolation issue => exact issue.refutes mechanism nature ready.2.2.2.1
  | refused item original failed => exact failed (ready.2.2.2.2.1 item original)
  | service unpaid => exact unpaid ready.2.2.2.2.2.1
  | unpaidNecessity person original unpaid => exact unpaid (ready.2.2.2.2.2.2.1 person original).1
  | unpaidMaintenance person original unpaid => exact unpaid (ready.2.2.2.2.2.2.1 person original).2
  | noProduction absent => exact absent ready.2.2.2.2.2.2.2

private def needsFailure (person : Party) (original : person ∈ mechanism.code.parties)
    (failed : ¬ (Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
        person (mechanism.code.law.necessities (mechanism.after nature) person) .necessity ∧
      Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
        person (mechanism.code.law.mandatoryMaintenance (mechanism.after nature) person) .maintenance)) : Failure mechanism nature :=
  if paid : Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
      person (mechanism.code.law.necessities (mechanism.after nature) person) .necessity then
    .unpaidMaintenance person original (fun maintained => failed ⟨paid, maintained⟩)
  else .unpaidNecessity person original paid

structure Accepted where
  private mk ::
  finance : Financing.Disbursement mechanism.code.law mechanism.code.initial mechanism.funding mechanism.terms
  financeRead : mechanism.fundingReceipt = some finance
  investmentPaid : mechanism.invested = true
  observationPaid : mechanism.observed nature = true
  safe : Safety.Safe mechanism nature
  continuation : ContinuationChecks mechanism nature

inductive Result where
  | accepted (result : Accepted mechanism nature)
  | failed (failure : Failure mechanism nature)

/-- The result is read from the one emitted raw word and its actual paid
local record. A failed trial is an outcome; success is never an input. -/
def generate : Result mechanism nature :=
  match financeRead : mechanism.fundingReceipt with
  | none => .failed (.unfunded financeRead)
  | some finance =>
      if investmentPaid : mechanism.invested = true then
        if observationPaid : mechanism.observed nature = true then
          match Safety.check mechanism nature with
          | .rejected issue => .failed (.budgetViolation issue)
          | .accepted safe =>
              match Material.inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
                  mechanism.code.law.Valid item.before item.request)
                  (mechanism.code.law.rawItems (mechanism.after nature) (mechanism.proposal nature)) with
              | .failure item original failed => .failed (.refused item original failed)
              | .clear legal =>
                  if service : ServiceAdequate mechanism.code.law (mechanism.after nature)
                      mechanism.code.task (mechanism.proposal nature) then
                    if productive : Productive mechanism nature then
                      match Material.inspectList (fun person =>
                          Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
                            person (mechanism.code.law.necessities (mechanism.after nature) person) .necessity ∧
                          Exit.Necessity.BundlePaid mechanism.code.law (mechanism.after nature) (mechanism.proposal nature)
                            person (mechanism.code.law.mandatoryMaintenance (mechanism.after nature) person) .maintenance)
                          mechanism.code.parties with
                      | .clear needs =>
                          .accepted ⟨finance, financeRead, investmentPaid, observationPaid, safe, legal, service, needs, productive⟩
                      | .failure person original failed => .failed (needsFailure mechanism nature person original failed)
                    else .failed (.noProduction productive)
                  else .failed (.service service)
        else .failed (.observation (Bool.eq_false_of_not_eq_true observationPaid))
      else .failed (.investment (Bool.eq_false_of_not_eq_true investmentPaid))

theorem generated_success_or_its_exact_original_failure :
    match mechanism.generate nature with
    | .accepted _ => ContinuationChecks mechanism nature ∧ Safety.Safe mechanism nature
    | .failed _ => ¬ Ready mechanism nature := by
  cases mechanism.generate nature with
  | accepted accepted => exact ⟨accepted.continuation, accepted.safe⟩
  | failed failure => exact failure.excludes_ready mechanism nature

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
