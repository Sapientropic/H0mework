import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  {current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}

namespace Operation

def word : Operation input depth count prefixLimit renewalLimit current → RawEvent Party Good Port Technology Instrument
  | .migration plan _ => plan.pair.1
  | .renewal word _ _ => word
  | .repair _ attempt => [attempt.request]

def execution (operation : Operation input depth count prefixLimit renewalLimit current) :=
  input.law.execute current.raw 0 (operation.word input depth count prefixLimit renewalLimit)

def next : Operation input depth count prefixLimit renewalLimit current →
    State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | .migration plan _ =>
      let after := input.law.next current.raw plan.pair.1
      ⟨after, .renewal plan.pair.2, Repair.alphabet input after⟩
  | .renewal word _ _ =>
      let after := input.law.next current.raw word
      ⟨after, .renewal word, Repair.alphabet input after⟩
  | .repair _ attempt => ⟨attempt.after input, .seeking, attempt.tail⟩

theorem requested_items_are_the_original_word
    (operation : Operation input depth count prefixLimit renewalLimit current) :
    (operation.execution input depth count prefixLimit renewalLimit).items.map ExecutionItem.request =
      operation.word input depth count prefixLimit renewalLimit :=
  input.law.inventory_requests_exact current.raw 0 _

theorem whole_material_balance (operation : Operation input depth count prefixLimit renewalLimit current)
    (person : Party) (good : Good) :
    (operation.next input depth count prefixLimit renewalLimit).raw.stock person good +
        input.law.totalDebit (operation.execution input depth count prefixLimit renewalLimit).items person good =
      current.raw.stock person good +
        input.law.totalCredit (operation.execution input depth count prefixLimit renewalLimit).items person good := by
  cases operation with
  | migration plan selected => exact input.law.actual_next_material_balance current.raw plan.pair.1 person good
  | renewal word original checked => exact input.law.actual_next_material_balance current.raw word person good
  | repair cause attempt => exact input.law.execute_material_balance current.raw 0 [attempt.request] person good

theorem original_claims_are_kept (operation : Operation input depth count prefixLimit renewalLimit current) :
    (operation.next input depth count prefixLimit renewalLimit).raw.claims = current.raw.claims := by
  cases operation with
  | migration plan selected => exact plan.checked.1.2.2.2.1.next_claims input.law current.raw plan.pair.1
  | renewal word original checked => exact checked.1.next_claims input.law current.raw word
  | repair cause attempt => exact (attempt.microstep_keeps_original_debt_and_period input depth count).1

theorem repair_consumes_real_code_and_cannot_advance_a_period
    (cause : Cause input depth count prefixLimit renewalLimit current)
    (attempt : Repair.AttemptAt input depth count current.raw (cause.focus input depth count prefixLimit renewalLimit) current.remaining) :
    let next := (Operation.repair cause attempt).next input depth count prefixLimit renewalLimit
    next.remaining.length < current.remaining.length ∧ next.raw.clock = current.raw.clock ∧ next.raw.round = current.raw.round :=
  ⟨Repair.attempted_inventory_strictly_decreases input depth count attempt,
    (attempt.microstep_keeps_original_debt_and_period input depth count).2⟩

end Operation

/-- No automatic operation is returned for an exhausted responsibility.
An actual registration is a different source event, not an empty retry. -/
def step? (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  match decide input depth count prefixLimit renewalLimit current with
  | .action operation => some (operation.next input depth count prefixLimit renewalLimit)
  | .blocked _ => none

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual
