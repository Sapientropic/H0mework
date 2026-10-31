import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Control
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity

/-!
# Material admission checks for one proposed liberation period

All quantities are computed from the original interpreter. The checks keep
original members, needs, material contributions and production techniques;
no target current, successful future or C-free label is supplied by a caller.
They are subordinate to actual selection and do not themselves execute a word.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Consent deletion is only a test: the actual word still has its original
requests. Acceptance of this test proves no controller consent is needed. -/
def withoutControllerConsents (request : Request Party Good Port Technology Instrument) :=
  { request with consents := [] }

def ActualAndIndependent (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ item ∈ input.law.rawItems current word,
    input.law.Valid item.before item.request ∧
      input.law.Valid item.before (withoutControllerConsents item.request) ∧
      (∀ debit ∈ input.law.debit item.before item.request,
        0 < debit.2 → debit.1.1 = item.request.signer)

instance (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (ActualAndIndependent input current word) := by
  unfold ActualAndIndependent
  infer_instance

/-- Comparison uses the original goods and technology recipes. Distinct goods
are not added through an observer-supplied conversion or utility weight. -/
def TechniqueDominates (before after : Technique Good Port) : Prop :=
  (∀ item ∈ before.outputs ++ after.outputs,
    amount Good before.outputs item.1 ≤ amount Good after.outputs item.1) ∧
  (∀ item ∈ before.inputs ++ after.inputs,
    amount Good after.inputs item.1 ≤ amount Good before.inputs item.1) ∧
  (∀ item ∈ before.maintenance ++ after.maintenance,
    amount Good after.maintenance item.1 ≤ amount Good before.maintenance item.1)

instance (before after : Technique Good Port) : Decidable (TechniqueDominates before after) := by
  unfold TechniqueDominates
  infer_instance

def ProductionRetained (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ person ∈ members,
    TechniqueDominates (input.law.technique current.technology person)
      (input.law.technique (input.law.next current word).technology person)

instance (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (ProductionRetained input current members word) := by
  unfold ProductionRetained
  infer_instance

def PolicyExplained : Prop :=
  match input.law.policy with
  | .unrestricted | .settlement _ => True
  | .opaque _ => False

instance : Decidable (PolicyExplained input) := by
  unfold PolicyExplained
  cases input.law.policy <;> infer_instance

/-- Every original instruction must be lawful and paid. In this interpreter
an instruction does not advance the period clock; needs are settled before
`next` advances it. Multi-period migration must apply this test at every period. -/
def PeriodChecks (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ActualAndIndependent input current word ∧
    Exit.Necessity.AllNeedsPaid input.law current members word ∧
    NoFreshControl input current word ∧
    ProductionRetained input current members word ∧ PolicyExplained input

instance (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (PeriodChecks input current members word) := by
  unfold PeriodChecks
  infer_instance

/-- These are literal intermediate executions, not a reconstructed receipt
history. Old debt changes only through actual issue/assignment/paid settlement. -/
theorem checked_period_material_balance
    (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (_checked : PeriodChecks input current members word) (person : Party) (good : Good) :
    (input.law.next current word).stock person good +
        input.law.totalDebit (input.law.rawItems current word) person good =
      current.stock person good + input.law.totalCredit (input.law.rawItems current word) person good :=
  input.law.actual_next_material_balance current word person good

theorem checked_period_financial_balance
    (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (checked : PeriodChecks input current members word) (code : Instrument) (debtor creditor : Party) :
    (input.law.next current word).claims code debtor creditor = current.claims code debtor creditor +
      (word.map (fun request => RawLaw.claimDelta request code debtor creditor)).sum :=
  input.law.accepted_next_financial_balance current word
    (fun item inside => (checked.1 item inside).1) code debtor creditor

theorem checked_period_original_member_needs
    (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (checked : PeriodChecks input current members word) (person : Party) (present : person ∈ members) :
    Exit.Necessity.BundlePaid input.law current word person (input.law.necessities current person) .necessity ∧
      Exit.Necessity.BundlePaid input.law current word person
        (input.law.mandatoryMaintenance current person) .maintenance :=
  checked.2.1 person present

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.checked_period_financial_balance
