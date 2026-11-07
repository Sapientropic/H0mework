import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- A calculation of the original raw recipe effects, before admission.
It uses paidStep, never actualDebit's rejected-zero convention. These items
are symbolic calculations, not a second actual occurrence or ledger. -/
def execute (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) :
    Nat → RawEvent Party Good Port Technology Instrument → ExecutionResult Party Good Port Technology Instrument
  | _, [] => ⟨current,[]⟩
  | index, request :: rest =>
    let later := execute law (law.paidStep current request) (index + 1) rest
    ⟨later.final,⟨index,current,request⟩ :: later.items⟩

def debit (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (actor : Party) (good : Good) : ℚ :=
  (items.map fun item => flowAt (law.debit item.before item.request) actor good).sum

def credit (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (actor : Party) (good : Good) : ℚ :=
  (items.map fun item => flowAt (law.credit item.before item.request) actor good).sum

def net (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (actor : Party) (good : Good) : ℚ :=
  credit law items actor good - debit law items actor good

theorem symbolic_stock_is_exactly_the_original_primitive_net
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument) (actor : Party) (good : Good) :
    (execute law current index word).final.stock actor good = current.stock actor good +
      net law (execute law current index word).items actor good := by
  induction word generalizing current index with
  | nil => simp [execute,net,debit,credit]
  | cons request rest inherited =>
    have later := inherited (law.paidStep current request) (index + 1)
    simp only [execute,net,debit,credit,List.map_cons,List.sum_cons,RawLaw.paidStep] at later ⊢
    linarith

/-- Primitive side conditions are separate source facts: permissions and policy,
raw nonnegative recipe amounts, the source demand guard, and physical affordability.
No actual Valid, paid service, next current or successful gate is supplied. -/
structure Conditions (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : Prop where
  signer : ∀ item ∈ items, RawLaw.SignerMatches item.request
  policy : ∀ item ∈ items, law.operationAllowed item.before item.request = true
  permission : ∀ item ∈ items, ∀ port ∈ law.requiredPorts item.before item.request,
    law.allowed item.before.technology port item.request.signer = true ∨
      law.controller item.before.technology port ∈ item.request.consents
  demand : ∀ item ∈ items, law.ClaimGuard item.before item.request
  debitNonnegative : ∀ item ∈ items, NonnegativeBundle (Party × Good) (law.debit item.before item.request)
  creditNonnegative : ∀ item ∈ items, NonnegativeBundle (Party × Good) (law.credit item.before item.request)
  affordable : ∀ item ∈ items, ∀ entry ∈ law.debit item.before item.request,
    flowAt (law.debit item.before item.request) entry.1.1 entry.1.2 ≤ item.before.stock entry.1.1 entry.1.2

namespace Conditions

variable {law : RawLaw Party Good Port Technology Instrument}
  {items : List (ExecutionItem Party Good Port Technology Instrument)} (conditions : Conditions law items)

omit [DecidableEq Instrument] in
include conditions in
theorem restrict {part : List (ExecutionItem Party Good Port Technology Instrument)}
    (included : ∀ item ∈ part, item ∈ items) : Conditions law part where
  signer := fun item member => conditions.signer item (included item member)
  policy := fun item member => conditions.policy item (included item member)
  permission := fun item member => conditions.permission item (included item member)
  demand := fun item member => conditions.demand item (included item member)
  debitNonnegative := fun item member => conditions.debitNonnegative item (included item member)
  creditNonnegative := fun item member => conditions.creditNonnegative item (included item member)
  affordable := fun item member => conditions.affordable item (included item member)

omit [DecidableEq Instrument] in
include conditions in
theorem actual_validity_is_generated (item : ExecutionItem Party Good Port Technology Instrument) (member : item ∈ items) :
    law.Valid item.before item.request :=
  ⟨⟨conditions.signer item member,conditions.policy item member⟩,conditions.permission item member,
    conditions.demand item member,conditions.debitNonnegative item member,conditions.creditNonnegative item member,
    conditions.affordable item member⟩

end Conditions

theorem all_primitive_effects_become_the_same_actual_execution
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (conditions : Conditions law (execute law current index word).items) :
    law.execute current index word = execute law current index word := by
  induction word generalizing current index with
  | nil => rfl
  | cons request rest inherited =>
    have firstValid := conditions.actual_validity_is_generated ⟨index,current,request⟩ List.mem_cons_self
    have later := conditions.restrict (part := (execute law (law.paidStep current request) (index + 1) rest).items)
      (fun item member => List.mem_cons_of_mem _ member)
    simp only [RawLaw.execute,execute,RawLaw.step,if_pos firstValid,inherited _ _ later]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Primitive
