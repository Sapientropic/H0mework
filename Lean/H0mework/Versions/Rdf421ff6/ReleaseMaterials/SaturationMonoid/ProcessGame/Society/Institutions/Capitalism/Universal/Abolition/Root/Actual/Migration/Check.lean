import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Batch.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program
open Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (pair : RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)

/-- The proposal contains finite code only. Its actual front pays the old
floor; its checked tail is generated at that front's own material target. -/
def Checks : Prop :=
  Batch.Checks input origin current members pair.1 ∧
  Material.ActualAndIndependent input current pair.1 ∧
  Material.ProductionRetained input current members pair.1 ∧
  Material.Migration.RenewalChecks input origin (input.law.next current pair.1) members pair.2

inductive Issue : Type
  | front (issue : Batch.Issue input origin current members pair.1)
  | independence (item : OriginalItem input.law current pair.1)
      (failed : ¬ (input.law.Valid item.val.before (Material.withoutControllerConsents item.val.request) ∧
        ∀ debit ∈ input.law.debit item.val.before item.val.request,
          0 < debit.2 → debit.1.1 = item.val.request.signer))
  | production (person : Party) (original : person ∈ members)
      (failed : ¬ Material.TechniqueDominates (input.law.technique current.technology person)
        (input.law.technique (input.law.next current pair.1).technology person))
  | renewal (issue : Material.Migration.RenewalIssue input origin (input.law.next current pair.1) members pair.2)

theorem Issue.refutes (issue : Issue input origin current members pair) :
    ¬ Checks input origin current members pair := by
  intro checked
  cases issue with
  | front issue => exact issue.refutes input origin current members pair.1 checked.1
  | independence item failed => exact failed (checked.2.1 item.val item.property).2
  | production person original failed => exact failed (checked.2.2.1 person original)
  | renewal issue => exact issue.refutes input origin _ members pair.2 checked.2.2.2

inductive Verdict : Type
  | accepted (checked : Checks input origin current members pair)
  | refused (issue : Issue input origin current members pair)

def inspect : Verdict input origin current members pair :=
  match Batch.inspect input origin current members pair.1 with
  | .refused issue => .refused (.front issue)
  | .accepted front =>
      match Material.inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
          input.law.Valid item.before (Material.withoutControllerConsents item.request) ∧
            ∀ debit ∈ input.law.debit item.before item.request, 0 < debit.2 → debit.1.1 = item.request.signer)
          (input.law.rawItems current pair.1) with
      | .failure item original failed => .refused (.independence ⟨item, original⟩ failed)
      | .clear independent =>
          match Material.inspectList (fun person =>
              Material.TechniqueDominates (input.law.technique current.technology person)
                (input.law.technique (input.law.next current pair.1).technology person)) members with
          | .failure person original failed => .refused (.production person original failed)
          | .clear retained =>
              match Material.Migration.checkRenewal input origin (input.law.next current pair.1) members pair.2 with
              | .accepted tail => .accepted ⟨front,
                  (fun item original => ⟨front.1 item original, independent item original⟩), retained, tail⟩
              | .rejected issue => .refused (.renewal issue)

theorem inspect_selects_every_checked_pair (checked : Checks input origin current members pair) :
    ∃ proof, inspect input origin current members pair = .accepted proof := by
  cases produced : inspect input origin current members pair with
  | accepted proof => exact ⟨proof, rfl⟩
  | refused issue => exact (issue.refutes input origin current members pair checked).elim

#print axioms inspect
#print axioms Issue.refutes
#print axioms inspect_selects_every_checked_pair

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Migration
