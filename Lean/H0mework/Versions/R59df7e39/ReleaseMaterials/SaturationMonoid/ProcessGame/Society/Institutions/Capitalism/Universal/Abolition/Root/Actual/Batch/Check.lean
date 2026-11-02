import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Issues

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Batch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Source.ProgrammeControl
open Material

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (word : RawEvent Party Good Port Technology Instrument)

/-- This admits an actual paid period, not an abolition certificate. Financial
instructions retain their ordinary native accounting obligations. -/
def Checks : Prop :=
  (∀ item ∈ input.law.rawItems current word, input.law.Valid item.before item.request) ∧
    Exit.Necessity.AllNeedsPaid input.law current members word ∧
    Material.OriginalNeedFloor input origin current members word

inductive Issue : Type
  | refused (item : OriginalItem input.law current word)
      (failed : ¬ input.law.Valid item.val.before item.val.request)
  | necessity (person : Party) (member : person ∈ members)
      (unpaid : ¬ Exit.Necessity.BundlePaid input.law current word person
        (input.law.necessities current person) .necessity)
  | maintenance (person : Party) (member : person ∈ members)
      (unpaid : ¬ Exit.Necessity.BundlePaid input.law current word person
        (input.law.mandatoryMaintenance current person) .maintenance)
  | originalFloor (issue : Material.NeedFloorIssue input origin current members word)

theorem Issue.refutes (issue : Issue input origin current members word) :
    ¬ Checks input origin current members word := by
  intro checked
  cases issue with
  | refused item failed => exact failed (checked.1 item.val item.property)
  | necessity person member unpaid => exact unpaid (checked.2.1 person member).1
  | maintenance person member unpaid => exact unpaid (checked.2.1 person member).2
  | originalFloor issue => exact issue.refutes input checked.2.2

inductive Verdict : Type
  | accepted (checked : Checks input origin current members word)
  | refused (issue : Issue input origin current members word)

def inspect : Verdict input origin current members word :=
  match inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
      input.law.Valid item.before item.request) (input.law.rawItems current word) with
  | .failure item original failed => .refused (.refused ⟨item, original⟩ failed)
  | .clear accepted =>
      match inspectList (fun person =>
          Exit.Necessity.BundlePaid input.law current word person (input.law.necessities current person) .necessity ∧
          Exit.Necessity.BundlePaid input.law current word person (input.law.mandatoryMaintenance current person) .maintenance)
          members with
      | .failure person original unpaid =>
          if paid : Exit.Necessity.BundlePaid input.law current word person
              (input.law.necessities current person) .necessity then
            .refused (.maintenance person original (fun maintained => unpaid ⟨paid, maintained⟩))
          else .refused (.necessity person original paid)
      | .clear needs =>
          match Material.checkOriginalNeedFloor input origin current members word with
          | .rejected issue => .refused (.originalFloor issue)
          | .accepted floor => .accepted ⟨accepted, needs, floor⟩

theorem inspect_selects_every_checked_word (checked : Checks input origin current members word) :
    ∃ proof, inspect input origin current members word = .accepted proof := by
  cases found : inspect input origin current members word with
  | accepted proof => exact ⟨proof, rfl⟩
  | refused issue => exact (issue.refutes input origin current members word checked).elim

#print axioms inspect
#print axioms Issue.refutes
#print axioms inspect_selects_every_checked_word

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Batch
