import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Issues
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (members : List Party) (word : RawEvent Party Good Port Technology Instrument)

def Checks : Prop :=
  Root.Settlement.NonFinancial word ∧
    Material.OriginalNeedFloor input origin current members word ∧
      Material.PeriodChecks input current members word

inductive Issue : Type
  | financial (request : Request Party Good Port Technology Instrument)
      (present : request ∈ word) (unsupported : ¬ Root.Settlement.NonFinancialRequest request)
  | originalNeed (issue : Material.NeedFloorIssue input origin current members word)
  | period (issue : Material.PeriodIssue input current members word)

theorem Issue.refutes (issue : Issue input origin current members word) :
    ¬ Checks input origin current members word := by
  intro checked
  cases issue with
  | financial request present unsupported => exact unsupported (checked.1 request present)
  | originalNeed failed => exact failed.refutes input checked.2.1
  | period failed => exact failed.refutes input current members word checked.2.2

inductive Check : Type
  | accepted (checked : Checks input origin current members word)
  | rejected (issue : Issue input origin current members word)

def inspect : Check input origin current members word :=
  match Root.Settlement.checkFinancial word with
  | .rejected request present unsupported => .rejected (.financial request present unsupported)
  | .accepted nonfinancial =>
      match Material.checkOriginalNeedFloor input origin current members word with
      | .rejected issue => .rejected (.originalNeed issue)
      | .accepted floor =>
          match Material.checkPeriod input current members word with
          | .rejected issue => .rejected (.period issue)
          | .accepted checked => .accepted ⟨nonfinancial, floor, checked⟩

theorem inspect_selects_checked (checked : Checks input origin current members word) :
    ∃ proof, inspect input origin current members word = .accepted proof := by
  cases found : inspect input origin current members word with
  | accepted proof => exact ⟨proof, rfl⟩
  | rejected issue => exact (issue.refutes input origin current members word checked).elim

#print axioms inspect
#print axioms Issue.refutes

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded
