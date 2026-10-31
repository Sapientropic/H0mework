import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler.Selection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection.Resource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq Port]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party)

/-- Coverage is over the exact current source menu. It never declares that an
unseen recipe, another plant composition or later source information is impossible. -/
def inspection : List (Σ candidate : RawEvent Party Good Port Technology Instrument,
    Capacity.ResourceResult claim state law members candidate) :=
  (plans claim state law members).map fun candidate =>
    ⟨candidate,Capacity.inspectResources claim state law members candidate⟩

theorem inspect_menu_from_no_compiled_plan (missing : compile claim state law members = none) :
    ∀ candidate ∈ plans claim state law members, ∃ issue,
      Capacity.inspectResources claim state law members candidate = .blocked issue := by
  intro candidate original
  have failed := no_compiled_plan_is_an_exact_menu_inspection_blocker claim state law members missing candidate original
  cases selected : Capacity.inspectResources claim state law members candidate with
  | ready resources => exact (failed resources).elim
  | blocked issue => exact ⟨issue,rfl⟩

theorem every_enough_plan_has_an_exact_successful_raw_inspection
    (plan : Plan claim state law members) :
    ∃ resources, Capacity.inspectResources claim state law members plan.word = .ready resources := by
  cases selected : Capacity.inspectResources claim state law members plan.word with
  | ready resources => exact ⟨resources,rfl⟩
  | blocked issue => exact (Capacity.resource_failure_is_exactly_about_the_same_source_plan claim state law members plan.word issue plan.resources).elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Compiler
