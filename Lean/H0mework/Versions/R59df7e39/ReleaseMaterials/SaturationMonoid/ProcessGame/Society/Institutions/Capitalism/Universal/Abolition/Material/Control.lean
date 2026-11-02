import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Family

/-!
# Fresh capital control checked without deleting historical capital

The local test scans title/surplus control and every fresh history-control
use. It does not erase `History.discovered`: past circuits retain their exact
origins even when no new admitted item can reproduce their control.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program Source.ProgrammeControl
open Source.ProgrammeControl.Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

def localFamily (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (item : OriginalItem input.law current word) : List Port :=
  generatedFamily input.law current word input.localAttempts item ++
    Kernel.ActualSurplus.familyAt input.law current word item

/-- Finite checks over this word's original instructions and required ports.
The second clause covers all historical circuits, regardless of their age. -/
def NoFreshControl (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  (controlInventory input.law current word (localFamily input current word)).length = 0 ∧
    ∀ item ∈ input.law.rawItems current word,
      ∀ port ∈ input.law.requiredPorts item.before item.request,
        ¬ History.FreshControl input port item

instance (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (NoFreshControl input current word) := by
  unfold NoFreshControl
  infer_instance

theorem noFreshControl_excludes_actual_family
    (visit : RootFace.Visit input)
    (checked : NoFreshControl input
      (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current))
    (item : RootFace.Item input visit) (accepted : input.law.Valid item.val.before item.val.request)
    (port : Port) (required : port ∈ input.law.requiredPorts item.val.before item.val.request) :
    port ∉ Root.Structural.familyAtVisit input visit item := by
  intro controlled
  have empty : controlInventory input.law
      (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current)
      (localFamily input (Root.ProgrammeSource.rawCurrent input visit.current)
        (Root.ProgrammeSource.rawEvent input visit.current)) = [] :=
    List.length_eq_zero_iff.mp checked.1
  simp only [Root.Structural.familyAtVisit, List.mem_append] at controlled
  rcases controlled with (title | surplus) | historical
  · exact (empty_controlInventory_excludes_every_control input.law _ _ _ empty item accepted
      port required) (List.mem_append_left _ title)
  · exact (empty_controlInventory_excludes_every_control input.law _ _ _ empty item accepted
      port required) (List.mem_append_right _ surplus)
  · obtain ⟨_, _, _, fresh⟩ := History.generatedFamily_actual_control input visit item port historical
    exact checked.2 item.val item.property port required fresh

/-- No source-generated capital-control witness survives this admission.
Past history is retained and is not part of the checker target. -/
theorem noFreshControl_actual_control_empty
    (visit : RootFace.Visit input)
    (checked : NoFreshControl input
      (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current)) :
    IsEmpty (ControlUse input.law
      (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current)
      (Root.Structural.familyAtVisit input visit)) := by
  refine ⟨fun controlled => ?_⟩
  exact noFreshControl_excludes_actual_family input visit checked controlled.item
    controlled.accepted controlled.port controlled.required controlled.controlled

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.noFreshControl_actual_control_empty
