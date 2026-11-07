import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Reading

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- The original guard's need bundle and the live census at this root cut. -/
def requirements (source : C) : List (Party × Use × Good × ℚ) :=
  Material.originalRequirements (Public.Scope.checkInput source.native.input)
    (Actual.origin source.native.input source.native.depth source.native.count) source.members

def delivered (source : C) (script : Script) (bearer : Party) (purpose : Use) (good : Good) : ℚ :=
  Optimality.Cost.resource source.native.input (Evolving.Epoch.Source.originalState source.native)
    (Execution.programme source script) (.use purpose) bearer good

theorem delivered_is_from_original_inventory (source : C) (script : Script)
    (bearer : Party) (purpose : Use) (good : Good) :
    delivered source script bearer purpose good =
      ((Execution.inventory source script).map fun item => flowAt
        (Optimality.Cost.actualPart source.native.handlerFace.rootRead
          item.before item.request (.use purpose)) bearer good).sum := by
  unfold delivered Optimality.Cost.resource
  rw [Execution.material_is_the_folded_actual_inventory]
  rfl

def Covers (source : C) (script : Script) : Prop :=
  ∀ cell ∈ requirements source, cell.2.2.2 ≤ delivered source script cell.1 cell.2.1 cell.2.2.1

structure Deficit (source : C) (script : Script) where
  cell : Party × Use × Good × ℚ
  original : cell ∈ requirements source
  shortage : delivered source script cell.1 cell.2.1 cell.2.2.1 < cell.2.2.2

theorem Deficit.refutes {source : C} {script : Script} (issue : Deficit source script) :
    ¬ Covers source script :=
  fun covered => (not_le_of_gt issue.shortage) (covered issue.cell issue.original)

inductive Inspection (source : C) (script : Script)
  | covered (paid : Covers source script)
  | deficit (issue : Deficit source script)

def inspect (source : C) (script : Script) : Inspection source script :=
  match Material.inspectList (fun cell : Party × Use × Good × ℚ =>
      cell.2.2.2 ≤ delivered source script cell.1 cell.2.1 cell.2.2.1) (requirements source) with
  | .clear paid => .covered paid
  | .failure cell original failed => .deficit ⟨cell, original, lt_of_not_ge failed⟩

theorem uncovered_has_its_original_shortage (source : C) (script : Script)
    (uncovered : ¬ Covers source script) : Nonempty (Deficit source script) :=
  match inspect source script with
  | .covered paid => (uncovered paid).elim
  | .deficit issue => ⟨issue⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand
