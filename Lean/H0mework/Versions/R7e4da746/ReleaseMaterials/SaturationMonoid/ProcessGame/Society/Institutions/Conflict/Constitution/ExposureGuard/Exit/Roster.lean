import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Footprint
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Exit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual (originalLosses)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ

def roster (seed : C) (community : Party → Community) (anchor history : Word) : List Party :=
  (bearers seed community anchor ++ (originalLosses seed community history).map (fun loss => loss.key.1)).dedup

theorem original_bearer_keeps_their_exit_row (seed : C) (community : Party → Community) (anchor history : Word)
    (person : Party) (original : person ∈ bearers seed community anchor) :
    person ∈ roster seed community anchor history :=
  List.mem_dedup.mpr (List.mem_append_left _ original)

theorem every_actual_victim_keeps_their_exit_row (seed : C) (community : Party → Community) (anchor history : Word)
    (loss : Reparation.Actual.Occurrence seed community)
    (original : loss ∈ originalLosses seed community history) :
    loss.key.1 ∈ roster seed community anchor history :=
  List.mem_dedup.mpr (List.mem_append_right _ (List.mem_map_of_mem original))

omit [DecidableEq Community] in
/-- Read the native need bundles against the retained roster. A victim
who disappears from a later census still has their original need row. -/
def needsAt (baseline : C) (people : List Party) : List Cell :=
  Material.originalRequirements (Public.Scope.checkInput baseline.native.input)
    (Actual.origin baseline.native.input baseline.native.depth baseline.native.count) people

omit [DecidableEq Community] in
theorem the_old_floor_cells_are_in_the_full_source_needs (baseline : C) (people : List Party)
    (cell : Cell) (original : cell ∈ Boundary.floorCells baseline people) :
    cell ∈ needsAt baseline people := by
  obtain ⟨listed, resident⟩ := List.mem_filter.mp original
  unfold Quantities.Demand.requirements Material.originalRequirements at listed
  obtain ⟨person, _, needs⟩ := List.mem_flatMap.mp listed
  have address : cell.1 = person := by
    rcases List.mem_append.mp needs with necessity | maintenance
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp necessity
      rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp maintenance
      rfl
  exact List.mem_flatMap.mpr ⟨person, address ▸ of_decide_eq_true resident, needs⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit
