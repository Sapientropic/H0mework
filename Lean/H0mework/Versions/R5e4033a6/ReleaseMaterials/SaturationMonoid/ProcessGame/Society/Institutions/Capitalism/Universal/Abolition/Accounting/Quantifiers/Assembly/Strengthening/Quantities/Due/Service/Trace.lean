import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveClock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered Execution
open Innovation.Contribution.Pricing.Root.Runtime (Trace)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- A paid primitive batch keeps the clock of its original cut on every
material debit. Its native accounting visits contribute no extra material. -/
theorem timed_primitives_are_the_original_material_at_the_same_clock
    {source target : C} {word : Word} (paid : Trace source word target) :
    timedInventory source (primitiveScript word) =
      (((Physical.Public.interpreter source.native.input).rawItems source.raw word).map
        fun item => ({item with index := 0}, source.raw.clock)) := by
  let script := primitiveScript word
  have finalClock : (endAt source script).raw.clock = source.raw.clock :=
    (congrArg (fun current : C => current.raw.clock) (original_primitive_trace paid)).trans
      (a_paid_primitive_trace_keeps_the_actual_clock paid)
  have stamp (item) (present : item ∈ timedInventory source script) : item.2 = source.raw.clock := by
    obtain ⟨earlier, later⟩ := every_original_service_commits_between_source_and_terminal_clock source script item present
    exact le_antisymm (later.trans_eq finalClock) earlier
  calc
    timedInventory source script = (timedInventory source script).map (fun item => (item.1, source.raw.clock)) := by
      nth_rewrite 1 [← List.map_id (timedInventory source script)]
      apply List.map_congr_left
      intro item present
      exact Prod.ext rfl (stamp item present)
    _ = ((timedInventory source script).map Prod.fst).map (fun item => (item, source.raw.clock)) := by
      rw [List.map_map]
      rfl
    _ = _ := by
      rw [timedInventory_is_the_original_inventory, primitive_inventory paid 0, List.map_map]
      rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
