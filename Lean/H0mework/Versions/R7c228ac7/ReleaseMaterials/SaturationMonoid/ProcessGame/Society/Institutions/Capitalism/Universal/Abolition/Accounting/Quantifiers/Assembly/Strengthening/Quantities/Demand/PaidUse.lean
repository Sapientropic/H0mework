import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand

open Source.Program Abolition.Root Abolition.Root.Registered
open Optimality.Cost

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- One original paid use supplies a lower bound on total same-purpose
delivery. Other actual uses add nonnegative amounts at this address. -/
theorem an_original_paid_use_is_counted (source : C) (script : Script)
    (item : ExecutionItem Party Good Port Technology Instrument) (original : item ∈ Execution.inventory source script)
    (bearer : Party) (goods : Bundle Good) (purpose : Use) (good : Good)
    (kind : item.request.operation = .use bearer goods purpose)
    (paid : source.native.handlerFace.rootRead.Valid item.before item.request) :
    amount Good goods good ≤ delivered source script bearer purpose good := by
  let law := source.native.handlerFace.rootRead
  let value := fun event : ExecutionItem Party Good Port Technology Instrument =>
    flowAt (actualPart law event.before event.request (.use purpose)) bearer good
  have charge : value item = amount Good goods good := by
    change flowAt (actualPart law item.before item.request (.use purpose)) bearer good = _
    have valid : law.Valid item.before item.request := paid
    simp only [actualPart, if_pos valid]
    simp [part, kind, RawLaw.debit, locate, flowAt, amount, List.map_map, Function.comp_def]
  rw [delivered_is_from_original_inventory, ← charge]
  change value item ≤ ((Execution.inventory source script).map value).sum
  apply List.single_le_sum
  · intro amount listed
    obtain ⟨event, _, rfl⟩ := List.mem_map.mp listed
    exact actualPart_nonnegative law event.before event.request (.use purpose) bearer good
  · exact List.mem_map.mpr ⟨item, original, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand
