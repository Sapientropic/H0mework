import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.PaidUse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

private theorem an_original_floor_stays_paid_on_every_actual_suffix
    (source : C) (past future : Script) (paid : Demand.Covers source past) :
    Demand.Covers source (past ++ future) := by
  intro cell original
  have old := paid cell original
  let law := source.native.handlerFace.rootRead
  let read := fun item : ExecutionItem Party Good Port Technology Instrument =>
    flowAt (Optimality.Cost.actualPart law item.before item.request (.use cell.2.1)) cell.1 cell.2.2.1
  rw [Demand.delivered_is_from_original_inventory] at old ⊢
  rw [Execution.inventory_append, List.map_append, List.sum_append]
  change cell.2.2.2 ≤ ((Execution.inventory source past).map read).sum + _
  apply old.trans
  apply le_add_of_nonneg_right
  apply List.sum_nonneg
  intro amount listed
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp listed
  exact Optimality.Cost.actualPart_nonnegative law item.before item.request (.use cell.2.1) _ _

/-- The paid successor consumes the literal continuation. The older need
floor and native claim lines stay in the original settlement. -/
theorem PaymentAt.advance_the_original_settlement {source : C} {past : Script} {word held : Word}
    (floorPaid : Demand.Covers source past) (payment : PaymentAt (Execution.endAt source past) word held) :
    Settled source (past ++ Execution.primitiveScript word) ∧
      Execution.endAt source (past ++ Execution.primitiveScript word) =
        Execution.endAt (Execution.endAt source past) (Execution.primitiveScript word) := by
  have exactNext := Execution.endAt_append source past (Execution.primitiveScript word)
  refine ⟨settle source _ ⟨an_original_floor_stays_paid_on_every_actual_suffix source past _ floorPaid, ?_⟩, exactNext⟩
  rw [exactNext]
  exact payment.ready

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
