import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Feasible
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def materialAddresses (source : C) (script : Script) : List (Party × Good) :=
  (inventory source script).flatMap fun item =>
    (source.native.handlerFace.rootRead.actualDebit item.before item.request).map Prod.fst ++
      (source.native.handlerFace.rootRead.actualCredit item.before item.request).map Prod.fst

theorem stock_outside_original_effects_is_unchanged (source : C) (script : Script)
    (bearer : Party) (good : Good) (outside : (bearer, good) ∉ materialAddresses source script) :
    (endAt source script).raw.stock bearer good = source.raw.stock bearer good := by
  let law := source.native.handlerFace.rootRead
  have debit : law.totalDebit (inventory source script) bearer good = 0 := by
    unfold RawLaw.totalDebit
    apply List.sum_eq_zero
    intro quantity member
    obtain ⟨item, original, rfl⟩ := List.mem_map.mp member
    apply amount_zero_of_absent
    intro lot inside address
    exact outside (List.mem_flatMap.mpr ⟨item, original,
      List.mem_append_left _ (List.mem_map.mpr ⟨lot, inside, address⟩)⟩)
  have credit : law.totalCredit (inventory source script) bearer good = 0 := by
    unfold RawLaw.totalCredit
    apply List.sum_eq_zero
    intro quantity member
    obtain ⟨item, original, rfl⟩ := List.mem_map.mp member
    apply amount_zero_of_absent
    intro lot inside address
    exact outside (List.mem_flatMap.mpr ⟨item, original,
      List.mem_append_right _ (List.mem_map.mpr ⟨lot, inside, address⟩)⟩)
  have balance := all_capacity_is_paid_from_the_original_stock_and_actual_credits source script bearer good
  change (endAt source script).raw.stock bearer good + law.totalDebit (inventory source script) bearer good =
    source.raw.stock bearer good + law.totalCredit (inventory source script) bearer good at balance
  simpa only [debit, credit, add_zero] using balance

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
