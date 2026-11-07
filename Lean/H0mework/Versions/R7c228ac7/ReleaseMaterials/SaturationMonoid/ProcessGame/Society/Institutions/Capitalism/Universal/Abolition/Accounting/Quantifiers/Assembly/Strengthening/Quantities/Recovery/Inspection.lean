import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.MaterialSupport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def Restored (origin : C) (exposure repair : Script) : Prop :=
  ∀ bearer good, origin.raw.stock bearer good ≤
    (Execution.endAt origin (exposure ++ repair)).raw.stock bearer good

structure Loss (origin : C) (exposure repair : Script) where
  address : Party × Good
  original : address ∈ Execution.materialAddresses origin (exposure ++ repair)
  unpaid : (Execution.endAt origin (exposure ++ repair)).raw.stock address.1 address.2 <
    origin.raw.stock address.1 address.2

def inspect (origin : C) (exposure repair : Script) : Option (Loss origin exposure repair) :=
  match Material.inspectList
      (fun address : Party × Good => origin.raw.stock address.1 address.2 ≤
        (Execution.endAt origin (exposure ++ repair)).raw.stock address.1 address.2)
      (Execution.materialAddresses origin (exposure ++ repair)) with
  | .clear _ => none
  | .failure address original deficit => some ⟨address, original, lt_of_not_ge deficit⟩

/-- Both exposure and repair contribute addresses. A repair that pays one
person by opening a new physical shortfall for another fails this test. -/
theorem cleared_exactly_when_no_original_actor_loses_stock
    (origin : C) (exposure repair : Script) :
    inspect origin exposure repair = none ↔ Restored origin exposure repair := by
  unfold inspect
  cases Material.inspectList
      (fun address : Party × Good => origin.raw.stock address.1 address.2 ≤
        (Execution.endAt origin (exposure ++ repair)).raw.stock address.1 address.2)
      (Execution.materialAddresses origin (exposure ++ repair)) with
  | clear covered =>
      refine ⟨fun _ bearer good => ?_, fun _ => rfl⟩
      by_cases inside : (bearer, good) ∈ Execution.materialAddresses origin (exposure ++ repair)
      · exact covered (bearer, good) inside
      · exact (Execution.stock_outside_original_effects_is_unchanged origin (exposure ++ repair) bearer good inside).ge
  | failure address original deficit =>
      constructor
      · intro impossible
        contradiction
      · intro paid
        exact (deficit (paid address.1 address.2)).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery
