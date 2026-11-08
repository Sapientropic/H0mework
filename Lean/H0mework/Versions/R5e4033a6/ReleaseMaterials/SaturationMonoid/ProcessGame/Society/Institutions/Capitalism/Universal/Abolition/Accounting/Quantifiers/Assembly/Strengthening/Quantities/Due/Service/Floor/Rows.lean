import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev Cell := Party × Use × Good × ℚ

abbrev Original (source : C) :=
  { cell : Cell (Party := Party) (Good := Good) // cell ∈ Demand.requirements source ∧ 0 < cell.2.2.2 }

/-- Repeated mentions of the same original total are one obligation. -/
def roster (source : C) : List (Original source) :=
  ((Demand.requirements source).attach.filterMap fun cell =>
    if positive : 0 < cell.val.2.2.2 then some ⟨cell.val, cell.property, positive⟩ else none).dedup

def ids (source : C) : Finset (Original source) := (roster source).toFinset

theorem every_positive_original_floor_is_present (source : C) (row : Original source) :
    row ∈ ids source := by
  apply List.mem_toFinset.mpr
  apply List.mem_dedup.mpr
  apply List.mem_filterMap.mpr
  exact ⟨⟨row.val, row.property.1⟩, List.mem_attach _ _, dif_pos row.property.2⟩

def serviceSlot {source : C} (row : Original source) : ServiceSlot Party Good :=
  ⟨row.val.1, [(row.val.2.2.1, row.val.2.2.2)], row.val.2.1⟩

def tasks (source : C) (opens due : ℚ) (row : Original source) : PublicTaskSpec Party Good where
  slots := [serviceSlot row]
  earliest := opens
  deadline := due
  demand := ⟨serviceSlot row, List.mem_cons_self,
    (row.val.2.2.1, row.val.2.2.2), List.mem_cons_self, row.property.2⟩

theorem original_slot (source : C) (opens due : ℚ) (slot : Slot (ids source) (tasks source opens due)) :
    slot.spec = serviceSlot slot.1.val := by
  unfold Slot.spec
  change ([serviceSlot slot.1.val] : List (ServiceSlot Party Good)).get slot.2 = _
  exact List.getElem_singleton slot.2.isLt

theorem the_original_floor_quantities_are_positive (source : C) (opens due : ℚ) :
    OriginalDemands (ids source) (tasks source opens due) := by
  intro slot
  rw [original_slot]
  intro lot inside
  have original := List.mem_singleton.mp inside
  rw [original]
  exact slot.1.val.property.2.le

def originalLine (source : C) (opens due : ℚ) (row : Original source) :
    Need (ids source) (tasks source opens due) :=
  let slot : Slot (ids source) (tasks source opens due) :=
    ⟨⟨row, every_positive_original_floor_is_present source row⟩, ⟨0, Nat.zero_lt_one⟩⟩
  ⟨slot, ⟨row.val.2.2.1, by
    unfold Slot.goods
    rw [original_slot]
    exact List.mem_toFinset.mpr List.mem_cons_self⟩⟩

theorem the_line_is_the_original_bearer_use_and_quantity (source : C) (script : Script)
    (opens due : ℚ) (reserved : Finset (Ordinal source script)) (row : Original source) :
    let line := originalLine source opens due row
    (line.1.spec.bearer, line.1.spec.purpose, line.2.val,
      (network source script (ids source) (tasks source opens due) reserved).need line) = row.val := by
  change (row.val.1, row.val.2.1, row.val.2.2.1,
    max 0 (amount Good [(row.val.2.2.1, row.val.2.2.2)] row.val.2.2.1)) = row.val
  simp [amount, max_eq_right row.property.2.le]

def allocateOriginalFloor (source : C) (script : Script) (opens due : ℚ)
    (reserved : Finset (Ordinal source script)) :
    (network source script (ids source) (tasks source opens due) reserved).Certificate :=
  allocate source script (ids source) (tasks source opens due) reserved (roster source) rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor
