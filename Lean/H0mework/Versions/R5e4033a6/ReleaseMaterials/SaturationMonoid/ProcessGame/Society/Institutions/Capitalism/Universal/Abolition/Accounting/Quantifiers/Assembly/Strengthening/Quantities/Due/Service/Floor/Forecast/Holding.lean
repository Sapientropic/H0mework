import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Use

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

def forecastUnpaid {source : C} (past : Script) (word : Word) (row : Original source) : ℚ :=
  let cell := row.val
  max 0 (cell.2.2.2 -
    (Demand.delivered source past cell.1 cell.2.1 cell.2.2.1 + forecastUse word cell.1 cell.2.1 cell.2.2.1))

/-- A proposed use can reduce a protected floor only in its original
material unit, at its original bearer, and for the same purpose. -/
def forecastHolding (source : C) (past : Script) (word : Word) (key : Party × Good) : ℚ :=
  ((roster source).map fun row =>
    if (row.val.1, row.val.2.2.1) = key then forecastUnpaid past word row else 0).sum

def holdingAddresses (source : C) : List (Party × Good) :=
  ((roster source).map fun row => (row.val.1, row.val.2.2.1)).dedup

theorem every_original_floor_address_is_listed (source : C) (row : Original source) :
    (row.val.1, row.val.2.2.1) ∈ holdingAddresses source := by
  apply List.mem_dedup.mpr
  exact List.mem_map.mpr ⟨row, List.mem_toFinset.mp (every_positive_original_floor_is_present source row), rfl⟩

theorem forecastHolding_nonnegative (source : C) (past : Script) (word : Word) (key : Party × Good) :
    0 ≤ forecastHolding source past word key := by
  unfold forecastHolding
  apply List.sum_nonneg
  intro value listed
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp listed
  split
  · exact le_max_left _ _
  · exact le_rfl

theorem forecastHolding_zero_off_support (source : C) (past : Script) (word : Word) (key : Party × Good)
    (absent : key ∉ holdingAddresses source) : forecastHolding source past word key = 0 := by
  unfold forecastHolding
  apply List.sum_eq_zero
  intro value listed
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp listed
  have unrelated : (row.val.1, row.val.2.2.1) ≠ key :=
    fun same => absent (same ▸ every_original_floor_address_is_listed source row)
  exact if_neg unrelated

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor
