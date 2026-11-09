import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Menus

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev cutAt (source : C) (history : Script) (index : Nat) : C :=
  Quantities.Execution.endAt source (history.take index)

/-- Proposals are generated only after the root has written that cut. Index
orders the writes, while the actual date is read from its material clock. -/
def pressureAt (source : C) (history : Script) (read : C → ℚ)
    (proposals : C → List Word × List Word) (index : Nat) : Option ℚ :=
  let current := cutAt source history index
  let (war, peace) := proposals current
  pressure current read war peace

def onset (source : C) (history : Script) (read : C → ℚ)
    (proposals : C → List Word × List Word) : Option Nat :=
  Threshold.firstPositive (pressureAt source history read proposals) (List.range (history.length + 1))

def peak (source : C) (history : Script) (read : C → ℚ)
    (proposals : C → List Word × List Word) : Option (Nat × ℚ) :=
  Threshold.peak (pressureAt source history read proposals) (List.range (history.length + 1))

theorem onset_is_an_original_cut_with_no_earlier_positive_comparison
    (source : C) (history : Script) (read : C → ℚ) (proposals : C → List Word × List Word)
    {index : Nat} (found : onset source history read proposals = some index) :
    index ≤ history.length ∧ Quantities.Recorded source (history.take index) ∧
      (∃ value, pressureAt source history read proposals index = some value ∧ 0 < value) ∧
      ∃ prior later, List.range (history.length + 1) = prior ++ index :: later ∧
        ∀ earlier ∈ prior, ∀ value,
          pressureAt source history read proposals earlier = some value → value ≤ 0 := by
  obtain ⟨positive, prior, later, order, earlier⟩ := Threshold.firstPositive_exact.mp found
  have inside : index ∈ List.range (history.length + 1) := by simp [order]
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp inside), Quantities.record source _,
    positive, prior, later, order, earlier⟩

theorem peak_is_an_attained_original_cut
    (source : C) (history : Script) (read : C → ℚ) (proposals : C → List Word × List Word)
    {index : Nat} {value : ℚ} (found : peak source history read proposals = some (index, value)) :
    index ≤ history.length ∧ Quantities.Recorded source (history.take index) ∧
      pressureAt source history read proposals index = some value ∧
      ∀ earlier ≤ history.length, ∀ other,
        pressureAt source history read proposals earlier = some other → other ≤ value := by
  obtain ⟨member, exactValue, upper⟩ := Threshold.peak_exact found
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp member), Quantities.record source _, exactValue,
    fun earlier inHistory => upper earlier (List.mem_range.mpr (Nat.lt_succ_of_le inHistory))⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
