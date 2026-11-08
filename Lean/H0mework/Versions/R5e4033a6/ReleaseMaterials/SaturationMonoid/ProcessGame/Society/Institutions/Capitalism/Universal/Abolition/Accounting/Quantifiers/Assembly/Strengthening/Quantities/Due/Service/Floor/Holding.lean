import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def unpaid {source : C} (past : Script) (row : Original source) : ℚ :=
  max 0 (row.val.2.2.2 - Demand.delivered source past row.val.1 row.val.2.1 row.val.2.2.1)

/-- Protect the old floor on its original material address after accounting
for every admitted use already committed by the original prefix. -/
def holding (source : C) (past : Script) (key : Party × Good) : ℚ :=
  ((roster source).map fun row =>
    if (row.val.1, row.val.2.2.1) = key then unpaid past row else 0).sum

theorem an_original_unpaid_floor_is_bounded_by_its_address_holding
    (source : C) (past : Script) (row : Original source) :
    unpaid past row ≤ holding source past (row.val.1, row.val.2.2.1) := by
  unfold holding
  apply List.single_le_sum
  · intro quantity listed
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp listed
    split
    · exact le_max_left _ _
    · exact le_rfl
  · apply List.mem_map.mpr
    refine ⟨row, List.mem_toFinset.mp (every_positive_original_floor_is_present source row), ?_⟩
    rw [if_pos rfl]

theorem original_floor_holding_vanishes_exactly_after_actual_payment (source : C) (past : Script) :
    (∀ key, holding source past key = 0) ↔ Demand.Covers source past := by
  constructor
  · intro noHold cell original
    by_cases positive : 0 < cell.2.2.2
    · let row : Original source := ⟨cell, original, positive⟩
      have carried := an_original_unpaid_floor_is_bounded_by_its_address_holding source past row
      rw [noHold] at carried
      exact sub_nonpos.mp ((le_max_right _ _).trans carried)
    · exact (le_of_not_gt positive).trans (by
        rw [Demand.delivered_is_from_original_inventory]
        apply List.sum_nonneg
        intro quantity listed
        obtain ⟨item, _, rfl⟩ := List.mem_map.mp listed
        exact Optimality.Cost.actualPart_nonnegative _ _ _ _ _ _)
  · intro paid key
    unfold holding
    apply List.sum_eq_zero
    intro quantity listed
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp listed
    have complete := paid _ row.property.1
    simp [unpaid, max_eq_left (sub_nonpos.mpr complete)]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor
