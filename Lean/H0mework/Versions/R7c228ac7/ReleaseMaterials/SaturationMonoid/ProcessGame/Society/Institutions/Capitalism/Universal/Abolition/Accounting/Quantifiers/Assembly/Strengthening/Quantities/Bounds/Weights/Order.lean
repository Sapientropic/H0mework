import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights.Support

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights

open Source.Program Abolition.Root Abolition.Root.Registered
open Optimality.Cost
open scoped BigOperators

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Cell" => Channel × Party × Good

def timeOnly : LinearReadout Party Good :=
  ⟨fun _ _ _ => 0, fun _ _ _ => le_rfl, 1, zero_le_one⟩

def materialOnly (address : Cell) : LinearReadout Party Good :=
  ⟨fun channel party good => if address = (channel, party, good) then 1 else 0,
    fun _ _ _ => by split <;> norm_num, 0, le_rfl⟩

theorem clock_is_its_own_weighted_readout (source : C) (script : Script) :
    nativeValue source script timeOnly = elapsed source script := by
  rw [the_original_linear_cost_is_a_weighting_of_the_same_actual_inventory]
  simp [weightAt, timeOnly]

theorem each_material_address_is_its_own_weighted_readout (source : C) (script : Script) (address : Cell) :
    nativeValue source script (materialOnly address) = amount Cell (material source script) address := by
  rw [the_original_linear_cost_is_a_weighting_of_the_same_actual_inventory]
  simp only [materialOnly, weightAt, zero_mul, add_zero, amount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _
  by_cases same : address = entry.1
  · simp only [same, ite_true, one_mul]
  · simp only [if_neg same, if_neg (Ne.symm same), zero_mul]

def NoHigherBurden (source : C) (first second : Script) : Prop :=
  elapsed source first ≤ elapsed source second ∧
    ∀ address, amount Cell (material source first) address ≤ amount Cell (material source second) address

/-- Agreement of every nonnegative accounting convention is exactly
the coordinatewise order of the original time and material burdens. -/
theorem agreement_of_every_weighting_iff_the_original_burden_order
    (source : C) (first second : Script) :
    (∀ reading, nativeValue source first reading ≤ nativeValue source second reading) ↔
      NoHigherBurden source first second := by
  constructor
  · intro every
    exact ⟨by simpa only [clock_is_its_own_weighted_readout] using every timeOnly,
      fun address => by simpa only [each_material_address_is_its_own_weighted_readout] using every (materialOnly address)⟩
  · intro paid reading
    let support := ((material source first).map Prod.fst).toFinset ∪ ((material source second).map Prod.fst).toFinset
    have left : ∀ entry ∈ material source first, entry.1 ∈ support := fun entry seen =>
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, seen, rfl⟩))
    have right : ∀ entry ∈ material source second, entry.1 ∈ support := fun entry seen =>
      Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, seen, rfl⟩))
    rw [the_grouped_original_cost_retains_each_actual_material_address source first reading support left,
      the_grouped_original_cost_retains_each_actual_material_address source second reading support right]
    refine add_le_add (Finset.sum_le_sum fun address _ => ?_)
      (mul_le_mul_of_nonneg_left paid.1 reading.time_nonnegative)
    exact mul_le_mul_of_nonneg_left (paid.2 address) (reading.resource_nonnegative address.1 address.2.1 address.2.2)

theorem incompatible_burdens_reverse_under_two_permitted_weightings
    (source : C) (first second : Script)
    (left : ¬ NoHigherBurden source first second) (right : ¬ NoHigherBurden source second first) :
    ∃ firstRead secondRead,
      nativeValue source second firstRead < nativeValue source first firstRead ∧
      nativeValue source first secondRead < nativeValue source second secondRead := by
  classical
  obtain ⟨firstRead, greater⟩ := not_forall.mp
    (fun every => left ((agreement_of_every_weighting_iff_the_original_burden_order source first second).mp every))
  obtain ⟨secondRead, smaller⟩ := not_forall.mp
    (fun every => right ((agreement_of_every_weighting_iff_the_original_burden_order source second first).mp every))
  exact ⟨firstRead, secondRead, lt_of_not_ge greater, lt_of_not_ge smaller⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights
