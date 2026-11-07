import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Profile
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights

open Source.Program Abolition.Root Abolition.Root.Registered
open Optimality.Cost
open scoped BigOperators

noncomputable section

private theorem sum_through_flatMap {Input Entry : Type} (items : List Input)
    (entries : Input → List Entry) (read : Entry → ℚ) :
    ((items.flatMap entries).map read).sum = (items.map fun item => ((entries item).map read).sum).sum := by
  induction items with
  | nil => rfl
  | cons item later ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem regroup_material_weight {Address : Type} [DecidableEq Address]
    (incidence : List (Address × ℚ)) (support : Finset Address) (weight : Address → ℚ)
    (covers : ∀ entry ∈ incidence, entry.1 ∈ support) :
    (incidence.map fun entry => weight entry.1 * entry.2).sum =
      ∑ address ∈ support, weight address * amount Address incidence address := by
  induction incidence with
  | nil => simp [amount]
  | cons first rest prior =>
    have inside := covers first List.mem_cons_self
    have later := prior fun entry found => covers entry (List.mem_cons_of_mem _ found)
    have one : (∑ address ∈ support, weight address * (if first.1 = address then first.2 else 0)) =
        weight first.1 * first.2 := by
      rw [Finset.sum_eq_single_of_mem first.1 inside]
      · simp
      · intro other _ different
        simp only [if_neg (Ne.symm different), mul_zero]
    simp only [List.map_cons, List.sum_cons, later]
    change weight first.1 * first.2 + (∑ address ∈ support, weight address * amount Address rest address) =
      ∑ address ∈ support, weight address * ((if first.1 = address then first.2 else 0) + amount Address rest address)
    rw [← one]
    simp only [mul_add, Finset.sum_add_distrib]

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Cell" => Channel × Party × Good

def material (source : C) (script : Script) : List (Cell × ℚ) :=
  (Execution.inventory source script).flatMap fun item =>
    channels.flatMap fun channel =>
      (actualPart source.native.handlerFace.rootRead item.before item.request channel).map fun lot =>
        ((channel, lot.1.1, lot.1.2), lot.2)

def weightAt (reading : LinearReadout Party Good) (address : Cell) : ℚ :=
  reading.resourceWeight address.1 address.2.1 address.2.2

def nativeValue (source : C) (script : Script) (reading : LinearReadout Party Good) : ℚ :=
  value reading source.native.input (Evolving.Epoch.Source.originalState source.native) (Execution.programme source script)

theorem the_original_linear_cost_is_a_weighting_of_the_same_actual_inventory
    (source : C) (script : Script) (reading : LinearReadout Party Good) :
    nativeValue source script reading =
      ((material source script).map (fun lot => weightAt reading lot.1 * lot.2)).sum +
        reading.timeWeight * elapsed source script := by
  unfold nativeValue value
  rw [Execution.material_is_the_folded_actual_inventory, elapsed_is_original_clock_cost]
  unfold material
  rw [sum_through_flatMap]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro item _
  rw [sum_through_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro channel _
  simp only [weightedFlow, weightAt, List.map_map]
  rfl

theorem the_grouped_original_cost_retains_each_actual_material_address
    (source : C) (script : Script) (reading : LinearReadout Party Good)
    (support : Finset Cell) (covers : ∀ entry ∈ material source script, entry.1 ∈ support) :
    nativeValue source script reading =
      (∑ address ∈ support, weightAt reading address * amount Cell (material source script) address) +
        reading.timeWeight * elapsed source script := by
  rw [the_original_linear_cost_is_a_weighting_of_the_same_actual_inventory,
    regroup_material_weight _ _ _ covers]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Weights
