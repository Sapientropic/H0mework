import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Shortage
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Domain

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution
open Quantities.Demand (Deficit delivered)
open Conflict.Consumers.Evolving (C)

noncomputable section

abbrev Cadence := Nat → C → Original.Word

private theorem initial_stage (source : C) (schedule : Cadence) :
    stageAt source schedule 0 = source := by
  rw [stageAt, stageScript]
  rfl

variable (prior : Original.Word) (policy : Cadence)

local notation "origin" => endAt Original.cut prior
local notation "stage" => stageAt origin policy
local notation "body" => stageBody origin policy

open Quantities.Recovery.PersonTime.Cohort.Conservation (stock) in
private theorem two_original_windows_cannot_both_pay
    (cut : C) (firstWord secondWord : Original.Word)
    (law : cut.native.input = Conflict.Consumers.Evolving.compact)
    (stocked : ∀ person good, 0 ≤ cut.raw.stock person good) (opening : stock cut.raw true ≤ 2)
    (first : ∀ person : Bool, 1 ≤ delivered cut firstWord person .necessity true)
    (second : ∀ person : Bool, 1 ≤ delivered (endAt cut firstWord) secondWord person .necessity true) : False := by
  let windows := [firstWord, secondWord]
  have supply := Material.food_spent_in_any_original_schedule_has_the_inventory_bound cut law windows
  have left := Material.food_stock_nonnegative cut windows.flatten stocked
  have paid : Material.PaidFoodWindows cut windows := ⟨first, second, trivial⟩
  have costs := Material.actual_living_windows_require_two_food_each cut windows paid
  change (2 : ℚ) * 2 ≤ Material.spentInFoodWindows cut windows at costs
  linarith only [supply, left, opening, costs]

private def missing (n : Nat) (person : Bool)
    (shortage : delivered (stage n) (body n) person .necessity true < 1) :
    Deficit (stage n) (body n) where
  cell := (person, .necessity, true, 1)
  original := by
    rw [stageAt, ← endAt_append]
    exact Material.each_original_food_cell_survives_every_original_continuation _ person
  shortage := shortage

/-- Read the first two native stages of an arbitrary cadence at any
actual later cut. The first failing food cell is still a native row. -/
def firstOriginalFoodFailure :
    Deficit (stage 0) (body 0) ⊕
      { _deficit : Deficit (stage 1) (body 1) //
        ∀ person : Bool, 1 ≤ delivered (stage 0) (body 0) person .necessity true } := by
  let checked (n : Nat) := Capitalism.Universal.Abolition.Material.inspectList
    (fun person : Bool => (1 : ℚ) ≤ delivered (stage n) (body n) person .necessity true) [false, true]
  have listed (person : Bool) : person ∈ [false, true] := by cases person <;> decide
  cases checked 0 with
  | failure person _ denied =>
    exact .inl (missing prior policy 0 person (lt_of_not_ge denied))
  | clear first =>
    have paid := fun person => first person (listed person)
    cases checked 1 with
    | failure person _ denied =>
      exact .inr ⟨missing prior policy 1 person (lt_of_not_ge denied), paid⟩
    | clear second =>
      have start := initial_stage origin policy
      have moved : stage 1 = endAt origin (body 0) :=
        (next_stage_is_the_literal_original_next origin policy 0).trans (congrArg (fun cut => endAt cut (body 0)) start)
      have nextPaid := fun person => second person (listed person)
      rw [start] at paid
      rw [moved] at nextPaid
      exact (two_original_windows_cannot_both_pay origin (body 0) (body 1)
        ((endAt_input Original.cut prior).trans Original.same_source)
        (Material.original_stock_stays_nonnegative Original.cut prior Material.the_original_stocks_are_nonnegative)
        (Material.every_original_continuation_has_at_most_two_food prior) paid nextPaid).elim

theorem no_paid_cofinal_cadence_can_start_at_an_original_later_cut
    {Issue : Nat → C → Original.Word → Type}
    (inspect : (n : Nat) → (cut : C) → (word : Original.Word) → Option (Issue n cut word)) :
    ¬ Quantities.Bounds.Cofinal.Paid origin policy Issue inspect := by
  intro claimed
  cases firstOriginalFoodFailure prior policy with
  | inl failed =>
    exact (not_le_of_gt failed.shortage) ((claimed.allStages 0).paid failed.cell failed.original)
  | inr second =>
    let failed := second.val
    exact (not_le_of_gt failed.shortage) ((claimed.allStages 1).paid failed.cell failed.original)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
