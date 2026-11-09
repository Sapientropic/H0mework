import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Original
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Positivity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Root
open Conflict.Consumers.Evolving
open Quantities.Execution
open Quantities.Recovery.PersonTime.Cohort.Conservation
open scoped BigOperators

noncomputable section

local notation "Law" => RawLaw Bool Bool Bool Unit Unit
local notation "Raw" => RawCurrent Bool Bool Unit Unit
local notation "Item" => ExecutionItem Bool Bool Bool Unit Unit
local notation "Script" => Reparation.Actual.Script Bool Bool Bool Unit Unit

private theorem bool_stock (raw : Raw) :
    stock raw true = raw.stock false true + raw.stock true true := by
  simp [stock, Fintype.univ_bool, add_comm]

private def foodUse (law : Law) (raw : Raw) (request : R) (bearer : Bool) : ℚ :=
  flowAt (Optimality.Cost.actualPart law raw request (.use .necessity)) bearer true

private def livingSpent (law : Law) (items : List Item) : ℚ :=
  (items.map fun item => foodUse law item.before item.request false + foodUse law item.before item.request true).sum

private theorem living_spent_append (law : Law) (first later : List Item) :
    livingSpent law (first ++ later) = livingSpent law first + livingSpent law later := by
  simp [livingSpent, List.sum_append]

private theorem physical_food_step (law : Law) (raw : Raw) (request : R)
    (noOutput : ∀ tech bearer, amount Bool (law.technique tech bearer).outputs true = 0) :
    stock (law.step raw request) true + foodUse law raw request false +
      foodUse law raw request true ≤ stock raw true := by
  by_cases valid : law.Valid raw request
  · by_cases paid : ∃ bearer goods, request.operation = .use bearer goods .necessity
    · obtain ⟨bearer, goods, form⟩ := paid
      have debit (person : Bool) : foodUse law raw request person =
          flowAt (law.actualDebit raw request) person true := by
        simp [foodUse, Optimality.Cost.actualPart, valid, Optimality.Cost.part, form, RawLaw.actualDebit]
      have credit (person : Bool) : flowAt (law.actualCredit raw request) person true = 0 := by
        simp [RawLaw.actualCredit, valid, RawLaw.credit, form, flowAt, amount]
      have left := law.material_step_balance raw request false true
      have right := law.material_step_balance raw request true true
      rw [credit] at left right
      rw [bool_stock, bool_stock, debit, debit]
      linarith
    · have noUse (person : Bool) : foodUse law raw request person = 0 := by
        cases form : request.operation with
        | use bearer goods purpose =>
          cases purpose <;> simp [foodUse, Optimality.Cost.actualPart, valid, Optimality.Cost.part, form,
            flowAt, amount]
          exact (paid ⟨bearer, goods, form⟩).elim
        | _ => simp [foodUse, Optimality.Cost.actualPart, valid, Optimality.Cost.part, form,
            flowAt, amount]
      simpa only [noUse, add_zero] using
        stock_cannot_increase_in_one_instruction_without_output law raw request true noOutput
  · have noUse (person : Bool) : foodUse law raw request person = 0 := by
      simp [foodUse, Optimality.Cost.actualPart, valid, flowAt, amount]
    simpa only [noUse, add_zero] using
      stock_cannot_increase_in_one_instruction_without_output law raw request true noOutput

private theorem physical_food_word (law : Law) (raw : Raw) (word : W) (index : Nat)
    (noOutput : ∀ tech bearer, amount Bool (law.technique tech bearer).outputs true = 0) :
    let reached := law.execute raw index word
    stock reached.final true + livingSpent law reached.items ≤ stock raw true := by
  induction word generalizing raw index with
  | nil => simp [RawLaw.execute, livingSpent]
  | cons request later ih =>
      have head := physical_food_step law raw request noOutput
      have tail := ih (law.step raw request) (index + 1)
      simp only [RawLaw.execute, livingSpent, List.map_cons, List.sum_cons]
      dsimp [livingSpent] at tail
      linarith

private theorem programme_food
    (input : ProgrammeSource.Input Bool Bool Bool Unit Unit)
    (before : Capitalism.Universal.Abolition.Root.Actual.Current (Party := Bool)
      (Good := Bool) (Port := Bool) (Technology := Unit) (Instrument := Unit))
    (code : List (Compile.RawInput Bool Bool Bool Unit Unit))
    (noOutput : ∀ tech bearer, amount Bool ((Physical.Public.interpreter input).technique tech bearer).outputs true = 0) :
    stock (Optimality.Programme.run input before code).raw true +
      livingSpent (Physical.Public.interpreter input) (Optimality.Programme.items input before code) ≤
        stock before.raw true := by
  induction code generalizing before with
  | nil => simp [Optimality.Programme.run, Optimality.Programme.items, livingSpent]
  | cons proposal later ih =>
      let selected := Physical.Public.compile input before proposal
      have first : stock selected.next.raw true +
          livingSpent (Physical.Public.interpreter input) selected.execution.items ≤
            stock before.raw true := by
        unfold selected
        cases Physical.Public.compile input before proposal with
        | accepted word chosen checked =>
          cases proposal <;> exact physical_food_word _ before.raw word 0 noOutput
        | refused => simp [Physical.Public.ResultAt.next, Physical.Public.ResultAt.execution, livingSpent]
        | metadata => simp [Physical.Public.ResultAt.next, Physical.Public.ResultAt.execution, livingSpent]
      have rest := ih selected.next
      simp only [Optimality.Programme.run, Optimality.Programme.items, living_spent_append]
      change stock (Optimality.Programme.run input selected.next later).raw true +
        (livingSpent _ selected.execution.items + livingSpent _ (Optimality.Programme.items input selected.next later)) ≤ _
      linarith

private theorem living_spent_is_the_two_original_uses (law : Law) (items : List Item) :
    livingSpent law items =
      (items.map fun item => foodUse law item.before item.request false).sum +
      (items.map fun item => foodUse law item.before item.request true).sum := by
  induction items with
  | nil => simp [livingSpent]
  | cons item later ih =>
    simp only [livingSpent, List.map_cons, List.sum_cons] at ih ⊢
    linarith

theorem food_is_consumed_in_the_original_ledger (cut : C)
    (same : cut.native.input = compact) (suffix : Script) :
    stock (endAt cut suffix).raw true +
      Quantities.Demand.delivered cut suffix false .necessity true +
      Quantities.Demand.delivered cut suffix true .necessity true ≤ stock cut.raw true := by
  have bound := programme_food cut.native.input (Evolving.Epoch.Source.originalState cut.native)
    (programme cut suffix) (by rw [same]; exact no_food_output)
  rw [physical_is_the_folded_actual_end, material_is_the_folded_actual_inventory,
    living_spent_is_the_two_original_uses] at bound
  rw [Quantities.Demand.delivered_is_from_original_inventory,
    Quantities.Demand.delivered_is_from_original_inventory]
  change stock (endAt cut suffix).raw true +
    ((inventory cut suffix).map fun item => foodUse (Physical.Public.interpreter cut.native.input) item.before item.request false).sum +
    ((inventory cut suffix).map fun item => foodUse (Physical.Public.interpreter cut.native.input) item.before item.request true).sum ≤ _
  change stock (endAt cut suffix).raw true + (_ + _) ≤ stock cut.raw true at bound
  simpa only [add_assoc] using bound

private theorem nonnegative_after_word (law : Law) (raw : Raw) (word : W) (index : Nat)
    (stocked : ∀ bearer good, 0 ≤ raw.stock bearer good) :
    ∀ bearer good, 0 ≤ (law.execute raw index word).final.stock bearer good := by
  induction word generalizing raw index with
  | nil => exact stocked
  | cons request later ih =>
    exact ih (law.step raw request) (index + 1) (law.step_stock_nonnegative raw request stocked)

private theorem nonnegative_after_programme
    (input : ProgrammeSource.Input Bool Bool Bool Unit Unit)
    (before : Capitalism.Universal.Abolition.Root.Actual.Current (Party := Bool)
      (Good := Bool) (Port := Bool) (Technology := Unit) (Instrument := Unit))
    (code : List (Compile.RawInput Bool Bool Bool Unit Unit))
    (stocked : ∀ bearer good, 0 ≤ before.raw.stock bearer good) :
    ∀ bearer good, 0 ≤ (Optimality.Programme.run input before code).raw.stock bearer good := by
  induction code generalizing before with
  | nil => exact stocked
  | cons proposal later ih =>
    let selected := Physical.Public.compile input before proposal
    have first : ∀ bearer good, 0 ≤ selected.next.raw.stock bearer good := by
      unfold selected
      cases Physical.Public.compile input before proposal with
      | accepted word chosen checked =>
        cases proposal <;> exact nonnegative_after_word _ before.raw word 0 stocked
      | refused => exact stocked
      | metadata => exact stocked
    exact ih selected.next first

theorem original_stock_stays_nonnegative (cut : C) (suffix : Script)
    (stocked : ∀ bearer good, 0 ≤ cut.raw.stock bearer good) :
    ∀ bearer good, 0 ≤ (endAt cut suffix).raw.stock bearer good := by
  have paid := nonnegative_after_programme cut.native.input (Evolving.Epoch.Source.originalState cut.native)
    (programme cut suffix) stocked
  rw [physical_is_the_folded_actual_end] at paid
  exact paid

theorem food_stock_nonnegative (cut : C) (suffix : Script)
    (stocked : ∀ bearer good, 0 ≤ cut.raw.stock bearer good) :
    0 ≤ stock (endAt cut suffix).raw true := by
  rw [bool_stock]
  exact add_nonneg (original_stock_stays_nonnegative cut suffix stocked false true)
    (original_stock_stays_nonnegative cut suffix stocked true true)

theorem original_food_delivery_nonnegative (cut : C) (suffix : Script) (bearer : Bool) :
    0 ≤ Quantities.Demand.delivered cut suffix bearer .necessity true :=
  Optimality.Cost.all_programmes_have_nonnegative_real_resource_costs _ _ _ _ _ _

#print axioms food_is_consumed_in_the_original_ledger

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
