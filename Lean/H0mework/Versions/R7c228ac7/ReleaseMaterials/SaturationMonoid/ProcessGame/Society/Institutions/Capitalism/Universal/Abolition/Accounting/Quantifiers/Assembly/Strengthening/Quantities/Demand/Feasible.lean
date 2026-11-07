import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Responsibility
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities

open Source.Program
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def Pending (target : C) : Prop :=
  Public.Inquiry.HasWork target.native.frame target.native.actual.actual

instance (target : C) : Decidable (Pending target) :=
  inferInstanceAs (Decidable (Public.Inquiry.HasWork target.native.frame target.native.actual.actual))

abbrev nextNativeItem (target : C) :=
  Public.Accounting.item? target.native.input target.native.depth target.native.count
    target.native.prefixLimit target.native.renewalLimit target.native.oldPast target.native.start
    target.native.actual.actual

inductive NativeObstruction (target : C)
  | body (unpaid : target.native.actual.actual.bodyPaid = false)
  | item (original : Epoch.Finance.ActualItem target.native.input target.native.depth target.native.count)
      (pending : nextNativeItem target = some original)

theorem NativeObstruction.pending {target : C} (issue : NativeObstruction target) : Pending target := by
  cases issue with
  | body unpaid => exact Or.inl unpaid
  | item original pending =>
      apply Or.inr
      change (nextNativeItem target).isSome = true
      simp only [pending, Option.isSome_some]

def inspectNative (target : C) : Option (NativeObstruction target) :=
  if unpaid : target.native.actual.actual.bodyPaid = false then some (.body unpaid)
  else match observed : nextNativeItem target with
    | some original => some (.item original observed)
    | none => none

theorem native_is_finished_without_a_pending_item (target : C)
    (noneFound : inspectNative target = none) : ¬ Pending target := by
  unfold inspectNative at noneFound
  split at noneFound
  · contradiction
  · rename_i body
    split at noneFound
    · contradiction
    · rename_i item
      intro work
      rcases work with unpaid | more
      · exact body unpaid
      · change (nextNativeItem target).isSome = true at more
        simp only [item, Option.isSome_none, Bool.false_eq_true] at more

/-- All source-admitted scripts execute under the original stock and
permission checks. Completion also pays the original needs and finishes
the native accounting work produced by the selected script. -/
structure Feasible (source : C) (script : Script) : Prop where
  paid : Demand.Covers source script
  finished : ¬ Pending (Execution.endAt source script)

inductive Obstruction (source : C) (script : Script)
  | material (issue : Demand.Deficit source script)
  | native (issue : NativeObstruction (Execution.endAt source script))

theorem Obstruction.refutes {source : C} {script : Script} (issue : Obstruction source script) :
    ¬ Feasible source script := by
  intro paid
  cases issue with
  | material deficit => exact deficit.refutes paid.paid
  | native work => exact paid.finished work.pending

inductive Decision (source : C) (script : Script)
  | feasible (paid : Feasible source script)
  | blocked (issue : Obstruction source script)

def decideAt (source : C) (script : Script) : Decision source script :=
  match Demand.inspect source script with
  | .deficit issue => .blocked (.material issue)
  | .covered paid =>
      match observed : inspectNative (Execution.endAt source script) with
      | some issue => .blocked (.native issue)
      | none => .feasible ⟨paid, native_is_finished_without_a_pending_item _ observed⟩

theorem infeasible_iff_original_obstruction (source : C) (script : Script) :
    ¬ Feasible source script ↔ Nonempty (Obstruction source script) := by
  constructor
  · intro failed
    cases decideAt source script with
    | feasible paid => exact (failed paid).elim
    | blocked issue => exact ⟨issue⟩
  · rintro ⟨issue⟩
    exact issue.refutes

theorem all_capacity_is_paid_from_the_original_stock_and_actual_credits
    (source : C) (script : Script) (bearer : Party) (good : Good) :
    (Execution.endAt source script).raw.stock bearer good +
      source.native.handlerFace.rootRead.totalDebit (Execution.inventory source script) bearer good =
    source.raw.stock bearer good +
      source.native.handlerFace.rootRead.totalCredit (Execution.inventory source script) bearer good := by
  have balance := Optimality.Programme.the_entire_programme_has_its_original_material_balance
    source.native.input (Evolving.Epoch.Source.originalState source.native)
    (Execution.programme source script) bearer good
  rw [Execution.physical_is_the_folded_actual_end, Execution.material_is_the_folded_actual_inventory] at balance
  exact balance

theorem paid_needs_have_their_actual_bearer_and_material (source : C) (script : Script)
    (completed : Feasible source script) (cell : Party × Use × Good × ℚ)
    (original : cell ∈ Demand.requirements source) :
    cell.2.2.2 ≤ ((Execution.inventory source script).map fun item => flowAt
      (Optimality.Cost.actualPart source.native.handlerFace.rootRead
        item.before item.request (.use cell.2.1)) cell.1 cell.2.2.1).sum := by
  rw [← Demand.delivered_is_from_original_inventory]
  exact completed.paid cell original

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities
