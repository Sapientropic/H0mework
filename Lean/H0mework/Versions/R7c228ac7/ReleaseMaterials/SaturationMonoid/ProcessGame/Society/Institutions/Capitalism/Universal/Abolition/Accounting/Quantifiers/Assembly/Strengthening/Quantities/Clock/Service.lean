import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Matching

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock

open Source.Program Abolition.Root Abolition.Root.Registered
open PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Whole-bundle obligations use distinct actual debit ordinals. An empty
bundle never occupies a service slot or an execution item. -/
def geometry (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    CanonicalBipartiteFeasibility (Fin task.slots.length) (Fin (Execution.inventory source script).length) :=
  geometryOf (Physical.Public.interpreter source.native.input) task (Execution.inventory source script)

def FullyServed (source : C) (task : PublicTaskSpec Party Good) (script : Script) : Prop :=
  let live := geometry source task script
  ∃ matching ∈ live.matchings, matching.card = live.leftCarrier.card

theorem fully_served_iff_the_original_capacity_covers_every_slot
    (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    FullyServed source task script ↔
      (geometry source task script).maximumMatchingCapacity = (geometry source task script).leftCarrier.card :=
  (full_capacity_iff_there_is_a_complete_matching (geometry source task script)).symm

structure ServiceShortage (source : C) (task : PublicTaskSpec Party Good) (script : Script) : Type where
  short : (geometry source task script).maximumMatchingCapacity < (geometry source task script).leftCarrier.card

def inspectService (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    Option (ServiceShortage source task script) :=
  if short : (geometry source task script).maximumMatchingCapacity < (geometry source task script).leftCarrier.card
  then some ⟨short⟩ else none

theorem service_pass_iff_fully_paid (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    inspectService source task script = none ↔ FullyServed source task script := by
  rw [fully_served_iff_the_original_capacity_covers_every_slot]
  have bound := (geometry source task script).maximumMatchingCapacity_le_left
  unfold inspectService
  split
  · rename_i short
    simp only [reduceCtorEq, false_iff]
    exact short.ne
  · rename_i full
    exact ⟨fun _ => le_antisymm bound (le_of_not_gt full), fun _ => rfl⟩

theorem ServiceShortage.unpaid_original_slot {source : C} {task : PublicTaskSpec Party Good} {script : Script}
    (shortage : ServiceShortage source task script)
    (matching : Finset (Fin task.slots.length × Fin (Execution.inventory source script).length))
    (listed : matching ∈ (geometry source task script).matchings) :
    ∃ slot ∈ (geometry source task script).leftCarrier, ∀ edge ∈ matching, edge.1 ≠ slot :=
  a_short_matching_leaves_an_original_slot _ shortage.short matching listed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock
