import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Matching.Completion

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window

open Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

theorem all_in_window_services_are_paid_iff_every_group_has_enough_actual_debits
    (source : C) (task : PublicTaskSpec Party Good) (script : Script) :
    FullyServed source task script ↔
      ∀ group ⊆ (geometry source task script).leftCarrier,
        group.card ≤ (neighbours (geometry source task script) group).card := by
  unfold FullyServed
  rw [← full_capacity_iff_there_is_a_complete_matching,
    full_payment_iff_every_original_group_has_enough_neighbours]

/-- The maximum number of simultaneously unserved original obligations
has a group that witnesses its exact shortfall on the original receipts. -/
theorem Shortage.exact_original_group {source : C} {task : PublicTaskSpec Party Good} {script : Script}
    (issue : Shortage source task script) :
    let actual := geometry source task script
    ∃ group ⊆ actual.leftCarrier,
      (neighbours actual group).card < group.card ∧
      actual.maximumMatchingCapacity + deficit actual group = actual.leftCarrier.card ∧
      Recorded source script := by
  let actual := geometry source task script
  obtain ⟨group, sourceGroup, largest⟩ := the_largest_deficit_is_attained_at_an_original_group actual
  have exactCapacity := actual_capacity_plus_the_largest_original_deficit_is_the_full_need actual
  rw [← largest] at exactCapacity
  have short : actual.maximumMatchingCapacity < actual.leftCarrier.card := issue.short
  refine ⟨group, sourceGroup, ?_, exactCapacity, record source script⟩
  change (neighbours actual group).card < group.card
  unfold deficit at exactCapacity
  omega

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window
