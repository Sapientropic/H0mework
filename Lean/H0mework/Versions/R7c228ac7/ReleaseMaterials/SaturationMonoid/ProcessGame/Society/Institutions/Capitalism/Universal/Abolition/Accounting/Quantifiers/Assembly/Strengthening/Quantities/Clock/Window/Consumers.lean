import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.CofinalClock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Consumers

open Abolition.Root Abolition.Root.Registered PublicFunction Execution
open Innovation.Contribution.Pricing.Consumers.Actual (lifeWord task)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
  (lifeSource lifePeriod firstPaidPeriod the_original_full_period_pays_life_and_finishes_its_native_work
    the_original_period_advances_one_actual_hour)

noncomputable section

def closesAtStart : PublicTaskSpec Bool Bool :=
  { task with deadline := lifeSource.raw.clock }

private def committed := next lifeSource (some (.execute lifeWord))

private theorem all_life_items_have_the_actual_commit_time :
    ∀ receipt ∈ timedInventory lifeSource firstPaidPeriod, receipt.2 = committed.raw.clock := by
  have empty := (the_first_exhausted_native_cut_is_the_original_paid_drain committed).2.2.1
  have timedEmpty : timedInventory committed (drain committed) = [] :=
    List.map_eq_nil_iff.mp ((timedInventory_is_the_original_inventory _ _).trans empty)
  intro receipt present
  change receipt ∈ (Optimality.Programme.Epoch.materialItems (query lifeSource (some (.execute lifeWord)))).map
    (fun item => (item, committed.raw.clock)) ++ timedInventory committed (drain committed) at present
  rw [timedEmpty, List.append_nil] at present
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp present
  rfl

theorem a_real_material_period_can_commit_after_its_original_service_cutoff :
    Settled lifeSource firstPaidPeriod ∧
      (∀ ordinal, closesAtStart.deadline < (timedAt lifeSource firstPaidPeriod ordinal).2) ∧
      Nonempty (Shortage lifeSource closesAtStart firstPaidPeriod) := by
  have one := the_original_period_advances_one_actual_hour
  change committed.raw.clock - lifeSource.raw.clock = 1 at one
  have overdue (ordinal : Fin (inventory lifeSource firstPaidPeriod).length) :
      closesAtStart.deadline < (timedAt lifeSource firstPaidPeriod ordinal).2 := by
    have present : timedAt lifeSource firstPaidPeriod ordinal ∈ timedInventory lifeSource firstPaidPeriod := by
      unfold timedAt
      exact List.get_mem _ _
    rw [all_life_items_have_the_actual_commit_time _ present]
    change lifeSource.raw.clock < committed.raw.clock
    linarith
  exact ⟨the_original_full_period_pays_life_and_finishes_its_native_work.1, overdue,
    ⟨material_committed_after_the_deadline_leaves_the_original_service_unpaid _ _ _ overdue⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Consumers
