import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities

noncomputable section

private theorem native_drain_has_no_material_receipt (cut : C) :
    Execution.timedInventory cut (Execution.drain cut) = [] :=
  List.map_eq_nil_iff.mp ((Execution.timedInventory_is_the_original_inventory _ _).trans
    (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain cut).2.2.1)

private theorem preparation_has_no_material_receipt :
    Execution.timedInventory source (preparedScript source proposal) = [] := by
  change Execution.timedInventory source (Execution.drain source) = []
  exact native_drain_has_no_material_receipt source

theorem the_ten_original_items_keep_their_two_committing_clocks :
    Execution.timedInventory source (script source proposal) =
      (publicLaw.rawItems opening period).map (fun item => (item, (5 : ℚ))) ++
        (publicLaw.rawItems firstRaw period).map (fun item => (item, (6 : ℚ))) := by
  have migrationReady : ¬ Public.Inquiry.HasWork migration.native.frame migration.native.actual.actual :=
    preparation_is_ready source proposal
  have renewalReady : ¬ Public.Inquiry.HasWork renewal.native.frame renewal.native.actual.actual :=
    renewal_is_ready source proposal
  have first : Optimality.Programme.Epoch.materialItems migration = publicLaw.rawItems opening period := by
    unfold Optimality.Programme.Epoch.materialItems
    rw [if_neg migrationReady]
    exact the_front_physically_pays_the_original_word.2.2
  have second : Optimality.Programme.Epoch.materialItems renewal = publicLaw.rawItems firstRaw period := by
    unfold Optimality.Programme.Epoch.materialItems
    rw [if_neg renewalReady]
    exact the_renewal_physically_pays_the_same_word.2.2
  obtain ⟨_, firstClock, secondClock, _, _⟩ := the_same_original_root_pays_two_periods_at_clocks_five_and_six
  have lastClock : (renewed source proposal).raw.clock = 6 := secondClock
  unfold script
  rw [Execution.timedInventory_append, Execution.timedInventory_append, Execution.endAt_append,
    preparation_has_no_material_receipt, List.nil_append]
  change ((Optimality.Programme.Epoch.materialItems migration).map
      (fun item => (item, (migrated source proposal).raw.clock)) ++
      Execution.timedInventory (migrated source proposal) (Execution.drain (migrated source proposal))) ++
    ((Optimality.Programme.Epoch.materialItems renewal).map
      (fun item => (item, (renewed source proposal).raw.clock)) ++
      Execution.timedInventory (renewed source proposal) (Execution.drain (renewed source proposal))) = _
  rw [first, second, firstClock, lastClock, native_drain_has_no_material_receipt,
    native_drain_has_no_material_receipt, List.append_nil, List.append_nil]

theorem both_services_commit_at_distinct_original_positions :
    ∃ first second : ExecutionItem Bool Bool Bool Unit Unit,
      (Execution.timedInventory source (script source proposal))[4]? = some (first, 5) ∧
      (Execution.timedInventory source (script source proposal))[9]? = some (second, 6) ∧
      first.request = service ∧ second.request = service := by
  rw [the_ten_original_items_keep_their_two_committing_clocks]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
