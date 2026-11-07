import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Shared
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Shared.Consumers

open Exit.Grant.Cohort.Consumers
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

private abbrev shared := geometry afterSecond (Finset.univ : Finset Bool) (fun _ => task) both.exit

private theorem four_original_slots : shared.leftCarrier.card = 4 := by
  unfold shared geometry
  rw [Finset.card_sigma]
  have one : (Window.geometry afterSecond task both.exit).leftCarrier.card = 2 := by
    change (Finset.univ.filter (fun slot : Fin task.slots.length => (task.slots.get slot).goods ≠ [])).card = 2
    decide
  simp [one]

private theorem two_paid_positions : shared.rightCarrier.card = 2 := by
  change (Finset.univ : Finset (Fin (Execution.inventory afterSecond both.exit).length)).card = 2
  rw [Finset.card_univ, Fintype.card_fin, actual_inventory]
  rfl

/-- Two independent uses of the same demand specification each have a
complete candidate allocation. The native two debits cannot satisfy both. -/
theorem two_tasks_can_pass_alone_but_their_joint_original_deficit_is_positive :
    Window.FullyServed afterSecond task both.exit ∧
      2 ≤ maximumDeficit shared ∧
      Nonempty (Deficiency afterSecond (Finset.univ : Finset Bool) (fun _ => task) both.exit) ∧
      Recorded afterSecond both.exit := by
  have balance := actual_capacity_plus_the_largest_original_deficit_is_the_full_need shared
  rw [four_original_slots] at balance
  have upper := shared.maximumMatchingCapacity_le_right
  rw [two_paid_positions] at upper
  have needed : 2 ≤ maximumDeficit shared := by omega
  obtain ⟨account, result⟩ := actual_joint_service_has_a_paid_matching_or_an_exact_original_group
    afterSecond (Finset.univ : Finset Bool) (fun _ => task) both.exit
  refine ⟨both_original_exit_services_commit_in_the_installed_window, needed, ?_, account⟩
  rcases result with paid | issue
  · have full : shared.maximumMatchingCapacity = shared.leftCarrier.card :=
      (full_capacity_iff_there_is_a_complete_matching _).mpr paid
    rw [four_original_slots] at full
    omega
  · exact issue

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Shared.Consumers
