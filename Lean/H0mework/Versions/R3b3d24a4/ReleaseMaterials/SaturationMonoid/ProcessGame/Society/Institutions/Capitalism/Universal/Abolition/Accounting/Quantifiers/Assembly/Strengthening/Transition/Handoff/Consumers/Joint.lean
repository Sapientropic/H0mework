import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual.Service
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Frontier

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint

open Source.Program Abolition.Root Abolition.Root.Registered Quantities
open Actual

noncomputable section

def budget (key : Bool × Bool) : ℚ := if key = (true, false) then 1 else 0
def absentBudget (_key : Bool × Bool) : ℚ := 0

private theorem held_is_the_one_old_service :
    Allocation.heldRows ordered task held = [row false] := by decide +kernel

private theorem each_original_position_pays_only_its_chosen_task :
    Reserve.assignedAt (Due.Settlement.paidAt assigned) =
      fun line position => if position = place line.1.1.val then 1 else 0 := by
  funext line position
  unfold Reserve.assignedAt
  split
  · rename_i inside
    unfold Due.Settlement.paidAt assigned
    have sameUnit : Due.Settlement.originalUnit line = (lot line.1.1.val).2 := by
      apply Subtype.ext
      change line.2.val = (row line.1.1.val).2.val
      exact congrArg (fun need : Row => need.2.val) (a_row_is_its_original_task line)
    have same : ((⟨position, inside⟩, Due.Settlement.originalUnit line) : Lot) = lot line.1.1.val ↔
        position = place line.1.1.val := by
      constructor
      · exact fun hit => congrArg (fun receipt : Lot => receipt.1.val) hit
      · exact fun hit => Prod.ext (Fin.ext hit) sameUnit
    simp only [same]
  · rename_i outside
    have different : position ≠ place line.1.1.val := by
      intro exactPlace
      apply outside
      rw [exactPlace, original_inventory_length]
      cases line.1.1.val <;> decide
    simp [different]

theorem the_full_original_stock_budget_is_tight_at_each_address (key : Bool × Bool) :
    requiredOpening source ordered task reserved held proposal assigned key = budget key := by
  change Reserve.openingNeed (Allocation.heldRows ordered task held) Due.Settlement.address key
      (Reserve.readSteps source.native.handlerFace.rootRead (Reserve.assignedAt (Due.Settlement.paidAt assigned))
        (Execution.timedInventory source word) 0) (fun line => net.need line) = budget key
  rw [held_is_the_one_old_service, original_handler, each_original_position_pays_only_its_chosen_task,
    the_ten_original_items_keep_their_two_committing_clocks, funext needed]
  obtain ⟨person, good⟩ := key
  cases person <;> cases good <;> decide +kernel

theorem the_two_services_are_funded_at_the_tight_opening :
    Fits source ordered task reserved held budget proposal assigned := by
  refine ⟨assignment_covers_the_two_original_services _, ?_⟩
  intro key _
  have stock : budget key ≤ Allocation.opening source budget key := by
    unfold Allocation.opening
    rw [source_reads_the_paid_opening]
    obtain ⟨person, good⟩ := key
    cases person <;> cases good <;> decide +kernel
  have opening : requiredOpening source ordered task reserved held proposal assigned key ≤
      Allocation.opening source budget key :=
    (the_full_original_stock_budget_is_tight_at_each_address key).symm ▸ stock
  exact (Reserve.openingNeed_fits_iff _ _ _ _ _ _).mp opening

theorem the_same_original_handoff_is_admitted_at_clock_six :
    Admitted source ordered task reserved held budget ((6 : ℚ) : WithTop ℚ) proposal := by
  refine ⟨(inspection_is_complete _ _ _ _ _ _ _).mpr
    ⟨Actual.paid, original_demands_are_nonnegative, the_original_handoff_has_paid_its_native_settlement,
      assigned, the_two_services_are_funded_at_the_tight_opening⟩, ?_⟩
  rw [the_same_original_root_pays_two_periods_at_clocks_five_and_six.2.2.1]

theorem the_same_paid_programme_is_refused_at_clock_five :
    ∃ late, refusal source ordered task reserved held budget ((5 : ℚ) : WithTop ℚ) proposal = some (.late late) := by
  obtain ⟨paid, result⟩ := the_same_original_handoff_is_admitted_at_clock_six.1
  have late : ((5 : ℚ) : WithTop ℚ) < (handoffTime source proposal : WithTop ℚ) := by
    apply WithTop.coe_lt_coe.mpr
    rw [the_same_original_root_pays_two_periods_at_clocks_five_and_six.2.2.1]
    norm_num
  refine ⟨late, ?_⟩
  unfold refusal
  rw [result, dif_pos late]

private theorem opening_pays_outstanding_stock {Item : Type}
    (rows : List Row) (address : Row → Bool × Bool) (key : Bool × Bool)
    (steps : List (Reserve.Step Row (Bool × Bool) Item)) (need : Row → ℚ) (stock : ℚ)
    (protection : Reserve.Protects rows address key steps need stock) :
    Reserve.held rows address need key ≤ stock := by
  cases steps with
  | nil => exact protection.2
  | cons _ _ => exact protection.2.1

theorem the_old_service_owes_one_at_its_original_address :
    Reserve.held (Allocation.heldRows ordered task held) Due.Settlement.address
      (fun line => net.need line) (true, false) = 1 := by
  rw [held_is_the_one_old_service, funext needed]
  decide +kernel

theorem no_allocation_can_lower_the_original_one_unit_opening
    (allocation : Handoff.Assignment source ordered task proposal) :
    (1 : ℚ) ≤ requiredOpening source ordered task reserved held proposal allocation (true, false) := by
  let profile := Allocation.view source word ordered task (reserved word) allocation
  let steps := Reserve.originalSteps source word (Reserve.assignedAt profile.paid)
  have holds := Reserve.openingNeed_attains (Allocation.heldRows ordered task held) profile.address
    (true, false) steps profile.required
  have lower := opening_pays_outstanding_stock _ _ _ _ _ _ holds
  change Reserve.held (Allocation.heldRows ordered task held) Due.Settlement.address
    (fun line => net.need line) (true, false) ≤
      requiredOpening source ordered task reserved held proposal allocation (true, false) at lower
  rw [the_old_service_owes_one_at_its_original_address] at lower
  exact lower

theorem one_missing_unit_blocks_every_allocation_to_the_same_old_row :
    ¬ ∃ allocation, Fits source ordered task reserved held absentBudget proposal allocation := by
  rintro ⟨allocation, fits⟩
  have watched : (true, false) ∈ Allocation.watched source word ordered task :=
    Due.Settlement.every_due_address_is_watched source word ordered task (row false)
  have upper : requiredOpening source ordered task reserved held proposal allocation (true, false) ≤
      Allocation.opening source absentBudget (true, false) :=
    (Reserve.openingNeed_fits_iff _ _ _ _ _ _).mpr (fits.2 (true, false) watched)
  have lower := (no_allocation_can_lower_the_original_one_unit_opening allocation).trans upper
  have noStock : Allocation.opening source absentBudget (true, false) = 0 := by
    unfold Allocation.opening
    rw [source_reads_the_paid_opening]
    decide +kernel
  rw [noStock] at lower
  norm_num at lower

theorem the_missing_old_reserve_returns_the_original_allocation_refusal :
    ∃ conflict, inspect source ordered task reserved held absentBudget proposal = .inr (.allocation conflict) ∧
      0 < conflict.minimumSlack.amount := by
  have route : ∃ checked, inspectPath source proposal = .inl ⟨checked⟩ := by
    cases found : inspectPath source proposal with
    | inl checked => exact ⟨checked.down, rfl⟩
    | inr issue => exact (issue.refutes Actual.paid).elim
  have checked : ∃ feasible, Quantities.decideAt source word = .feasible feasible := by
    cases found : Quantities.decideAt source word with
    | feasible paid => exact ⟨paid, rfl⟩
    | blocked issue => exact (issue.refutes the_original_handoff_has_paid_its_native_settlement.toFeasible).elim
  obtain ⟨routeProof, originalRoute⟩ := route
  obtain ⟨nativeProof, originalNative⟩ := checked
  unfold inspect
  rw [originalRoute]
  dsimp only
  rw [dif_pos original_demands_are_nonnegative, originalNative]
  cases solved : Allocation.decideAllocation source word ordered task (reserved word) held absentBudget with
  | paid allocation fits => exact (one_missing_unit_blocks_every_allocation_to_the_same_old_row ⟨allocation, fits⟩).elim
  | blocked impossible =>
    let conflict := Allocation.Diagnostics.jointConflictOfInfeasible source word ordered task
      (reserved word) held absentBudget impossible
    exact ⟨conflict, rfl, conflict.minimumSlack.positive⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint
