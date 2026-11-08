import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Run
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Renewal
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Preservation
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.CarryJoin.Allocation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program PublicFunction Abolition.Root Abolition.Root.Registered Quantities Actual Handoff.Continuation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Joint
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

noncomputable section

abbrev tailWord := renewalSuffix start
abbrev wholeWord := word ++ tailWord
abbrev WholeLot := Due.Service.Supply source wholeWord ordered.toFinset task
abbrev NewLot := Due.Service.Supply start tailWord ordered.toFinset task

private theorem fullRow (line : Row) : Network.rowTotal assigned line = net.need line :=
  (assignment_covers_the_two_original_services (fun _ => true)).2 line rfl

private def oldCertificate : Network.Certificate net := by
  have original := (assignment_covers_the_two_original_services (fun _ => true)).1
  have exactTotal := (net.full_quantity_iff_total_is_exact original).mp ⟨original, fullRow⟩
  refine ⟨assigned, ∅, original, ?_⟩
  simpa [Network.cut, Network.gap, Network.demandOf, Network.supplyOf, Network.neighbours] using exactTotal

private def joined : Row → WholeLot → ℚ :=
  Due.Service.joinedAllocation (future := tailWord) oldCertificate (fun _ _ => 0)

private abbrev wholeLot (id : Bool) : WholeLot :=
  priorSupply source word tailWord ordered task (lot id)

private theorem keepsPrior : Keeps source word tailWord ordered task assigned joined := by
  intro line oldLot
  let split := Due.Service.carriedSupply source word tailWord ordered.toFinset task
  change Sum.elim (assigned line) (fun _ : NewLot => 0) (split.symm (split (.inl oldLot))) = assigned line oldLot
  rw [Equiv.symm_apply_apply]
  rfl

private theorem joined_exact (line : Row) (item : WholeLot) :
    joined line item = if item = wholeLot line.1.1.val then 1 else 0 := by
  let split := Due.Service.carriedSupply source word tailWord ordered.toFinset task
  have read : wholeLot line.1.1.val = split (.inl (lot line.1.1.val)) := rfl
  obtain ⟨old | new, rfl⟩ := split.surjective item
  · rw [read]
    change (Sum.elim (assigned line) (fun _ : NewLot => 0) (split.symm (split (.inl old)))) =
      if split (.inl old) = split (.inl (lot line.1.1.val)) then 1 else 0
    simp only [Equiv.symm_apply_apply, split.injective.eq_iff, Sum.inl.injEq]
    rfl
  · rw [read]
    have distinct : split (.inr new) ≠ split (.inl (lot line.1.1.val)) := fun same => by
      cases split.injective same
    change Sum.elim (assigned line) (fun _ : NewLot => 0) (split.symm (split (.inr new))) =
      if split (.inr new) = split (.inl (lot line.1.1.val)) then 1 else 0
    rw [Equiv.symm_apply_apply, if_neg distinct]
    rfl

private abbrev booked := reservations source word tailWord (reserved word) ∅

private theorem coversJoined :
    Allocation.Covers (Due.Service.network source wholeWord ordered.toFinset task booked)
      (Allocation.due source wholeWord ordered task) joined := by
  have fresh : (Due.Service.carryNetwork oldCertificate tailWord ∅).Admissible (fun _ _ => 0) := by
    refine ⟨fun _ _ => ⟨le_rfl, fun _ => rfl⟩, ?_, ?_⟩
    · intro line
      simp only [Network.rowTotal, Finset.sum_const_zero]
      exact (Due.Service.carryNetwork oldCertificate tailWord ∅).need_nonnegative line
    · intro item
      simp only [Network.columnTotal, Finset.sum_const_zero]
      exact (Due.Service.carryNetwork oldCertificate tailWord ∅).capacity_nonnegative item
  refine ⟨?_, fun line _ => ?_⟩
  · simpa [reservations, joined, wholeWord] using
      Due.Service.joined_original_allocations_are_conservative oldCertificate fresh
  · change Network.rowTotal joined line = net.need line
    rw [joined, Due.Service.the_joined_row_is_the_sum_of_its_old_and_new_payments]
    change Network.rowTotal assigned line + (∑ _ : NewLot, (0 : ℚ)) = net.need line
    rw [Finset.sum_const_zero, add_zero, fullRow]

private theorem paidPosition :
    Reserve.assignedAt (Due.Settlement.paidAt joined) =
      fun line position => if position = place line.1.1.val then 1 else 0 := by
  funext line position
  unfold Reserve.assignedAt
  split
  · rename_i inside
    unfold Due.Settlement.paidAt
    rw [joined_exact]
    have sameUnit : Due.Settlement.originalUnit line = (wholeLot line.1.1.val).2 := by
      apply Subtype.ext
      change line.2.val = (row line.1.1.val).2.val
      exact congrArg (fun need : Row => need.2.val) (a_row_is_its_original_task line)
    have same : ((⟨position, inside⟩, Due.Settlement.originalUnit line) : WholeLot) =
        wholeLot line.1.1.val ↔ position = place line.1.1.val :=
      ⟨fun hit => congrArg (fun used : WholeLot => used.1.val) hit,
        fun hit => Prod.ext (Fin.ext hit) sameUnit⟩
    simp only [same]
  · rename_i outside
    have different : position ≠ place line.1.1.val := fun same =>
      outside (same.symm ▸ (wholeLot line.1.1.val).1.isLt)
    rw [if_neg different]

private theorem joinedOpening (key : Bool × Bool) :
    Reserve.openingNeed (Allocation.heldRows ordered task held) Due.Settlement.address key
      (Reserve.originalSteps source wholeWord (Reserve.assignedAt (Due.Settlement.paidAt joined)))
      (fun line => net.need line) = budget key := by
  have tailItems : Execution.timedInventory (Execution.endAt source word) tailWord =
      (publicLaw.rawItems secondRaw period).map (fun item => (item, (7 : ℚ))) := by
    change Execution.timedInventory start tailWord = _
    simpa [material_starts_at_the_paid_handoff, show (6 : ℚ) + 1 = 7 by norm_num] using
      the_renewal_commits_the_original_inventory start 0 start_is_installed
  have heldRows : Allocation.heldRows ordered task held = [row false] := by decide +kernel
  unfold Reserve.originalSteps
  rw [heldRows, original_handler, paidPosition, Execution.timedInventory_append,
    the_ten_original_items_keep_their_two_committing_clocks, tailItems, funext needed]
  obtain ⟨bearer, good⟩ := key
  cases bearer <;> cases good <;> decide +kernel

theorem the_same_original_bridge_funds_the_third_period :
    Allocation.Fits source wholeWord ordered task booked held budget joined := by
  refine ⟨coversJoined, fun key _ => (Reserve.openingNeed_fits_iff _ _ _ _ _ _).mp ?_⟩
  change Reserve.openingNeed (Allocation.heldRows ordered task held) Due.Settlement.address key
      (Reserve.originalSteps source wholeWord (Reserve.assignedAt (Due.Settlement.paidAt joined)))
      (fun line => net.need line) ≤ Allocation.opening source budget key
  rw [joinedOpening]
  unfold Allocation.opening
  rw [source_reads_the_paid_opening]
  obtain ⟨bearer, good⟩ := key
  cases bearer <;> cases good <;> decide +kernel

def oldPrefix : PaidPrefix source word ordered task (reserved word) held budget :=
  fromHandoff source ordered task reserved held budget
    ⟨Actual.paid, original_demands_are_nonnegative, the_original_handoff_has_paid_its_native_settlement,
      assigned, the_two_services_are_funded_at_the_tight_opening⟩

theorem the_third_actual_period_keeps_every_paid_service_and_uses_no_new_debit_for_it :
    ∃ installed extension, tryRenew oldPrefix ∅ = .paid installed extension ∧
      (Execution.endAt source wholeWord).raw.clock = 7 ∧
      ∀ line (fresh : NewLot),
        extension.combined.allocation line
          ((Due.Service.carriedSupply source word tailWord ordered.toFinset task) (.inr fresh)) = 0 := by
  have paid := each_original_renewal_is_settled 0
  obtain ⟨installed, extension, selected⟩ := (tryRenew_pays_iff oldPrefix ∅).mpr
    ⟨paid.1, (extension_is_complete oldPrefix tailWord ∅).mpr
      ⟨paid.2, joined, keepsPrior, the_same_original_bridge_funds_the_third_period⟩⟩
  refine ⟨installed, extension, selected, ?_, fun line fresh => ?_⟩
  · rw [Execution.endAt_append]
    change (run 1).raw.clock = 7
    simpa [show (6 : ℚ) + 1 = 7 by norm_num] using the_run_clock 1
  · exact extension.a_fully_paid_original_row_cannot_draw_from_a_new_debit line fresh (fullRow line)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
