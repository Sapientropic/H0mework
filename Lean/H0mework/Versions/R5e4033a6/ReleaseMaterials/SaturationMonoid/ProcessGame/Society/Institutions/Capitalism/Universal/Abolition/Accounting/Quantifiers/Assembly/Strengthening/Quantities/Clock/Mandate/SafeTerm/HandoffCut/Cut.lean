import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut.Balance
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Frontier

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut

open Source.Program PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch)

def repaymentSuffix : Install.Words :=
  if World.repaymentWord inventory = [] then [] else [World.repaymentWord inventory]

def oldCut : Inventory epoch := Install.submitAll (World.staged inventory) (repaymentSuffix inventory)

abbrev reviewOrdinal := inventory.inputs.length + 2

def choose : Option (Handoff.Ready epoch.bound (oldCut inventory).inputs) :=
  Handoff.chooseAt epoch.bound (oldCut inventory).inputs (reviewOrdinal inventory)

theorem legacy_selector_has_exactly_its_registered_conditions
    (bound : BoundSource base epoch.scope) (inputs : Install.Words) :
    (Handoff.choose bound inputs).isSome = true ↔
      2 ≤ inputs.length ∧ (Handoff.reviews bound inputs).head?.isSome = true ∧
        Handoff.Quiet (Handoff.after bound inputs) := by
  by_cases boundary : 2 ≤ inputs.length
  · rw [Handoff.choose, Handoff.chooseAt, dif_pos boundary, dif_pos ⟨boundary, Nat.le_succ _⟩]
    split
    · by_cases quiet : Handoff.Quiet (Handoff.after bound inputs) <;> simp_all
    · simp_all
  · rw [Handoff.choose, Handoff.chooseAt, dif_neg boundary]
    simp [boundary]

def oldRoute : Input.Event.Evolution ⟨epoch, inventory⟩ ⟨epoch, oldCut inventory⟩ :=
  .append (.submit inventory (World.reviewWord inventory))
    (Install.submitAllEvolution (World.staged inventory) (repaymentSuffix inventory))

theorem old_cut_inputs_are_the_review_and_real_settlement_suffix :
    (oldCut inventory).inputs = inventory.inputs ++ [World.reviewWord inventory] ++ repaymentSuffix inventory :=
  Install.submit_all_inputs _ _

theorem the_original_review_word_is_the_actual_submission_at_the_chosen_period :
    (OutstandingSource.History.actualExecution epoch.source (oldCut inventory).inputs
      (inventory.inputs.length + 1)).submitted = World.reviewWord inventory := by
  have inside : inventory.inputs.length < (oldCut inventory).inputs.length := by
    rw [old_cut_inputs_are_the_review_and_real_settlement_suffix]
    simp only [List.length_append, List.length_singleton]
    omega
  have actual := OutstandingSource.History.scheduled_input_is_actual epoch.source (oldCut inventory).inputs
    inventory.inputs.length inside
  apply actual.trans
  simp only [old_cut_inputs_are_the_review_and_real_settlement_suffix, List.append_assoc,
    List.singleton_append, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]

theorem extra_periods_are_zero_iff_original_balances_clear :
    (repaymentSuffix inventory).length = 0 ↔ originalBalancesClear inventory := by
  rw [← no_added_repayment_iff_all_original_staged_balances_clear]
  unfold repaymentSuffix
  split <;> simp_all

theorem committed_extra_clock_is_its_exact_native_word_count :
    (World.current epoch (oldCut inventory).inputs).clock =
      (stagedCurrent inventory).clock + (repaymentSuffix inventory).length :=
  Install.submit_all_uses_the_actual_elapsed_clock _ _

theorem no_extra_clock_iff_the_original_staged_balances_clear :
    (World.current epoch (oldCut inventory).inputs).clock = (stagedCurrent inventory).clock ↔
      originalBalancesClear inventory := by
  rw [committed_extra_clock_is_its_exact_native_word_count, ← extra_periods_are_zero_iff_original_balances_clear]
  simp

theorem no_debt_reuses_the_literal_paid_review_after
    (clear : originalBalancesClear inventory) : oldCut inventory = World.staged inventory := by
  unfold oldCut repaymentSuffix
  rw [if_pos ((no_added_repayment_iff_all_original_staged_balances_clear inventory).mpr clear)]
  rfl

theorem actual_debt_uses_the_existing_paid_repayment_cut
    (owed : ¬ originalBalancesClear inventory) : oldCut inventory = World.reviewed inventory := by
  have nonempty := fun empty => owed ((no_added_repayment_iff_all_original_staged_balances_clear inventory).mp empty)
  unfold oldCut repaymentSuffix
  rw [if_neg nonempty]
  rfl

theorem chosen_review_has_its_actual_ordinal_and_committed_item
    (fresh : Handoff.Ready epoch.bound (oldCut inventory).inputs)
    (selected : choose inventory = some fresh) :
    fresh.ordinal = reviewOrdinal inventory ∧
      fresh.actual.item.val ∈ (OutstandingSource.History.actualExecution epoch.source (oldCut inventory).inputs
        (inventory.inputs.length + 1)).interpreted.items := by
  have atReview := Handoff.choose_at_recorded_ordinal _ _ _ fresh selected
  refine ⟨atReview, ?_⟩
  have actual := fresh.item_is_its_actual_committed_review
  have depth : fresh.ordinal - 1 = inventory.inputs.length + 1 := by
    rw [atReview]
    change inventory.inputs.length + 2 - 1 = inventory.inputs.length + 1
    omega
  exact (congrArg (fun ordinal => fresh.actual.item.val ∈
    (OutstandingSource.History.actualExecution epoch.source (oldCut inventory).inputs ordinal).interpreted.items) depth).mp actual

theorem a_clear_cut_recovers_the_latest_submitted_review
    (clear : originalBalancesClear inventory)
    (fresh : Handoff.Ready epoch.bound (oldCut inventory).inputs)
    (selected : choose inventory = some fresh) :
    fresh.ordinal = (oldCut inventory).inputs.length + 1 := by
  have ordinal := (chosen_review_has_its_actual_ordinal_and_committed_item inventory fresh selected).1
  calc
    fresh.ordinal = reviewOrdinal inventory := ordinal
    _ = (World.staged inventory).inputs.length + 1 := by
      change inventory.inputs.length + 2 = (inventory.inputs ++ [World.reviewWord inventory]).length + 1
      simp only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.reduceAdd]
    _ = (oldCut inventory).inputs.length + 1 :=
      congrArg (fun cut => cut.inputs.length + 1) (no_debt_reuses_the_literal_paid_review_after inventory clear).symm

theorem a_clear_handoff_removes_one_real_clock_period
    (clear : originalBalancesClear inventory) :
    (World.current epoch (World.reviewed inventory).inputs).clock =
      (World.current epoch (oldCut inventory).inputs).clock + 1 := by
  rw [no_debt_reuses_the_literal_paid_review_after inventory clear]
  exact Install.submit_all_uses_the_actual_elapsed_clock (World.staged inventory) [World.repaymentWord inventory]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.HandoffCut
