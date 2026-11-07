import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers.Payments
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Matching
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveClock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers

open Source.Program Abolition.Root.Registered PublicFunction
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (life lifeWord request the_repair_really_funds_both_original_lives source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers (position proposal original_unit original_food_is_still_available life_is_valid_from_actual_stock)
open Redemption (sourceLaw unit)

noncomputable section

private def reversePlan : Proposal Bool Bool Bool Unit Unit := ⟨[], 2, []⟩
private abbrev originalLaw := Physical.Public.interpreter Joint.Consumers.Compact.input

theorem first_read_is_the_original_input : afterFirst.native.input = lifeSource.native.input :=
  Execution.endAt_input lifeSource (paidWord lifeSource (position, 1))

theorem second_read_is_the_original_law : sourceLaw afterSecond = originalLaw := by
  unfold sourceLaw afterSecond
  rw [Execution.endAt_input, first_read_is_the_original_input, source_input_is_the_original_registered_input]

set_option maxHeartbeats 500000 in
private theorem the_first_and_second_grant_leave_original_food (actor : Bool) :
    afterSecond.raw.stock actor true = 1 := by
  have distinct : true ≠ unit (sourceLaw afterFirst) otherPosition := by
    unfold sourceLaw
    rw [first_read_is_the_original_input, source_input_is_the_original_registered_input]
    decide
  have stock : afterSecond.raw.stock actor true = afterFirst.raw.stock actor true :=
    the_paid_grant_preserves_every_other_material_unit afterFirst otherPosition reversePlan originalSecond actor true distinct
  exact stock.trans (original_food_is_still_available 1 originalFirst actor)

private theorem both_actual_lives_are_physically_payable :
    ∀ item ∈ (sourceLaw afterSecond).rawItems afterSecond.raw lifeWord,
      (sourceLaw afterSecond).Valid item.before item.request := by
  rw [second_read_is_the_original_law]
  have first := life_is_valid_from_actual_stock afterSecond.raw false (the_first_and_second_grant_leave_original_food false).ge
  have other : (originalLaw.step afterSecond.raw (life false)).stock true true = 1 := by
    rw [RawLaw.step, if_pos first]
    simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, life, request, locate, flowAt, amount,
      the_first_and_second_grant_leave_original_food true]
  have second := life_is_valid_from_actual_stock (originalLaw.step afterSecond.raw (life false)) true other.ge
  simp only [lifeWord, RawLaw.rawItems, RawLaw.execute, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  exact ⟨first, second⟩

theorem both_lives_are_really_paid_after_both_grants :
    Trace afterSecond lifeWord (Execution.endAt afterSecond both.exit) ∧
      Ready (Execution.endAt afterSecond both.exit) := by
  have signed : ∀ action ∈ lifeWord, action.consents = [] := by
    intro action member
    simp only [lifeWord, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  obtain ⟨trace, ready, _⟩ := Execution.pay_checked_primitives afterSecond lifeWord 0
    originalSecond.ready originalSecond.available signed both_actual_lives_are_physically_payable
  exact ⟨trace, ready⟩

def task : PublicTaskSpec Bool Bool :=
  ⟨[⟨false, [(true, 1)], .necessity⟩, ⟨true, [(true, 1)], .necessity⟩],
    Innovation.Contribution.Pricing.Consumers.Actual.task.earliest,
    Innovation.Contribution.Pricing.Consumers.Actual.task.deadline,
    ⟨_, List.mem_cons_self, _, List.mem_cons_self, by decide⟩⟩

theorem actual_inventory :
    Execution.inventory afterSecond both.exit =
      [⟨0, afterSecond.raw, life false⟩, ⟨0, (sourceLaw afterSecond).step afterSecond.raw (life false), life true⟩] := by
  change Execution.inventory afterSecond (Execution.primitiveScript lifeWord) = _
  rw [Execution.primitive_inventory both_lives_are_really_paid_after_both_grants.1 0]
  rfl

private def positionAt (slot : Fin task.slots.length) : Fin (Execution.inventory afterSecond both.exit).length :=
  ⟨slot.val, by rw [actual_inventory]; exact slot.isLt⟩

private theorem after_both_payments_is_the_original_clock : afterSecond.raw.clock = lifeSource.raw.clock := by
  have second := the_paid_grant_microsteps_keep_the_real_clock afterFirst otherPosition reversePlan originalSecond
  have first := the_paid_grant_microsteps_keep_the_real_clock lifeSource position (proposal 1) originalFirst
  change afterSecond.raw.clock = afterFirst.raw.clock at second
  change afterFirst.raw.clock = lifeSource.raw.clock at first
  exact second.trans first

private theorem cutoff_in_time : task.earliest ≤ afterSecond.raw.clock := by
  rw [after_both_payments_is_the_original_clock, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem both_original_members_have_distinct_actual_exit_services :
    Clock.FullyServed afterSecond task both.exit := by
  let geometry := Clock.geometry afterSecond task both.exit
  apply (Clock.fully_served_iff_the_original_capacity_covers_every_slot _ _ _).mpr
  apply Clock.distinct_paid_positions_cover_the_original_services geometry positionAt
  · intro left _ right _ same
    apply Fin.ext
    exact congrArg (fun item : Fin (Execution.inventory afterSecond both.exit).length => item.val) same
  · intro slot _
    refine ⟨Finset.mem_univ _, ?_⟩
    have valid := both_actual_lives_are_physically_payable
    simp only [lifeWord, RawLaw.rawItems, RawLaw.execute, List.forall_mem_cons, List.not_mem_nil,
      false_implies, implies_true, and_true] at valid
    have cases : slot = ⟨0, by decide⟩ ∨ slot = ⟨1, by decide⟩ := by
      have less : slot.val < 2 := slot.isLt
      rcases show slot.val = 0 ∨ slot.val = 1 by omega with zero | one
      · exact .inl (Fin.ext zero)
      · exact .inr (Fin.ext one)
    rcases cases with rfl | rfl
    · have exactItem : (Execution.inventory afterSecond both.exit).get (positionAt ⟨0, by decide⟩) =
          ⟨0, afterSecond.raw, life false⟩ := by
        have actual := congrArg (fun items => items[0]?) actual_inventory
        have inside : 0 < (Execution.inventory afterSecond both.exit).length := (positionAt ⟨0, by decide⟩).isLt
        rw [List.getElem?_eq_getElem inside] at actual
        exact Option.some.inj actual
      change task.earliest ≤ ((Execution.inventory afterSecond both.exit).get _).before.clock ∧ _ ∧ _
      rw [exactItem]
      exact ⟨cutoff_in_time, valid.1, rfl, rfl, rfl⟩
    · have exactItem : (Execution.inventory afterSecond both.exit).get (positionAt ⟨1, by decide⟩) =
          ⟨0, (sourceLaw afterSecond).step afterSecond.raw (life false), life true⟩ := by
        have actual := congrArg (fun items => items[1]?) actual_inventory
        have inside : 1 < (Execution.inventory afterSecond both.exit).length := (positionAt ⟨1, by decide⟩).isLt
        rw [List.getElem?_eq_getElem inside] at actual
        exact Option.some.inj actual
      have clock : ((sourceLaw afterSecond).step afterSecond.raw (life false)).clock = afterSecond.raw.clock := by
        rw [RawLaw.step, if_pos valid.1]
        rfl
      change task.earliest ≤ ((Execution.inventory afterSecond both.exit).get _).before.clock ∧ _ ∧ _
      rw [exactItem]
      exact ⟨clock.symm ▸ cutoff_in_time, valid.2, rfl, rfl, rfl⟩

theorem both_original_exit_services_commit_in_the_installed_window :
    Clock.Window.FullyServed afterSecond task both.exit := by
  apply Clock.Window.a_fully_paid_script_ending_in_time_serves_every_original_window _ _ _
    both_original_members_have_distinct_actual_exit_services
  rw [Execution.a_paid_primitive_trace_keeps_the_actual_clock both_lives_are_really_paid_after_both_grants.1,
    after_both_payments_is_the_original_clock, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers
