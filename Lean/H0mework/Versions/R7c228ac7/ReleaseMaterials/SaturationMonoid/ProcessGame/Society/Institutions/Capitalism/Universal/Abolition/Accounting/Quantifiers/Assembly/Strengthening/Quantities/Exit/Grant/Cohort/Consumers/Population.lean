import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers.Service
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.PaidUse

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (life lifeWord request every_original_person_keeps_actual_standing source_input_is_the_original_registered_input)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers (position)
open Redemption (sourceLaw)

noncomputable section

private theorem original_population_is_exact : CoversOriginalMembers lifeSource task both := by
  refine ⟨?_, ?_, ?_⟩
  · intro actor _
    cases actor <;> simp [recipients, both, position, otherPosition]
  · intro bid inside
    simp only [both, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    all_goals exact ⟨every_original_person_keeps_actual_standing _, every_original_person_keeps_actual_standing _⟩
  · intro actor _
    cases actor with
    | false => exact ⟨_, List.mem_cons_self, rfl, _, List.mem_cons_self, by decide⟩
    | true => exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, _, List.mem_cons_self, by decide⟩

private theorem original_exit_is_independent :
    ∀ item ∈ Execution.inventory afterSecond both.exit, Independent lifeSource [] item := by
  rw [actual_inventory]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  constructor <;>
    refine ⟨every_original_person_keeps_actual_standing _, List.not_mem_nil, rfl, ?_⟩ <;>
    intro lot present _ <;>
    unfold RawLaw.actualDebit at present <;>
    split at present <;>
    simp [RawLaw.debit, life, request, locate] at present ⊢ <;>
    subst lot <;> rfl

private theorem the_complete_two_member_grant_has_a_real_exit : Actionable lifeSource task 0 both := by
  refine ⟨original_population_is_exact, both_original_members_receive_actual_payments_at_one_root.1, ?_⟩
  rw [both_original_members_receive_actual_payments_at_one_root.2]
  exact ⟨original_exit_is_independent, both_original_exit_services_commit_in_the_installed_window⟩

private def fullWord :=
  (Grant.word (sourceLaw lifeSource) position 1 ++ Grant.word (sourceLaw afterFirst) otherPosition 2) ++ lifeWord

private theorem full_script : Execution.primitiveScript fullWord = compile lifeSource 0 both := by
  unfold fullWord
  simp only [Execution.primitiveScript_append]
  rfl

private theorem full_trace : Trace lifeSource fullWord (Execution.endAt afterSecond both.exit) :=
  Execution.append_primitive_traces
    (Execution.append_primitive_traces originalFirst.actual originalSecond.actual)
    both_lives_are_really_paid_after_both_grants.1

private theorem paid_original_life_rows : Demand.Covers lifeSource (compile lifeSource 0 both) := by
  intro cell required
  unfold Demand.requirements Material.originalRequirements at required
  obtain ⟨bearer, _, sourceCell⟩ := List.mem_flatMap.mp required
  rw [source_input_is_the_original_registered_input] at sourceCell
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] ++ [] at sourceCell
  have exactCell : cell = (bearer, .necessity, true, 1) := by simpa [amount] using sourceCell
  have listed : life bearer ∈ fullWord := by
    apply List.mem_append_right
    cases bearer <;> simp [lifeWord]
  obtain ⟨item, original, same, accepted⟩ := Execution.every_original_request_has_its_paid_native_inventory_item
    full_trace (life bearer) listed
  rw [full_script] at original
  have kind : item.request.operation = .use bearer [(true, 1)] .necessity := by rw [same]; rfl
  have delivered := Demand.an_original_paid_use_is_counted lifeSource _ item original bearer [(true, 1)]
    .necessity true kind accepted
  rw [exactCell]
  simpa [amount] using delivered

theorem the_original_population_word_is_settled : Settled lifeSource (compile lifeSource 0 both) := by
  apply settle
  refine ⟨paid_original_life_rows, ?_⟩
  rw [the_paid_population_exit_uses_the_literal_original_successor, both_original_members_receive_actual_payments_at_one_root.2]
  exact both_lives_are_really_paid_after_both_grants.2

theorem the_full_original_population_really_enters_the_joint_exit_domain :
    tenderAmounts lifeSource both ∈ Bounds.System.values lifeSource (compile lifeSource 0)
      (checkPopulation lifeSource task 0) (tenderAmounts lifeSource) :=
  (exact_simultaneous_population_amounts _ _ _ _).mpr ⟨both, the_original_population_word_is_settled,
    the_complete_two_member_grant_has_a_real_exit, rfl⟩

def onlyFirst := { both with tenders := [(position, 1)] }

theorem paying_only_one_original_recipient_leaves_the_other_member_visible :
    Recorded lifeSource (compile lifeSource 0 onlyFirst) ∧
      Nonempty (PopulationFailure lifeSource task onlyFirst) ∧ ¬ Actionable lifeSource task 0 onlyFirst := by
  have failure : PopulationFailure lifeSource task onlyFirst :=
    .unpaid true (every_original_person_keeps_actual_standing true) (by decide)
  exact ⟨record lifeSource _, ⟨failure⟩, fun completed => failure.refutes completed.1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers
