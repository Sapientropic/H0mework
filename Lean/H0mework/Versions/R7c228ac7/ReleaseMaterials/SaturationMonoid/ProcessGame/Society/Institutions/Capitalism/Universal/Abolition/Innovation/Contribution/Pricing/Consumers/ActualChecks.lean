import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualBranches

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program Source.ProgrammeControl
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

def lifeWord : List R := [life false,life true]
def checkedWords : List (List R) := [lifeWord,wholeWord 2,wholeWord 4]

theorem each_original_test_word_really_passes_the_complete_period_checks
    (word : List R) (original : word ∈ checkedWords) :
    Material.PeriodChecks (Root.sourceInput source) source.raw source.members word := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold Material.ActualAndIndependent
    rw [the_quote_uses_the_original_public_physical_law,the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    simp only [checkedWords,List.mem_cons,List.not_mem_nil,or_false] at original
    rcases original with rfl | rfl | rfl <;> decide +kernel
  · intro person _present
    rw [the_quote_uses_the_original_public_physical_law,the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    simp only [checkedWords,List.mem_cons,List.not_mem_nil,or_false] at original
    rcases original with rfl | rfl | rfl <;> cases person <;> decide +kernel
  · have idempotent : Macro.Public.Scope.checkInput (Root.sourceInput source) = Root.sourceInput source := rfl
    refine idempotent ▸ ?_
    constructor
    · have empty : controlInventory (Macro.Public.Scope.checkInput (Root.sourceInput source)).law source.raw word
          (Material.localFamily (Macro.Public.Scope.checkInput (Root.sourceInput source)) source.raw word) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro use _present
        have families := Functions.open_interpretation_generated_families_empty
          (Root.sourceInput source).law source.raw word (Root.sourceInput source).localAttempts use.item
        have present := use.controlled
        change use.port ∈ Kernel.AssetAuthority.generatedFamily
          (PublicFunction.physicalLaw (Root.sourceInput source).law) source.raw word
          (Root.sourceInput source).localAttempts use.item ++
          Kernel.ActualSurplus.familyAt (PublicFunction.physicalLaw (Root.sourceInput source).law)
            source.raw word use.item at present
        rw [families.1,families.2] at present
        exact List.not_mem_nil present
      rw [empty]
      rfl
    · intro item _listed port _required fresh
      obtain ⟨_accepted,_port,subject,_affected,phase⟩ := fresh
      exact Functions.open_interpretation_has_no_private_phase
        (Root.sourceInput source).law item.before port subject phase
  · intro person _present
    rw [the_quote_uses_the_original_public_physical_law]
    change Material.TechniqueDominates (⟨[],[(false,18)],[],[true]⟩ : Technique Bool Bool)
      ⟨[],[(false,18)],[],[true]⟩
    decide +kernel
  · trivial

theorem every_actual_generated_schedule_has_safe_original_whole_accounts
    (schedule : Root.ScheduleAt source mechanism) (event : schedule.programme.QuotedNature) :
    Source.retainedAccounts schedule false event.val := by
  intro person _person good _good
  rw [every_actual_outside_word_has_the_same_complete_account schedule.provider.word
      schedule.provider.generated schedule.provider.checked,
    every_actual_outside_word_has_the_same_complete_account schedule.payer.word
      schedule.payer.generated schedule.payer.checked,max_self,
    the_actual_branch_requests_have_no_external_price_parameter schedule event,
    the_quote_uses_the_original_public_physical_law]
  rcases every_actual_quoted_branch_is_one_of_the_original_two schedule event with first | second
  · rw [first,the_actual_quote_cut_comes_from_the_paid_original_food_repair]; cases person <;> cases good <;> decide +kernel
  · rw [second,the_actual_quote_cut_comes_from_the_paid_original_food_repair]; cases person <;> cases good <;> decide +kernel

theorem every_actual_generated_schedule_passes_all_its_original_branch_checks
    (schedule : Root.ScheduleAt source mechanism) (event : schedule.programme.QuotedNature) :
    Source.branchChecks schedule false event := by
  obtain ⟨plan,amount,selected⟩ := every_actual_branch_selects_the_original_computed_plan schedule event
  refine ⟨?_,?_,every_actual_generated_schedule_has_safe_original_whole_accounts schedule event⟩
  · simp only [Source.Schedule.payment,selected]
    refine ⟨Or.inr Bool.false_ne_true,?_,?_⟩
    · have afterEq := congrArg (fun programme : Trials.Mechanism Bool Bool Bool Unit Unit => programme.after (event.val : R))
        (every_actual_schedule_uses_the_original_unreloaded_programme schedule)
      change Source.completedPayment (Settlement.compile (Root.sourceInput source).law
        (schedule.programme.after event.val) false true () false plan.transfer) = true
      rw [afterEq,the_quote_uses_the_original_public_physical_law,amount]
      rcases every_actual_quoted_branch_is_one_of_the_original_two schedule event with first | second
      · rw [first]; decide +kernel
      · rw [second]; decide +kernel
    · intro _nonzero
      have afterEq := congrArg (fun programme : Trials.Mechanism Bool Bool Bool Unit Unit => programme.after (event.val : R))
        (every_actual_schedule_uses_the_original_unreloaded_programme schedule)
      rw [afterEq,amount]
      rcases every_actual_quoted_branch_is_one_of_the_original_two schedule event with first | second
      · rw [first]; decide +kernel
      · rw [second]; decide +kernel

  · rw [the_actual_branch_requests_have_no_external_price_parameter schedule event]
    apply each_original_test_word_really_passes_the_complete_period_checks
    rcases every_actual_quoted_branch_is_one_of_the_original_two schedule event with first | second
    · rw [first]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [second]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
