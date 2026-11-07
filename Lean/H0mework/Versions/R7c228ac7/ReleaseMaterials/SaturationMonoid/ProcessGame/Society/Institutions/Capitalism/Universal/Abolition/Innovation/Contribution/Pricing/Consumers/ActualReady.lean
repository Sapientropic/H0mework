import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualChecks
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualCatalogue

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction
noncomputable section

theorem the_two_lives_are_actually_in_the_source_word_domain :
    lifeWord ∈ Material.Migration.sourceWords (Root.sourceInput source) source.raw mechanism.code.actionLimit := by
  apply (Material.Migration.sourceWords_complete _ _ _ _).mpr
  refine ⟨by decide +kernel,?_⟩
  intro item original
  simp only [lifeWord,List.mem_cons,List.not_mem_nil,or_false] at original
  rcases original with rfl | rfl
  · exact each_life_request_is_in_the_actual_original_source_alphabet false
  · exact each_life_request_is_in_the_actual_original_source_alphabet true

theorem the_two_actual_lives_pass_the_outside_checks :
    Outside.Checks (Root.sourceInput source) source.raw source.members lifeWord := by
  refine ⟨each_original_test_word_really_passes_the_complete_period_checks lifeWord List.mem_cons_self,?_⟩
  decide +kernel

def firstNature (schedule : Root.ScheduleAt source mechanism) : schedule.programme.QuotedNature :=
  ⟨nature 2,by change Distributed.Event.adversary (nature 2) ∈ [.adversary (nature 2),.adversary (nature 4)]
               exact List.mem_cons_self⟩

theorem the_actual_source_preparation_is_ready :
    ∃ prepared : Root.Prepared source mechanism, Root.prepare source mechanism = .ready prepared := by
  cases computed : Root.prepare source mechanism with
  | providerBlocked failures | payerBlocked failures =>
      exact False.elim (((failures lifeWord the_two_lives_are_actually_in_the_source_word_domain).refutes
        _ _ _) the_two_actual_lives_pass_the_outside_checks)
  | noForecast schedule empty =>
      have original := every_declared_nature_is_in_the_forecast_domain schedule.programme (firstNature schedule)
      rw [empty] at original
      exact False.elim (List.not_mem_nil original)
  | riskBlocked schedule event _original failed =>
      exact False.elim (failed (every_actual_generated_schedule_passes_all_its_original_branch_checks schedule event))
  | ready prepared => exact ⟨prepared,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
