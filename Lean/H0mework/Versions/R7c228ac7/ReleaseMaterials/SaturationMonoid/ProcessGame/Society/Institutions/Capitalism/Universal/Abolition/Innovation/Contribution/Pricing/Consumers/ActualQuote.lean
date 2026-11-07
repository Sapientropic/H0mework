import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualOutside
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualReadback

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
noncomputable section

theorem every_actual_outside_word_has_the_same_complete_account
    (word : List R) (generated : word ∈ Material.Migration.sourceWords (Root.sourceInput source) source.raw 2)
    (checked : Outside.Checks (Root.sourceInput source) source.raw source.members word) (person good : Bool) :
    Outside.value (Root.sourceInput source) source.raw person good word = if good then -1 else 0 := by
  apply every_two_request_outside_word_has_its_exact_original_living_account
    (Root.sourceInput source) source.raw source.members word _
    (every_original_person_keeps_actual_standing false) (every_original_person_keeps_actual_standing true)
    generated checked person good
  intro person
  rw [the_quote_uses_the_original_public_physical_law]
  rfl

theorem every_actual_schedule_uses_the_original_unreloaded_programme
    (schedule : Root.ScheduleAt source mechanism) : schedule.programme = mechanism := by
  unfold Source.Schedule.programme Source.atCut
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair,the_quote_uses_the_original_public_physical_law]
  rfl

theorem both_actual_outside_amounts_are_computed_zero
    (schedule : Root.ScheduleAt source mechanism) : schedule.provider.amount = 0 ∧ schedule.payer.amount = 0 := by
  have unit : (Root.sourceInput source).law.settlementUnit mechanism.terms.instrument = false := by
    rw [the_quote_uses_the_original_public_physical_law]
    rfl
  constructor
  · exact (every_actual_outside_word_has_the_same_complete_account schedule.provider.word
      schedule.provider.generated schedule.provider.checked mechanism.terms.lender
      ((Root.sourceInput source).law.settlementUnit mechanism.terms.instrument)).trans (by rw [unit]; rfl)
  · exact (every_actual_outside_word_has_the_same_complete_account schedule.payer.word
      schedule.payer.generated schedule.payer.checked mechanism.terms.borrower
      ((Root.sourceInput source).law.settlementUnit mechanism.terms.instrument)).trans (by rw [unit]; rfl)

def quoteAmount (rows : List (ℚ × ℚ)) : Option ℚ :=
  match Source.quote rows with
  | .priced plan => some plan.transfer
  | .obstructed _ => none

def quoted (schedule : Root.ScheduleAt source mechanism) : Option ℚ :=
  quoteAmount (schedule.rows signal)

theorem the_actual_original_root_generates_four_without_loading
    (schedule : Root.ScheduleAt source mechanism) : quoted schedule = some 4 := by
  have rowsSame : schedule.rows signal = Source.riskRows mechanism 0 0 signal := by
    simp only [Source.Schedule.rows,(both_actual_outside_amounts_are_computed_zero schedule).1,
      (both_actual_outside_amounts_are_computed_zero schedule).2]
    unfold Source.Schedule.programme Source.atCut
    rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair,the_quote_uses_the_original_public_physical_law]
    rfl
  unfold quoted
  rw [rowsSame]
  decide +kernel

theorem every_actual_schedule_has_its_computed_four_plan
    (schedule : Root.ScheduleAt source mechanism) :
    ∃ plan : Source.Quote (schedule.rows signal), schedule.table signal = .priced plan ∧ plan.transfer = 4 := by
  have actual := the_actual_original_root_generates_four_without_loading schedule
  unfold quoted quoteAmount at actual
  cases selected : Source.quote (schedule.rows signal) with
  | priced plan =>
      rw [selected] at actual
      exact ⟨plan,selected,Option.some.inj actual⟩
  | obstructed issue => rw [selected] at actual; cases actual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
