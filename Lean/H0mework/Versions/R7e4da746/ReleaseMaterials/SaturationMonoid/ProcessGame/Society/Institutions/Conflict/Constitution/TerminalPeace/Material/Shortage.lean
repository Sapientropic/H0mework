import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Horizon

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
  (source_parameters source_input_is_the_original_registered_input)
open Conflict.Consumers.Evolving (C issue compact)
open Quantities.Execution
open Quantities.Demand (requirements Deficit delivered)

noncomputable section

private theorem native_indices (cut : C) (word : Original.Word) :
    (endAt cut word).native.depth = cut.native.depth ∧
      (endAt cut word).native.count = cut.native.count ∧
      (endAt cut word).native.prefixLimit = cut.native.prefixLimit ∧
      (endAt cut word).native.renewalLimit = cut.native.renewalLimit ∧
      (endAt cut word).native.oldPast = cut.native.oldPast := by
  induction word generalizing cut with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons input later ih =>
    have rest := ih (next cut input)
    have first : (next cut input).native.depth = cut.native.depth ∧
        (next cut input).native.count = cut.native.count ∧
        (next cut input).native.prefixLimit = cut.native.prefixLimit ∧
        (next cut input).native.renewalLimit = cut.native.renewalLimit ∧
        (next cut input).native.oldPast = cut.native.oldPast := by
      have p := (query cut input).advance_parameters
      cases input <;> exact ⟨p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1⟩
    exact ⟨rest.1.trans first.1, rest.2.1.trans first.2.1, rest.2.2.1.trans first.2.2.1,
      rest.2.2.2.1.trans first.2.2.2.1, rest.2.2.2.2.trans first.2.2.2.2⟩

theorem each_original_person_keeps_standing_at_every_material_successor
    (suffix : Original.Word) (bearer : Bool) : bearer ∈ (endAt Original.cut suffix).members := by
  let quote := Conflict.Consumers.Evolving.Original.source
  have original : endAt quote (primitiveScript [issue]) = Original.seed := rfl
  have same : endAt quote ((primitiveScript [issue] ++ Original.history) ++ suffix) =
      endAt Original.cut suffix := by
    rw [endAt_append, endAt_append, original]
  have params := native_indices quote ((primitiveScript [issue] ++ Original.history) ++ suffix)
  rw [same] at params
  have input : (endAt Original.cut suffix).native.input = compact :=
    (endAt_input Original.cut suffix).trans Original.same_source
  apply Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
  rw [input, params.1, params.2.1, params.2.2.1, params.2.2.2.1, params.2.2.2.2,
    source_parameters.1, source_parameters.2.1, source_parameters.2.2.1,
    source_parameters.2.2.2.1, source_parameters.2.2.2.2]
  cases bearer <;> decide +kernel

theorem each_original_food_cell_survives_every_original_continuation
    (suffix : Original.Word) (bearer : Bool) :
    (bearer, .necessity, true, (1 : ℚ)) ∈ requirements (endAt Original.cut suffix) := by
  unfold requirements Capitalism.Universal.Abolition.Material.originalRequirements
  apply List.mem_flatMap.mpr
  refine ⟨bearer, each_original_person_keeps_standing_at_every_material_successor suffix bearer, ?_⟩
  rw [(endAt_input Original.cut suffix).trans Original.same_source]
  change (bearer, Use.necessity, true, (1 : ℚ)) ∈
    [(bearer, Use.necessity, true, amount Bool [(true, 1)] true)]
  simp [amount]

/-- Both exact original living rows are still present when the original
food is spent. A refusal cannot turn either shortfall into an unowned row. -/
def an_original_bearers_second_period_food_deficit (suffix : Original.Word) (bearer : Bool) :
    Deficit (endAt Original.cut livingPeriod) suffix where
  cell := (bearer, .necessity, true, 1)
  original := each_original_food_cell_survives_every_original_continuation livingPeriod bearer
  shortage := by
    change delivered (endAt Original.cut livingPeriod) suffix bearer .necessity true < 1
    rw [no_original_continuation_after_the_paid_period_can_deliver_either_food]
    norm_num

theorem that_bearers_material_gap_is_exactly_one (suffix : Original.Word) (bearer : Bool) :
    let deficit := an_original_bearers_second_period_food_deficit suffix bearer
    deficit.cell.2.2.2 - delivered (endAt Original.cut livingPeriod) suffix
      deficit.cell.1 deficit.cell.2.1 deficit.cell.2.2.1 = 1 := by
  change (1 : ℚ) - delivered (endAt Original.cut livingPeriod) suffix bearer .necessity true = 1
  rw [no_original_continuation_after_the_paid_period_can_deliver_either_food, sub_zero]

theorem every_longer_original_schedule_returns_its_first_typed_food_deficit
    (windows : List Original.Word) (many : 1 < windows.length) :
    ∃ (front : List Original.Word) (window : Original.Word) (tail : List Original.Word) (bearer : Bool)
      (issue : Deficit (endAt Original.cut front.flatten) window),
      windows = front ++ window :: tail ∧ PaidFoodWindows Original.cut front ∧
        issue.cell = (bearer, .necessity, true, 1) ∧
        Quantities.Recorded Original.seed (Original.history ++ front.flatten ++ window) := by
  obtain ⟨front, window, tail, bearer, exactWindows, earlier, lacking⟩ :=
    a_second_living_window_has_a_named_original_shortage windows many
  let issue : Deficit (endAt Original.cut front.flatten) window :=
    ⟨(bearer, .necessity, true, 1),
      each_original_food_cell_survives_every_original_continuation front.flatten bearer, lacking⟩
  exact ⟨front, window, tail, bearer, issue, exactWindows, earlier, rfl, Quantities.record _ _⟩

#print axioms an_original_bearers_second_period_food_deficit
#print axioms that_bearers_material_gap_is_exactly_one
#print axioms every_longer_original_schedule_returns_its_first_typed_food_deficit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
