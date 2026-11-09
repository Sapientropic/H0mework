import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Cut
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (compact)
open Quantities.Execution
open Quantities.Recovery.PersonTime.Cohort.Conservation (stock)

noncomputable section

theorem the_levy_leaves_each_original_person_one_food (bearer : Bool) :
    Original.cut.raw.stock bearer true = 1 := by
  rw [Original.cut_raw]
  rfl

theorem the_original_stocks_are_nonnegative (bearer good : Bool) :
    0 ≤ Original.cut.raw.stock bearer good := by
  rw [Original.cut_raw]
  cases bearer <;> cases good <;> decide +kernel

theorem no_food_output (tech : Unit) (bearer : Bool) :
    amount Bool ((Physical.Public.interpreter compact).technique tech bearer).outputs true = 0 := by
  change amount Bool [(false, (18 : ℚ))] true = 0
  decide +kernel

theorem original_food_opening : stock Original.cut.raw true = 2 := by
  rw [Original.cut_raw]
  decide +kernel

theorem every_original_continuation_has_at_most_two_food (suffix : Original.Word) :
    stock (endAt Original.cut suffix).raw true ≤ 2 := by
  rw [← original_food_opening]
  apply Quantities.Recovery.PersonTime.Cohort.Conservation.unproduced_original_stock_never_increases_in_any_continuation
  rw [Original.same_source]
  exact no_food_output

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
