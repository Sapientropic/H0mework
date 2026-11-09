import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Original
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PaidPeriod

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (normalise)
open Conflict.Consumers.Evolving (C W compact life)
open Quantities.Execution
open Quantities.Recovery.PersonTime.Cohort.Conservation (stock)

noncomputable section

def livingWord : W := [life false, life true]

def livingPeriod : Original.Word := periodAndAccounting Original.cut livingWord

private theorem compact_living_checks (origin : Original.Raw) :
    Review.Guarded.Checks (Public.Scope.checkInput compact) origin (Original.snapshot 111 113)
      [false, true] livingWord := by
  change Review.Guarded.Checks (Public.Scope.checkInput compact) (Original.snapshot 111 113)
    (Original.snapshot 111 113) [false, true] livingWord
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem the_living_period_passes_the_original_guards_at (cut : C)
    (same : cut.native.input = compact) (raw : cut.raw = Original.snapshot 111 113) :
    PeriodChecks cut livingWord := by
  let n := cut.native
  let origin := Capitalism.Universal.Abolition.Root.Actual.origin n.input n.depth n.count
  let input := Public.Scope.checkInput n.input
  let members := Public.Scope.scope n.input n.depth n.count n.prefixLimit n.renewalLimit n.oldPast
    n.actual.snapshot livingWord
  change Review.Guarded.Checks input origin cut.raw members livingWord
  have paid : Review.Guarded.Checks input origin cut.raw [false, true] livingWord := by
    dsimp only [input, n]
    rw [same, raw]
    exact compact_living_checks origin
  have member (bearer : Bool) : bearer ∈ [false, true] := by cases bearer <;> decide
  refine ⟨paid.1, ?_, paid.2.2.1, ?_, paid.2.2.2.2.1, ?_, paid.2.2.2.2.2.2⟩
  · intro cell listed
    obtain ⟨bearer, _, required⟩ := List.mem_flatMap.mp listed
    exact paid.2.1 cell (List.mem_flatMap.mpr ⟨bearer, member bearer, required⟩)
  · intro bearer _
    exact paid.2.2.2.1 bearer (member bearer)
  · intro bearer _
    exact paid.2.2.2.2.2.1 bearer (member bearer)

theorem the_living_period_passes_the_original_guards : PeriodChecks Original.cut livingWord :=
  the_living_period_passes_the_original_guards_at Original.cut Original.same_source Original.cut_raw

theorem the_original_cut_pays_one_real_living_period :
    Quantities.Settled Original.cut livingPeriod ∧
      (endAt Original.cut livingPeriod).raw =
        (Physical.Public.interpreter compact).next (Original.snapshot 111 113) livingWord := by
  have paid := the_original_paid_period_retains_all_native_rows Original.cut livingWord
    Original.ready Original.review the_living_period_passes_the_original_guards
  refine ⟨paid.1, ?_⟩
  rw [livingPeriod, paid.2, Original.same_source, Original.cut_raw,
    show normalise livingWord = livingWord from rfl]

theorem the_living_period_moves_the_original_clock_one :
    (endAt Original.cut livingPeriod).raw.clock = Original.cut.raw.clock + 1 := by
  rw [the_original_cut_pays_one_real_living_period.2, Original.cut_raw]
  decide +kernel

theorem the_living_period_pays_one_unit_to_each_original_bearer (bearer : Bool) :
    Quantities.Demand.delivered Original.cut livingPeriod bearer .necessity true = 1 := by
  rw [Quantities.Demand.delivered_is_from_original_inventory, livingPeriod,
    inventory_of_the_original_period_and_accounting Original.cut livingWord Original.ready Original.review
      the_living_period_passes_the_original_guards,
    show Original.cut.native.handlerFace.rootRead = Physical.Public.interpreter Original.cut.native.input from rfl,
    Original.same_source, Original.cut_raw, show normalise livingWord = livingWord from rfl]
  cases bearer <;> decide +kernel

theorem the_living_period_uses_each_original_bearers_last_food (bearer : Bool) :
    (endAt Original.cut livingPeriod).raw.stock bearer true = 0 := by
  rw [the_original_cut_pays_one_real_living_period.2]
  cases bearer <;> decide +kernel

theorem food_is_exhausted_after_the_living_period :
    stock (endAt Original.cut livingPeriod).raw true = 0 := by
  rw [the_original_cut_pays_one_real_living_period.2]
  decide +kernel

#print axioms the_original_cut_pays_one_real_living_period

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
