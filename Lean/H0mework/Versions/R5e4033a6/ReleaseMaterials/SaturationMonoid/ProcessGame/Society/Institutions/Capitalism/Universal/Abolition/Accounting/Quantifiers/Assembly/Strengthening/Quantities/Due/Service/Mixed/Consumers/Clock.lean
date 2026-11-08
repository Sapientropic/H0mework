import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PaidPeriod

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Execution PublicFunction
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (lifeWord quoteCut source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers (halfFee liveClock)

noncomputable section

private abbrev originalInput := Joint.Consumers.Compact.input
private abbrev law := Physical.Public.interpreter originalInput
private abbrev Raw := RawCurrent Bool Bool Unit Unit
private abbrev Item := ExecutionItem Bool Bool Bool Unit Unit

def early := afterNative lifeSource halfFee
def earlyScript := primitiveScript [halfFee]
def lateWord := lifeWord ++ [halfFee]
def period := periodAndAccounting early lateWord
def mixedScript := earlyScript ++ period
def lateClock := liveClock + 1

private theorem early_valid :
    (Physical.Public.interpreter lifeSource.native.input).Valid lifeSource.raw halfFee := by
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem early_step : Ready early ∧
    early.raw = (Physical.Public.interpreter lifeSource.native.input).step lifeSource.raw halfFee :=
  two_actual_root_steps_pay_and_consume_the_generated_primitive lifeSource halfFee
    source_ready source_review rfl early_valid

private theorem early_review : ReviewAvailable early :=
  afterNative_keeps_the_available_review lifeSource halfFee source_ready source_review rfl early_valid

private theorem early_input : early.native.input = originalInput :=
  (afterNative_keeps_the_same_original_input lifeSource halfFee).trans source_input_is_the_original_registered_input

def rawEarly := law.step quoteCut halfFee

private theorem early_raw : early.raw = rawEarly := by
  rw [early_step.2, source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  rfl

private theorem early_trace : Trace lifeSource [halfFee] early :=
  .cons lifeSource halfFee [] early source_ready source_review rfl early_valid (.nil early)

private theorem original_period_checks (origin : Raw) :
    Review.Guarded.Checks (Public.Scope.checkInput originalInput) origin rawEarly [false, true] lateWord := by
  change Review.Guarded.Checks (Public.Scope.checkInput originalInput) quoteCut rawEarly [false, true] lateWord
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem checked_period : PeriodChecks early lateWord := by
  let n := early.native
  let origin := Actual.origin n.input n.depth n.count
  let input := Public.Scope.checkInput n.input
  let members := Public.Scope.scope n.input n.depth n.count n.prefixLimit n.renewalLimit
    n.oldPast n.actual.snapshot lateWord
  change Review.Guarded.Checks input origin early.raw members lateWord
  have paid : Review.Guarded.Checks input origin early.raw [false, true] lateWord := by
    dsimp only [input, n]
    rw [early_input, early_raw]
    exact original_period_checks origin
  have member (bearer : Bool) : bearer ∈ [false, true] := by cases bearer <;> decide
  refine ⟨paid.1, ?_, paid.2.2.1, ?_, paid.2.2.2.2.1, ?_, paid.2.2.2.2.2.2⟩
  · intro cell listed
    obtain ⟨bearer, _, exactCell⟩ := List.mem_flatMap.mp listed
    exact paid.2.1 cell (List.mem_flatMap.mpr ⟨bearer, member bearer, exactCell⟩)
  · intro bearer _
    exact paid.2.2.2.1 bearer (member bearer)
  · intro bearer _
    exact paid.2.2.2.2.2.1 bearer (member bearer)

private theorem same_normal_word : normalise lateWord = lateWord := rfl

private theorem later_native : Settled early period ∧ (endAt early period).raw = law.next rawEarly lateWord := by
  have actual := the_original_paid_period_retains_all_native_rows early lateWord early_step.1 early_review checked_period
  refine ⟨actual.1, ?_⟩
  rw [period, actual.2, early_input, early_raw, same_normal_word]

theorem late_commit :
    (next early (some (.execute lateWord))).raw.clock = lateClock := by
  rw [a_checked_period_has_the_original_real_effect early lateWord early_step.1 early_review checked_period,
    early_input, early_raw, same_normal_word]
  unfold lateClock
  rw [show liveClock = quoteCut.clock from congrArg RawCurrent.clock the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem early_commit : early.raw.clock = liveClock := by
  rw [early_raw]
  change (law.step quoteCut halfFee).clock = lifeSource.raw.clock
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem mixed_terminal_clock : (endAt lifeSource mixedScript).raw.clock = lateClock := by
  rw [mixedScript, endAt_append, show endAt lifeSource earlyScript = early from rfl, later_native.2]
  unfold lateClock
  rw [show liveClock = quoteCut.clock from congrArg RawCurrent.clock the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem early_stock (party good : Bool) : 0 ≤ early.raw.stock party good := by
  rw [early_raw]
  cases party <;> cases good <;> decide +kernel

theorem mixed_terminal_stock (party good : Bool) :
    0 ≤ (endAt lifeSource mixedScript).raw.stock party good := by
  rw [mixedScript, endAt_append, show endAt lifeSource earlyScript = early from rfl, later_native.2]
  cases party <;> cases good <;> decide +kernel

private theorem late_timed :
    timedInventory early period = (law.rawItems rawEarly lateWord).map fun item => (item, lateClock) := by
  let body : List (Option (Compile.RawInput Bool Bool Bool Unit Unit)) := [some (.execute lateWord)]
  let afterBody := next early (some (.execute lateWord))
  have empty := (the_first_exhausted_native_cut_is_the_original_paid_drain afterBody).2.2.1
  have timedEmpty : timedInventory afterBody (drain afterBody) = [] :=
    List.map_eq_nil_iff.mp ((timedInventory_is_the_original_inventory _ _).trans empty)
  have onlyBody :
      timedInventory early body = (inventory early body).map fun item => (item, afterBody.raw.clock) := by
    simp [body, afterBody, timedInventory, inventory]
  change timedInventory early (body ++ drain afterBody) = _
  rw [timedInventory_append, show endAt early body = afterBody from rfl, timedEmpty, List.append_nil, onlyBody]
  rw [show afterBody.raw.clock = lateClock from late_commit]
  change (inventory early [some (.execute lateWord)]).map _ = _
  rw [a_checked_period_has_the_original_paid_inventory early lateWord early_step.1 early_review checked_period,
    early_input, early_raw, same_normal_word]

def timedReceipts : List (Item × ℚ) :=
  ((law.rawItems quoteCut [halfFee]).map fun item => ({item with index := 0}, liveClock)) ++
    ((law.rawItems rawEarly lateWord).map fun item => (item, lateClock))

theorem the_original_half_debits_commit_at_distinct_actual_clocks :
    timedInventory lifeSource mixedScript = timedReceipts := by
  unfold mixedScript timedReceipts
  rw [timedInventory_append, show endAt lifeSource earlyScript = early from rfl, late_timed,
    show earlyScript = primitiveScript [halfFee] from rfl,
    timed_primitives_are_the_original_material_at_the_same_clock early_trace,
    source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  rw [show liveClock = quoteCut.clock from congrArg RawCurrent.clock the_actual_quote_cut_comes_from_the_paid_original_food_repair]

theorem nativeSettled : Settled lifeSource mixedScript := by
  apply settle
  refine ⟨?_, ?_⟩
  · intro cell original
    obtain ⟨bearer, _, item⟩ := List.mem_flatMap.mp original
    rw [source_input_is_the_original_registered_input] at item
    change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] ++ [] at item
    have same : cell = (bearer, .necessity, true, 1) := by simpa [amount] using item
    rw [same, Demand.delivered_is_from_original_inventory, ← timedInventory_is_the_original_inventory,
      the_original_half_debits_commit_at_distinct_actual_clocks,
      show lifeSource.native.handlerFace.rootRead = Physical.Public.interpreter lifeSource.native.input from rfl,
      source_input_is_the_original_registered_input]
    cases bearer <;> decide +kernel
  · rw [mixedScript, endAt_append, show endAt lifeSource earlyScript = early from rfl]
    exact later_native.1.finished

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers
