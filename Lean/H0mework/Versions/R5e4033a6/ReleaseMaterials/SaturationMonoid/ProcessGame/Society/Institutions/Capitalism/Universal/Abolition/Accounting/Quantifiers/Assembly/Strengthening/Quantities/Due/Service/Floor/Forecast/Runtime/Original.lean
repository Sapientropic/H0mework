import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Runtime.Fixture
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Runtime
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Use
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Funding
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Runtime.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource lifeScript lifeTrace life_target_is_the_actual_script_successor)
open Innovation.Contribution.Pricing.Consumers.Actual (lifeWord)
open Innovation.Contribution.Pricing.Consumers.Actual
  (every_original_person_keeps_actual_standing source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)

theorem numeric_stock_is_the_literal_original_opening : numericCut = lifeSource.raw := by
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  apply RawCurrent.ext
  · funext party good
    cases party <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

theorem numeric_word_is_the_original_signed_word : numericWord = Service.Consumers.word := rfl

private noncomputable def needed (party : Bool) : Original lifeSource := by
  refine ⟨(party, .necessity, true, 1), ?_, by change (0 : ℚ) < 1; decide⟩
  unfold Demand.requirements Material.originalRequirements
  apply List.mem_flatMap.mpr
  refine ⟨party, every_original_person_keeps_actual_standing party, ?_⟩
  rw [source_input_is_the_original_registered_input]
  change (party, Use.necessity, true, (1 : ℚ)) ∈ [(party, Use.necessity, true, amount Bool [(true, 1)] true)]
  simp [amount]

private theorem every_row_is_a_living_row (row : Original lifeSource) : row = needed row.val.1 := by
  obtain ⟨bearer, _, original⟩ := List.mem_flatMap.mp row.property.1
  rw [source_input_is_the_original_registered_input] at original
  change row.val ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] ++ [] at original
  have exactRow : row.val = (bearer, Use.necessity, true, 1) := by simpa [amount] using original
  apply Subtype.ext
  change row.val = (row.val.1, .necessity, true, 1)
  rw [exactRow]

private theorem original_rows :
    (roster lifeSource).Perm [needed false, needed true] := by
  have distinct : needed false ≠ needed true :=
    fun same => Bool.false_ne_true (congrArg (fun row : Original lifeSource => row.val.1) same)
  have noRepeat : [needed false, needed true].Nodup := List.nodup_cons.mpr
    ⟨fun present => distinct (List.mem_singleton.mp present), List.nodup_singleton _⟩
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) noRepeat).mpr
  intro row
  refine ⟨fun _ => ?_, fun _ => List.mem_toFinset.mp (every_positive_original_floor_is_present lifeSource row)⟩
  rw [every_row_is_a_living_row row]
  cases row.val.1 <;> simp

private abbrev Script := List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

private noncomputable def originalReadings (past : Script) : List ((Bool × Use × Bool × ℚ) × ℚ) :=
  (roster lifeSource).map fun row =>
    (row.val, Demand.delivered lifeSource past row.val.1 row.val.2.1 row.val.2.2.1)

private theorem original_readings_are_the_two_paid_cells (past : Script) (read : Bool → ℚ)
    (exact : ∀ bearer, Demand.delivered lifeSource past bearer .necessity true = read bearer) :
    (originalReadings past).Perm
      [((false, .necessity, true, 1), read false), ((true, .necessity, true, 1), read true)] := by
  let readOriginal := fun row : Original lifeSource =>
    (row.val, Demand.delivered lifeSource past row.val.1 row.val.2.1 row.val.2.2.1)
  have same := original_rows.map readOriginal
  change (originalReadings past).Perm
    [((false, .necessity, true, 1), Demand.delivered lifeSource past false .necessity true),
     ((true, .necessity, true, 1), Demand.delivered lifeSource past true .necessity true)] at same
  simpa only [exact] using same

private theorem no_prior_payment (bearer : Bool) :
    Demand.delivered lifeSource [] bearer .necessity true = 0 := by
  rw [Demand.delivered_is_from_original_inventory]
  rfl

def originalOpening : Snapshot lifeSource [] where
  current := numericCut
  rows := numericRows
  current_exact := numeric_stock_is_the_literal_original_opening
  rows_exact := (original_readings_are_the_two_paid_cells [] (fun _ => 0) no_prior_payment).symm

def numericPaidCut : RawCurrent Bool Bool Unit Unit :=
  { numericCut with stock := fun bearer good => if good then 0 else numericCut.stock bearer good }

private theorem paid_stock_is_the_literal_successor :
    numericPaidCut = (Execution.endAt lifeSource lifeScript).raw := by
  rw [life_target_is_the_actual_script_successor, lifeTrace.raw_is_the_complete_original_execution 0,
    source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  apply RawCurrent.ext
  · funext party good
    cases party <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

private theorem the_original_prefix_paid_a_unit_each (bearer : Bool) :
    Demand.delivered lifeSource lifeScript bearer .necessity true = 1 := by
  unfold lifeScript
  rw [Demand.delivered_is_from_original_inventory, Execution.primitive_inventory lifeTrace 0,
    show lifeSource.native.handlerFace.rootRead = Physical.Public.interpreter lifeSource.native.input from rfl,
    source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  cases bearer <;> decide +kernel

def originalPaidCut : Snapshot lifeSource lifeScript where
  current := numericPaidCut
  rows := [((false, .necessity, true, 1), 1), ((true, .necessity, true, 1), 1)]
  current_exact := paid_stock_is_the_literal_successor
  rows_exact := (original_readings_are_the_two_paid_cells lifeScript (fun _ => 1) the_original_prefix_paid_a_unit_each).symm

theorem paid_numeric_opening : ∀ party good, 0 ≤ originalPaidCut.current.stock party good := by
  intro party good
  cases party <;> cases good <;> decide +kernel

theorem the_executable_numeric_charge_is_the_original_guard
    (word : RawEvent Bool Bool Bool Unit Unit) (key : Bool × Bool) :
    chargeRows numericRows word key = Production.floorCharge lifeSource [] word key :=
  originalOpening.charge_exact word key

def authenticShortage (word : RawEvent Bool Bool Bool Unit Unit) : Option (Bool × Bool × ℚ) :=
  let stock := originalOpening.current
  let readings := originalOpening.rows
  match inspectRows stock readings word numericOpening with
  | .funded _ => none
  | .short issue =>
    some (issue.address.1, issue.address.2,
      chargeRows readings word issue.address - stock.stock issue.address.1 issue.address.2)

/-- info: (none, some (false, true, 1)) -/
#guard_msgs in
#eval (authenticShortage numericWord, authenticShortage [otherUse])

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Runtime.Consumers
