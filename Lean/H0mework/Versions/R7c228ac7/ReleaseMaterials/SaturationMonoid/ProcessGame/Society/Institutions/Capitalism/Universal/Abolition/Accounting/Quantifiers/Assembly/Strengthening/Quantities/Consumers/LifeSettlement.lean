import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeTrace
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Contract

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Innovation.Contribution.Pricing.Consumers.Actual (lifeWord
  source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair
  every_original_person_keeps_actual_standing the_repair_really_funds_both_original_lives)

noncomputable section

private theorem original_necessity (origin : RawCurrent Bool Bool Unit Unit) (person : Bool) :
    (Public.Scope.checkInput Joint.Consumers.Compact.input).law.necessities origin person = [(true, 1)] := rfl

private theorem original_maintenance (origin : RawCurrent Bool Bool Unit Unit) (person : Bool) :
    (Public.Scope.checkInput Joint.Consumers.Compact.input).law.mandatoryMaintenance origin person = [] := rfl

private theorem living_cell (person : Bool) :
    (person, .necessity, true, 1) ∈ Demand.requirements lifeSource := by
  unfold Demand.requirements Material.originalRequirements
  apply List.mem_flatMap.mpr
  refine ⟨person, every_original_person_keeps_actual_standing person, ?_⟩
  rw [source_input_is_the_original_registered_input]
  simp [original_necessity, original_maintenance, amount]

private theorem both_lives_are_paid : Demand.Covers lifeSource lifeScript := by
  apply (Demand.primitive_covers_iff_original_floor lifeTrace).mpr
  intro cell listed
  unfold Material.originalRequirements at listed
  obtain ⟨person, _, required⟩ := List.mem_flatMap.mp listed
  rw [source_input_is_the_original_registered_input] at required
  have cellExact : cell = (person, .necessity, true, 1) := by
    simpa [original_necessity, original_maintenance, amount] using required
  rw [cellExact, source_input_is_the_original_registered_input,
    the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  cases person <;> decide +kernel

theorem the_two_actual_life_payments_write_the_original_ledger : Settled lifeSource lifeScript :=
  settle lifeSource lifeScript ⟨both_lives_are_paid, by
    rw [life_target_is_the_actual_script_successor]
    exact life_target_has_finished_its_original_native_work⟩

def lifeAmount (script : List (Option (Compile.RawInput Bool Bool Bool Unit Unit))) : EReal :=
  (((Demand.delivered lifeSource script false .necessity true +
    Demand.delivered lifeSource script true .necessity true : ℚ) : ℝ) : EReal)

private theorem lifeAmount_exact : lifeAmount lifeScript = 2 := by
  unfold lifeAmount
  have same (person : Bool) :
      Demand.delivered lifeSource lifeScript person .necessity true = 1 := by
    have active : lifeSource.native.handlerFace.rootRead = Physical.Public.interpreter lifeSource.native.input := rfl
    unfold lifeScript
    rw [Demand.delivered_is_from_original_inventory, active, Execution.primitive_inventory lifeTrace 0,
      source_input_is_the_original_registered_input,
      the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    cases person <;> decide +kernel
  rw [same false, same true]
  norm_num
  exact EReal.coe_coe_eq_natCast 2

theorem the_original_living_requirement_attains_its_tight_material_bound :
    Bounds.lower lifeSource lifeAmount = 2 ∧
      ∃ script, Settled lifeSource script ∧ lifeAmount script = Bounds.lower lifeSource lifeAmount := by
  have paid := the_two_actual_life_payments_write_the_original_ledger
  have envelope := the_original_root_generates_its_feasible_domain_and_tight_bounds lifeSource
  have bound : Bounds.lower lifeSource lifeAmount = 2 := by
    apply le_antisymm
    · exact (Bounds.lower_le lifeSource lifeAmount lifeScript paid.toFeasible).trans_eq lifeAmount_exact
    · apply (envelope.exactBounds lifeAmount).1.2
      rintro value ⟨script, complete, rfl⟩
      have first := complete.paid _ (living_cell false)
      have second := complete.paid _ (living_cell true)
      have both : (2 : ℚ) ≤ Demand.delivered lifeSource script false .necessity true +
          Demand.delivered lifeSource script true .necessity true := by linarith
      exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast both)
  exact ⟨bound, lifeScript, paid, lifeAmount_exact.trans bound.symm⟩

theorem stock_without_actual_use_returns_the_original_living_deficit :
    lifeSource.raw.stock false true = 1 ∧ Recorded lifeSource [] ∧
      Nonempty (Obstruction lifeSource []) := by
  refine ⟨the_repair_really_funds_both_original_lives.1, record lifeSource [],
    ⟨.material ⟨(false, .necessity, true, 1), living_cell false, ?_⟩⟩⟩
  change (0 : ℚ) < 1
  decide

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
