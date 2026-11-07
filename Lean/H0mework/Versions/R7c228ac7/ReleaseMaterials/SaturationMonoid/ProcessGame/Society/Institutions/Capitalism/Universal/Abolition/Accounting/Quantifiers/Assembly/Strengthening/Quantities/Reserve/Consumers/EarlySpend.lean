import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Consumers.Advance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (base base_raw_is_the_real_settled_cut lifeWord source_ready source_review
    source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

def earlyUse : Request Bool Bool Bool Unit Unit :=
  ⟨false, [], false, [], .use false [(true, 1 / 2)] .external⟩

def earlyAllocation := Execution.primitiveScript [earlyUse]

private theorem earlyUse_valid :
    (Physical.Public.interpreter lifeSource.native.input).Valid lifeSource.raw earlyUse := by
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem earlyAllocation_funded_cut :
    (Execution.endAt base (advance ++ earlyAllocation)).raw =
      (Physical.Public.interpreter lifeSource.native.input).step lifeSource.raw earlyUse := by
  rw [Execution.endAt_append, advance_returns_the_existing_actual_source]
  exact (two_actual_root_steps_pay_and_consume_the_generated_primitive
    lifeSource earlyUse source_ready source_review rfl earlyUse_valid).2

private theorem half_stock : stockChange base (advance ++ earlyAllocation) false true = 1 / 2 := by
  unfold stockChange
  rw [earlyAllocation_funded_cut, source_input_is_the_original_registered_input,
    the_actual_quote_cut_comes_from_the_paid_original_food_repair, base_raw_is_the_real_settled_cut]
  decide +kernel

private theorem the_requirement_survives_the_early_spend :
    requiredShare base advance earlyAllocation lifeWord false true = 1 := by
  have originalInput : (Execution.endAt base (advance ++ earlyAllocation)).native.input =
      lifeSource.native.input :=
    (Execution.endAt_input base _).trans ((Execution.endAt_input base advance).symm.trans
      (congrArg (fun next => next.native.input) advance_returns_the_existing_actual_source))
  unfold requiredShare fundedLaw stockBaseline
  dsimp only
  rw [the_received_advance_is_one_net_real_unit, earlyAllocation_funded_cut, originalInput,
    source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair,
    base_raw_is_the_real_settled_cut]
  decide +kernel

theorem a_real_early_spend_cannot_disguise_the_original_retention_shortage :
    retainedShare base advance earlyAllocation false true = 1 / 2 ∧
    Recorded base (advance ++ earlyAllocation) ∧
    ¬ Accepted (fundedLaw base (advance ++ earlyAllocation))
      (Execution.endAt base (advance ++ earlyAllocation)).raw lifeWord := by
  have retained : retainedShare base advance earlyAllocation false true = 1 / 2 := by
    simp only [retainedShare, half_stock, the_received_advance_is_one_net_real_unit, div_one]
  refine ⟨retained, record base _, ?_⟩
  intro paid
  have received : 0 < stockChange base advance false true := by
    rw [the_received_advance_is_one_net_real_unit]
    decide
  have kept : 0 ≤ stockChange base (advance ++ earlyAllocation) false true := by
    rw [half_stock]
    norm_num
  have bound := ((actual_retention_iff_tight_share_and_other_original_requirements
    base advance earlyAllocation lifeWord false true received kept).mp paid).2.2
  rw [the_requirement_survives_the_early_spend, retained] at bound
  norm_num at bound

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Consumers
