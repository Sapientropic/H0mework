import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Material
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeSettlement

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers

open Source.Program PublicFunction.Repayment Abolition.Root.Registered
open Innovation.Contribution.Pricing.Consumers.Actual
  (lifeWord source_ready source_review task life
    source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair
    the_repair_really_funds_both_original_lives)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open Redemption (sourceLaw sourceOrigin unit rate lower)

noncomputable section

def position : Position Bool Unit := ⟨(), true, false⟩

def proposal (quantity : ℚ) : Proposal Bool Bool Bool Unit Unit :=
  ⟨[], quantity, Execution.primitiveScript lifeWord⟩

private theorem original_rate : rate (sourceLaw lifeSource) position = 1 := by
  unfold rate sourceLaw
  rw [source_input_is_the_original_registered_input]
  rfl

theorem original_unit : unit (sourceLaw lifeSource) position = false := by
  unfold unit sourceLaw
  rw [source_input_is_the_original_registered_input]
  rfl

private theorem already_has_cash_floor :
    lower (sourceLaw lifeSource) (sourceOrigin lifeSource) lifeSource.raw position = 0 := by
  unfold sourceLaw sourceOrigin
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem original_stock_supports_one :
    1 ≤ stockCeiling (sourceLaw lifeSource) (sourceOrigin lifeSource) lifeSource.raw position := by
  unfold sourceLaw sourceOrigin
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem the_original_claim_is_nonnegative : 0 ≤ balance position lifeSource.raw := by
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem pay_from_the_existing_source (quantity : ℚ) (positive : 0 < quantity) (bounded : quantity ≤ 1) :
    PaidAt lifeSource position quantity := by
  apply (actual_grant_amounts_fill_the_exact_original_funded_interval lifeSource position quantity source_ready source_review).mpr
  refine ⟨by decide, by rw [original_rate]; decide, the_original_claim_is_nonnegative, ?_, bounded.trans original_stock_supports_one⟩
  rw [already_has_cash_floor]
  exact positive.le

theorem original_food_is_still_available (quantity : ℚ) (paid : PaidAt lifeSource position quantity)
    (bearer : Bool) :
    (redeemed lifeSource position (proposal quantity)).raw.stock bearer true = 1 := by
  have other : true ≠ unit (sourceLaw (funded lifeSource (proposal quantity))) position := by
    change true ≠ unit (sourceLaw lifeSource) position
    rw [original_unit]
    decide
  have same := the_paid_grant_preserves_every_other_material_unit lifeSource position (proposal quantity) paid bearer true other
  change (redeemed lifeSource position (proposal quantity)).raw.stock bearer true = lifeSource.raw.stock bearer true at same
  rw [same]
  cases bearer
  · exact the_repair_really_funds_both_original_lives.1
  · exact the_repair_really_funds_both_original_lives.2.1

theorem redeemed_input_is_the_original (quantity : ℚ) :
    (redeemed lifeSource position (proposal quantity)).native.input = lifeSource.native.input :=
  Execution.endAt_input lifeSource _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
