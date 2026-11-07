import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Retention
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeTrace

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (base base_input_is_the_original_registered_input base_raw_is_the_real_settled_cut
    lifeWord source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

def advance := Execution.primitiveScript [Evolving.Epoch.Consumers.repair]

theorem advance_returns_the_existing_actual_source : Execution.endAt base advance = lifeSource := rfl

theorem the_received_advance_is_one_net_real_unit : stockChange base advance false true = 1 := by
  unfold stockChange
  rw [advance_returns_the_existing_actual_source, the_actual_quote_cut_comes_from_the_paid_original_food_repair,
    base_raw_is_the_real_settled_cut]
  decide +kernel

private theorem the_funded_word_is_physically_paid :
    Accepted (fundedLaw base advance) (Execution.endAt base advance).raw lifeWord := by
  unfold fundedLaw
  rw [advance_returns_the_existing_actual_source, source_input_is_the_original_registered_input,
    the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  unfold Accepted
  decide +kernel

theorem the_original_signed_advance_pays_the_word_and_carries_every_old_row :
    Trace (Execution.endAt base advance) (normalise lifeWord)
      (Execution.endAt base (fundedScript advance lifeWord)) ∧
    Ready (Execution.endAt base (fundedScript advance lifeWord)) ∧
    Recorded base (fundedScript advance lifeWord) := by
  have checked := (real_funding_admits_the_original_word_iff_exact_stock_and_gates base advance lifeWord).mp
    the_funded_word_is_physically_paid
  exact exact_paid_funding_generates_the_original_word_and_complete_account base advance lifeWord
    (advance_returns_the_existing_actual_source.symm ▸ source_ready)
    (advance_returns_the_existing_actual_source.symm ▸ source_review) checked.1 checked.2

theorem the_actual_advance_binds_the_tight_retention_share :
    requiredShare base advance [] lifeWord false true = 1 ∧
    retainedShare base advance [] false true = 1 := by
  unfold requiredShare retainedShare
  rw [List.append_nil, the_received_advance_is_one_net_real_unit]
  unfold fundedLaw stockBaseline
  dsimp only
  rw [advance_returns_the_existing_actual_source, source_input_is_the_original_registered_input,
    the_actual_quote_cut_comes_from_the_paid_original_food_repair, base_raw_is_the_real_settled_cut]
  decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Consumers
