import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualState

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

abbrev Raw := RawCurrent Bool Bool Unit Unit
abbrev R := Request Bool Bool Bool Unit Unit

theorem base_input_is_the_original_registered_input :
    base.native.input = Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.input := rfl

theorem the_original_food_repair_is_actually_payable :
    (Physical.Public.interpreter base.native.input).Valid base.raw Evolving.Epoch.Consumers.repair := by
  rw [base_raw_is_the_real_settled_cut,base_input_is_the_original_registered_input]
  decide +kernel

def source := Root.Runtime.afterNative base Evolving.Epoch.Consumers.repair

def quoteCut : Raw :=
  (PublicFunction.physicalLaw Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.law).step
    settledCut Evolving.Epoch.Consumers.repair

theorem source_ready : Root.Runtime.Ready source :=
  (Root.Runtime.two_actual_root_steps_pay_and_consume_the_generated_primitive base Evolving.Epoch.Consumers.repair
    base_ready base_review rfl the_original_food_repair_is_actually_payable).1

theorem source_review : Root.Runtime.ReviewAvailable source :=
  Root.Runtime.afterNative_keeps_the_available_review base Evolving.Epoch.Consumers.repair
    base_ready base_review rfl the_original_food_repair_is_actually_payable

theorem the_actual_quote_cut_comes_from_the_paid_original_food_repair : source.raw = quoteCut := by
  unfold source
  rw [Root.Runtime.two_actual_root_steps_pay_and_consume_the_generated_primitive base Evolving.Epoch.Consumers.repair
    base_ready base_review rfl the_original_food_repair_is_actually_payable |>.2,
    base_raw_is_the_real_settled_cut,base_input_is_the_original_registered_input]
  rfl

theorem source_input_is_the_original_registered_input :
    source.native.input = Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.input :=
  (Root.Runtime.afterNative_keeps_the_same_original_input base Evolving.Epoch.Consumers.repair).trans
    base_input_is_the_original_registered_input

theorem the_repair_really_funds_both_original_lives :
    source.raw.stock false true = 1 ∧ source.raw.stock true true = 1 ∧
      source.raw.stock false false = 117 ∧ source.raw.stock true false = 109 := by
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
