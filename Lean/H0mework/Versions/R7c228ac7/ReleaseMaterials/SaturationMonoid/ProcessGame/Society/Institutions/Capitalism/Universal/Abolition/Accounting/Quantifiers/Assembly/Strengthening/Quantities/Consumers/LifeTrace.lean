import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualChecks

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual (life lifeWord source_ready source_review
  source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair)

noncomputable section

abbrev lifeSource := Innovation.Contribution.Pricing.Consumers.Actual.source

def lifeMiddle := afterNative lifeSource (life false)
def lifeTarget := afterNative lifeMiddle (life true)
def lifeScript := Execution.primitiveScript lifeWord

private theorem firstValid : (Physical.Public.interpreter lifeSource.native.input).Valid lifeSource.raw (life false) := by
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem firstStep : Ready lifeMiddle ∧
    lifeMiddle.raw = (Physical.Public.interpreter lifeSource.native.input).step lifeSource.raw (life false) :=
  two_actual_root_steps_pay_and_consume_the_generated_primitive
    lifeSource (life false) source_ready source_review rfl firstValid

private theorem middleReview : ReviewAvailable lifeMiddle :=
  afterNative_keeps_the_available_review lifeSource (life false) source_ready source_review rfl firstValid

private theorem secondValid :
    (Physical.Public.interpreter lifeMiddle.native.input).Valid lifeMiddle.raw (life true) := by
  have same : lifeMiddle.native.input = lifeSource.native.input :=
    afterNative_keeps_the_same_original_input lifeSource (life false)
  rw [same, firstStep.2,
    source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem lifeTrace : Trace lifeSource lifeWord lifeTarget :=
  .cons lifeSource (life false) _ _ source_ready source_review rfl firstValid
    (.cons lifeMiddle (life true) [] lifeTarget firstStep.1 middleReview rfl secondValid (.nil lifeTarget))

theorem life_target_is_the_actual_script_successor : Execution.endAt lifeSource lifeScript = lifeTarget :=
  Execution.original_primitive_trace lifeTrace

theorem life_target_has_finished_its_original_native_work : Ready lifeTarget :=
  (two_actual_root_steps_pay_and_consume_the_generated_primitive
    lifeMiddle (life true) firstStep.1 middleReview rfl secondValid).1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
