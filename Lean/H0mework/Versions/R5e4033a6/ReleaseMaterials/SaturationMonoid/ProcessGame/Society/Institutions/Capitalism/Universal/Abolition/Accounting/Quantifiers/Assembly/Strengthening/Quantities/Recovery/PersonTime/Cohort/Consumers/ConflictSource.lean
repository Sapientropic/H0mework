import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Conservation.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeTrace

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Consumers.ConflictSource

open Source.Program Abolition.Root Abolition.Root.Registered
open Quantities.Consumers (lifeSource lifeMiddle)
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (life source_ready source_review source_input_is_the_original_registered_input
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)

noncomputable section

def exposure := Execution.primitiveScript [life false]

private abbrev Law := Physical.Public.interpreter lifeSource.native.input

private theorem firstValid : Law.Valid lifeSource.raw (life false) := by
  change (Physical.Public.interpreter lifeSource.native.input).Valid lifeSource.raw (life false)
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

private theorem firstPaid :
    Ready lifeMiddle ∧ lifeMiddle.raw = Law.step lifeSource.raw (life false) :=
  two_actual_root_steps_pay_and_consume_the_generated_primitive lifeSource
    (life false) source_ready source_review rfl firstValid

theorem exposure_has_one_actual_food_unit (person : Bool) :
    (Execution.endAt lifeSource exposure).raw.stock person true = if person then 1 else 0 := by
  change lifeMiddle.raw.stock person true = _
  rw [firstPaid.2]
  change ((Physical.Public.interpreter lifeSource.native.input).step lifeSource.raw (life false)).stock person true = _
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  cases person <;> decide +kernel

private def transfer (quantity : ℚ) : Request Bool Bool Bool Unit Unit :=
  ⟨true, [], false, [], .transfer true false [(true, quantity)]⟩

def move (quantity : ℚ) := Execution.primitiveScript [transfer quantity]

private theorem move_is_valid (quantity : ℚ) (nonnegative : 0 ≤ quantity) (available : quantity ≤ 1) :
    (Physical.Public.interpreter lifeMiddle.native.input).Valid lifeMiddle.raw (transfer quantity) := by
  change (Physical.Public.interpreter (afterNative lifeSource (life false)).native.input).Valid
    lifeMiddle.raw (transfer quantity)
  rw [afterNative_keeps_the_same_original_input lifeSource (life false)]
  have stock : lifeMiddle.raw.stock true true = 1 := exposure_has_one_actual_food_unit true
  refine ⟨⟨trivial, rfl⟩, fun _ _ => Or.inl rfl, trivial, ?_, ?_, ?_⟩
  · simpa [transfer, RawLaw.debit, locate, NonnegativeBundle] using nonnegative
  · simpa [transfer, RawLaw.credit, locate, NonnegativeBundle] using nonnegative
  · intro item listed
    rcases List.mem_singleton.mp listed with rfl
    simpa [transfer, RawLaw.debit, locate, flowAt, amount, stock] using available

theorem a_paid_move_changes_the_original_food_addresses
    (quantity : ℚ) (nonnegative : 0 ≤ quantity) (available : quantity ≤ 1) :
    (Execution.endAt lifeSource (exposure ++ move quantity)).raw.stock false true = quantity ∧
      (Execution.endAt lifeSource (exposure ++ move quantity)).raw.stock true true = 1 - quantity := by
  have valid := move_is_valid quantity nonnegative available
  have review : ReviewAvailable lifeMiddle :=
    afterNative_keeps_the_available_review lifeSource (life false) source_ready source_review rfl firstValid
  have paid := (two_actual_root_steps_pay_and_consume_the_generated_primitive lifeMiddle
    (transfer quantity) firstPaid.1 review rfl valid).2
  rw [Execution.endAt_append]
  change (afterNative lifeMiddle (transfer quantity)).raw.stock false true = _ ∧
    (afterNative lifeMiddle (transfer quantity)).raw.stock true true = _
  rw [paid, RawLaw.step, if_pos valid]
  have left : lifeMiddle.raw.stock false true = 0 := exposure_has_one_actual_food_unit false
  have right : lifeMiddle.raw.stock true true = 1 := exposure_has_one_actual_food_unit true
  simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, transfer, locate, flowAt, amount, left, right]

theorem no_installed_technique_outputs_food (tech : Unit) (person : Bool) :
    amount Bool ((Physical.Public.interpreter
      (Execution.endAt lifeSource exposure).native.input).technique tech person).outputs true = 0 := by
  rw [Execution.endAt_input, source_input_is_the_original_registered_input]
  cases tech
  cases person <;> decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Consumers.ConflictSource
