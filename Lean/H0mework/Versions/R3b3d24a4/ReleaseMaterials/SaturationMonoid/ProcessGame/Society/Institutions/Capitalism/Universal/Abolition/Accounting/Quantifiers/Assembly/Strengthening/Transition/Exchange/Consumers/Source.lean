import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Run
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualSource

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Consumers

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (base settledCut base_ready base_review base_raw_is_the_real_settled_cut
    base_input_is_the_original_registered_input)
open Quantities.Exit.Redemption (sourceLaw sourceOrigin)

noncomputable section

abbrev compact := Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.input
abbrev R := Request Bool Bool Bool Unit Unit
abbrev C := Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)

def removeOldStock : R := ⟨true, [], false, [], .transfer true false [(false,109)]⟩
def issue : R := ⟨true, [], false, [], .issue () true false 2⟩
def before : C := afterNative base removeOldStock
def source : C := afterNative before issue
def position : Position Bool Unit := ⟨(),true,false⟩
def beforeRaw := (Physical.Public.interpreter compact).step settledCut removeOldStock
def sourceRaw := (Physical.Public.interpreter compact).step beforeRaw issue
def index := (nativeAccount before).current.slots.length

private theorem removeValid : (sourceLaw base).Valid base.raw removeOldStock := by
  change (Physical.Public.interpreter base.native.input).Valid base.raw removeOldStock
  rw [base_input_is_the_original_registered_input, base_raw_is_the_real_settled_cut]
  decide +kernel

theorem beforeInput : before.native.input = compact :=
  (afterNative_keeps_the_same_original_input base removeOldStock).trans base_input_is_the_original_registered_input

theorem beforeReady : Ready before :=
  (two_actual_root_steps_pay_and_consume_the_generated_primitive
    base removeOldStock base_ready base_review rfl removeValid).1

theorem beforeReview : ReviewAvailable before :=
  afterNative_keeps_the_available_review base removeOldStock base_ready base_review rfl removeValid

theorem beforeRead : before.raw = beforeRaw := by
  unfold before
  rw [(two_actual_root_steps_pay_and_consume_the_generated_primitive
    base removeOldStock base_ready base_review rfl removeValid).2,
    base_raw_is_the_real_settled_cut, base_input_is_the_original_registered_input]
  rfl

theorem issueValid : (sourceLaw before).Valid before.raw issue := by
  change (Physical.Public.interpreter before.native.input).Valid before.raw issue
  rw [beforeInput, beforeRead]
  decide +kernel

theorem sourceInput : source.native.input = compact :=
  (afterNative_keeps_the_same_original_input before issue).trans beforeInput

theorem sourceReady : Ready source :=
  (two_actual_root_steps_pay_and_consume_the_generated_primitive
    before issue beforeReady beforeReview rfl issueValid).1

theorem sourceReview : ReviewAvailable source :=
  afterNative_keeps_the_available_review before issue beforeReady beforeReview rfl issueValid

theorem sourceRead : source.raw = sourceRaw := by
  unfold source
  rw [(two_actual_root_steps_pay_and_consume_the_generated_primitive
    before issue beforeReady beforeReview rfl issueValid).2, beforeInput, beforeRead]
  rfl

theorem the_original_debtor_has_two_due_and_no_old_settlement_stock :
    balance position source.raw = 2 ∧ source.raw.stock position.debtor false = 0 := by
  rw [sourceRead]
  decide +kernel

def plan : Plan Bool Bool Bool Unit Unit where
  supplier := false
  foreign := [(true,1)]
  returns := [(false,2)]
  offer := ⟨true, [], false, [], .transfer true false [(true,1)]⟩
  delivery := ⟨false, [], false, [], .transfer false true [(false,2)]⟩

theorem offer : plan.OfferAdmitted source position := by
  unfold Plan.OfferAdmitted
  change plan.OfferMatches (Physical.Public.interpreter source.native.input) position ∧
    (Physical.Public.interpreter source.native.input).Valid source.raw plan.offer ∧
    Protected (Physical.Public.interpreter source.native.input) (sourceOrigin source) source.raw plan.offer
  rw [sourceInput, sourceRead]
  decide +kernel

theorem middleRead :
    (plan.middle source).raw = (Physical.Public.interpreter compact).step sourceRaw plan.offer := by
  rw [(two_actual_root_steps_pay_and_consume_the_generated_primitive source plan.offer
    sourceReady sourceReview rfl offer.2.1).2, sourceInput, sourceRead]

theorem delivery : plan.DeliveryAdmitted source position := by
  unfold Plan.DeliveryAdmitted
  change plan.DeliveryMatches (Physical.Public.interpreter source.native.input) position ∧
    (Physical.Public.interpreter source.native.input).Valid (plan.middle source).raw plan.delivery ∧
    Protected (Physical.Public.interpreter source.native.input) (sourceOrigin source) (plan.middle source).raw plan.delivery
  rw [middleRead, sourceInput]
  decide +kernel

theorem delivered : Delivered source position plan := pay_exchange source position plan sourceReady sourceReview offer delivery

theorem exchangeRead :
    (plan.exchanged source).raw =
      (Physical.Public.interpreter compact).step ((Physical.Public.interpreter compact).step sourceRaw plan.offer)
        plan.delivery := by
  have input : (plan.middle source).native.input = compact :=
    (afterNative_keeps_the_same_original_input source plan.offer).trans sourceInput
  have first := two_actual_root_steps_pay_and_consume_the_generated_primitive
    source plan.offer sourceReady sourceReview rfl offer.2.1
  have review := afterNative_keeps_the_available_review source plan.offer sourceReady sourceReview rfl offer.2.1
  have valid : (sourceLaw (plan.middle source)).Valid (plan.middle source).raw plan.delivery := by
    change (Physical.Public.interpreter (plan.middle source).native.input).Valid _ _
    rw [input, ← sourceInput]
    exact delivery.2.1
  rw [plan.exchanged_eq, (two_actual_root_steps_pay_and_consume_the_generated_primitive
    (plan.middle source) plan.delivery first.1 review rfl valid).2, input, middleRead]

theorem the_delivered_old_unit_funds_the_tight_two_principal :
    lower source position plan = 0 ∧ materialUpper source position plan = 2 ∧ oldRate source position = 1 := by
  have law : sourceLaw source = Physical.Public.interpreter compact := congrArg Physical.Public.interpreter sourceInput
  have rate : oldRate source position = 1 := by
    change (Physical.Public.interpreter source.native.input).settlementRate () = _
    rw [sourceInput]
    rfl
  have originalRate : Quantities.Exit.Redemption.rate (sourceLaw source) position = 1 := rate
  have unit : Quantities.Exit.Redemption.unit (sourceLaw source) position = false := by
    change (sourceLaw source).settlementUnit () = false
    rw [law]
    rfl
  have floor (bearer : Bool) :
      Quantities.Exit.Redemption.essentials (sourceLaw source) (sourceOrigin source) bearer false = 0 := by
    rw [law]
    change max 0 (amount Bool [(true,1)] false + amount Bool [] false) = (0 : ℚ)
    decide +kernel
  have readback : balance position (plan.exchanged source).raw = 2 ∧
      (plan.exchanged source).raw.stock false false = 224 ∧ (plan.exchanged source).raw.stock true false = 2 := by
    rw [exchangeRead]
    decide +kernel
  have credit : receivedAt source position plan = 2 := by
    rw [the_old_unit_credit_is_the_original_delivered_quantity delivered]
    unfold Plan.received
    rw [unit]
    decide +kernel
  refine ⟨?_, ?_, rate⟩
  · have stock : Quantities.Exit.Redemption.creditorStock (sourceLaw source) (plan.exchanged source).raw position = 224 := by
      unfold Quantities.Exit.Redemption.creditorStock
      rw [unit]
      exact readback.2.1
    unfold lower Quantities.Exit.Redemption.lower
    rw [stock, unit, floor, originalRate]
    norm_num
  · have stock : Quantities.Exit.Redemption.debtorStock (sourceLaw source) (plan.exchanged source).raw position = 2 := by
      unfold Quantities.Exit.Redemption.debtorStock
      rw [unit]
      exact readback.2.2
    unfold materialUpper Quantities.Exit.Redemption.upper
    simp only [readback.1, stock, unit, floor, originalRate, credit]
    norm_num

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Consumers
