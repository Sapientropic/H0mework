import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Plan
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime
open Quantities (Recorded record)
open Quantities.Exit.Redemption (sourceLaw sourceOrigin)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument

def Plan.script (plan : P) := Quantities.Execution.primitiveScript plan.word

abbrev Plan.middle (plan : P) (source : C) := afterNative source plan.offer

abbrev Plan.exchanged (plan : P) (source : C) := Quantities.Execution.endAt source plan.script

theorem Plan.exchanged_eq (plan : P) (source : C) :
    plan.exchanged source = afterNative (plan.middle source) plan.delivery := rfl

theorem Plan.sameLaw (plan : P) (source : C) :
    sourceLaw (plan.exchanged source) = sourceLaw source := by
  exact congrArg Physical.Public.interpreter (Quantities.Execution.endAt_input source plan.script)

theorem Plan.sameOrigin (plan : P) (source : C) :
    sourceOrigin (plan.exchanged source) = sourceOrigin source := by
  obtain ⟨input, depth, count⟩ :=
    Quantities.Execution.the_actual_script_keeps_the_original_reader_indices source plan.script
  change Actual.origin _ _ _ = Actual.origin _ _ _
  rw [input, depth, count]

def Plan.OfferAdmitted (plan : P) (source : C) (position : Position Party Instrument) : Prop :=
  plan.OfferMatches (sourceLaw source) position ∧
    (sourceLaw source).Valid source.raw plan.offer ∧
    Protected (sourceLaw source) (sourceOrigin source) source.raw plan.offer

def Plan.DeliveryAdmitted (plan : P) (source : C) (position : Position Party Instrument) : Prop :=
  plan.DeliveryMatches (sourceLaw source) position ∧
    (sourceLaw source).Valid (plan.middle source).raw plan.delivery ∧
    Protected (sourceLaw source) (sourceOrigin source) (plan.middle source).raw plan.delivery

instance (plan : P) (source : C) (position : Position Party Instrument) :
    Decidable (plan.OfferAdmitted source position) := by
  unfold Plan.OfferAdmitted
  infer_instance

instance (plan : P) (source : C) (position : Position Party Instrument) :
    Decidable (plan.DeliveryAdmitted source position) := by
  unfold Plan.DeliveryAdmitted
  infer_instance

/-- Both original material positions are read at their own native cuts.
The old debt has not been reduced at the point the exchange is received. -/
structure Delivered (source : C) (position : Position Party Instrument) (plan : P) : Prop where
  offer : plan.OfferAdmitted source position
  delivery : plan.DeliveryAdmitted source position
  trace : Trace source plan.word (plan.exchanged source)
  ready : Ready (plan.exchanged source)
  review : ReviewAvailable (plan.exchanged source)
  offerFlow : (sourceLaw source).actualDebit source.raw plan.offer =
      locate position.debtor plan.foreign ∧
    (sourceLaw source).actualCredit source.raw plan.offer = locate plan.supplier plan.foreign
  deliveryFlow : (sourceLaw source).actualDebit (plan.middle source).raw plan.delivery =
      locate plan.supplier plan.returns ∧
    (sourceLaw source).actualCredit (plan.middle source).raw plan.delivery = locate position.debtor plan.returns
  originalClaims : (plan.exchanged source).raw.claims = source.raw.claims
  complete : Recorded source plan.script

theorem pay_exchange (source : C) (position : Position Party Instrument) (plan : P)
    (ready : Ready source) (review : ReviewAvailable source)
    (offer : plan.OfferAdmitted source position) (delivery : plan.DeliveryAdmitted source position) :
    Delivered source position plan := by
  have originalOffer := offer
  have originalDelivery := delivery
  obtain ⟨offerShape, offerValid, offerProtected⟩ := offer
  obtain ⟨deliveryShape, deliveryValid, deliveryProtected⟩ := delivery
  obtain ⟨_, _, _, _, offerConsents, offerTransfer⟩ := offerShape
  obtain ⟨_, _, deliveryConsents, deliveryTransfer⟩ := deliveryShape
  have first := two_actual_root_steps_pay_and_consume_the_generated_primitive
    source plan.offer ready review offerConsents offerValid
  have firstReview := afterNative_keeps_the_available_review source plan.offer
    ready review offerConsents offerValid
  have input : (plan.middle source).native.input = source.native.input :=
    afterNative_keeps_the_same_original_input source plan.offer
  have valid : (sourceLaw (plan.middle source)).Valid (plan.middle source).raw plan.delivery := by
    rw [show sourceLaw (plan.middle source) = sourceLaw source from congrArg Physical.Public.interpreter input]
    exact deliveryValid
  have second := two_actual_root_steps_pay_and_consume_the_generated_primitive
    (plan.middle source) plan.delivery first.1 firstReview deliveryConsents valid
  have secondReview := afterNative_keeps_the_available_review (plan.middle source) plan.delivery
    first.1 firstReview deliveryConsents valid
  refine ⟨originalOffer, originalDelivery, .cons _ _ _ _ ready review offerConsents offerValid
    (.cons _ _ [] _ first.1 firstReview deliveryConsents valid (.nil _)), second.1, secondReview,
    a_paid_transfer_has_its_original_debit_and_credit _ _ _ _ _ _ offerTransfer offerValid,
    a_paid_transfer_has_its_original_debit_and_credit _ _ _ _ _ _ deliveryTransfer deliveryValid,
    ?_, record source plan.script⟩
  rw [plan.exchanged_eq, second.2, a_material_transfer_retains_every_original_claim _ _ _ _ _ _ deliveryTransfer,
    first.2]
  exact a_material_transfer_retains_every_original_claim _ _ _ _ _ _ offerTransfer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
