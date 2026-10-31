import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Origins

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open ResponsibilityLifecycle
open Universal.Source.Program Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- An exercise of the financial source's native payment protocol, rather
than the existence of an outstanding claim somewhere in its account. -/
structure NativeMovementAt (leg : window.Leg) where
  origin : Financial.InstructionOrigin window.input
  receipt : Financial.Movement window.input origin
  same : receipt.instruction = leg.item.val

theorem an_original_plain_transfer_has_no_native_payment_receipt (leg : window.Leg) :
    ¬ Nonempty (NativeMovementAt window leg) := by
  rintro ⟨receipt⟩
  have operation := receipt.receipt.operation_exact
  rw [receipt.same,leg.operation] at operation
  cases kind : receipt.receipt.kind <;> simp only [kind] at operation <;> cases operation

/-- These are the source language's current debit-grant forms. A finite
claim alone is not a payment receipt and cannot be spent repeatedly. -/
inductive ExercisedGrant (leg : window.Leg) where
  | sourceSignature (signed : leg.item.val.request.signer = leg.sender)
  | sourceConsent (consent : leg.sender ∈ leg.item.val.request.consents)
  | nativePayment (receipt : NativeMovementAt window leg)
  | nativeMandate (event : Financial.Event window.input) (claim : Financial.IssuedClaim window.input)
      (mandate : (Financial.vocabulary window.input).MandateOriginAt event claim)

theorem an_unconsented_control_return_has_no_exercised_financial_grant
    (leg : window.Leg) (controlled : ControlledReturn leg) :
    ¬ Nonempty (ExercisedGrant window leg) := by
  rintro ⟨grant⟩
  cases grant with
  | sourceSignature signed => exact a_signed_gift_cannot_be_relabelled_as_this_private_taking leg signed controlled
  | sourceConsent consent => exact an_explicit_original_consent_is_not_erased leg consent controlled
  | nativePayment receipt => exact an_original_plain_transfer_has_no_native_payment_receipt window leg ⟨receipt⟩
  | nativeMandate _ _ impossible => cases impossible

theorem the_original_financial_claim_does_not_certify_that_this_cash_has_been_settled
    (leg : window.Leg) (_basis : NativeBacking window leg) :
    ¬ Nonempty (NativeMovementAt window leg) := an_original_plain_transfer_has_no_native_payment_receipt window leg

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
