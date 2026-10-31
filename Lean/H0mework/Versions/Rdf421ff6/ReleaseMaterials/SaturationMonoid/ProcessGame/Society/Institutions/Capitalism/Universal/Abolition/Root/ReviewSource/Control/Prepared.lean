import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.Parse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (located : Located input depth count prefixLimit renewalLimit)

/-- Only original task syntax and a parsed raw fee are admitted here.
There is no material plan, service coverage, target, or future in this value. -/
structure Prepared where
  private mk ::
  task : Material.OriginalTask input depth count
  feeScope : Review.FeeScope located.registration.code.fee
  decoded : Fees.scope? located.registration.code.fee = some feeScope

namespace Prepared
variable {input depth count prefixLimit renewalLimit located}
  (prepared : Prepared input depth count prefixLimit renewalLimit located)

def fee := (Fees.originalCode prepared.feeScope).withoutConsents

theorem fee_uses_the_original_amount_without_private_consent :
    prepared.fee.request.operation = located.registration.code.fee.operation ∧
      prepared.fee.request.signer = located.registration.code.fee.signer ∧
      prepared.fee.request.consents = [] ∧
      prepared.fee.scope.amount = prepared.feeScope.amount ∧ 0 < prepared.fee.scope.amount :=
  Fees.its_independent_fee_keeps_operation_signer_and_positive_amount prepared.feeScope

def candidates (_prepared : Prepared input depth count prefixLimit renewalLimit located) :=
  located.registration.code.candidates prefixLimit renewalLimit

theorem task_and_window_are_the_original_declaration :
    taskOfPayload (originalPayload input (Settlement.committedVisit input depth count).current) =
      some prepared.task.val := prepared.task.property

end Prepared

inductive PreparationIssue : Type
  | taskUndisclosed (blocker : DisclosureBlockerAt input (Settlement.committedVisit input depth count).current)
  | invalidFee (original : Fees.scope? located.registration.code.fee = none)
      (noPositiveFeeScope : IsEmpty (Review.FeeScope located.registration.code.fee))

inductive Preparation : Type
  | ready (prepared : Prepared input depth count prefixLimit renewalLimit located)
  | stopped (issue : PreparationIssue input depth count prefixLimit renewalLimit located)

def prepare : Preparation input depth count prefixLimit renewalLimit located :=
  match discloseTask input (Settlement.committedVisit input depth count).current with
  | .unresolved blocker => .stopped (.taskUndisclosed blocker)
  | .declared task original =>
      match Fees.parse located.registration.code.fee with
      | .accepted scope decoded => .ready ⟨⟨task, original⟩, scope, decoded⟩
      | .rejected original empty => .stopped (.invalidFee original empty)

theorem missing_task_retains_the_original_responsibility
    (blocker : DisclosureBlockerAt input (Settlement.committedVisit input depth count).current) :
    blocker.actualNextEntry input = ProgrammeSource.targetEntry input
      (Settlement.committedVisit input depth count).current .inherited :=
  blocker.same_row_and_actual_next input

#print axioms prepare
#print axioms Prepared.fee_uses_the_original_amount_without_private_consent
#print axioms Prepared.task_and_window_are_the_original_declaration

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
