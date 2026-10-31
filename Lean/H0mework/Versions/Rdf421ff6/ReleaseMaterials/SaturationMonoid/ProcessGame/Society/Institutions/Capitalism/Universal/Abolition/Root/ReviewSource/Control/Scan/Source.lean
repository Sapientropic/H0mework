import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Prepared
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Fees.Micro

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
  (prepared : Prepared input depth count prefixLimit renewalLimit located)

local notation "rawAt" => Material.rawAt input depth count prefixLimit renewalLimit

theorem paid_fee_target_is_the_original_microstep
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (paid : Review.PaymentAt input.law prepared.fee.request (rawAt current)) :
    rawAt (Fees.feeTarget current prepared.fee) = paid.microNext := by
  have original := Fees.the_original_primitive_fee_has_its_source_generated_effect
    input depth count prefixLimit renewalLimit current prepared.fee
  cases attempted : Review.attempt input.law prepared.fee.request prepared.fee.scope (rawAt current) with
  | inl actual =>
      dsimp only [Material.rawAt] at attempted
      rw [attempted] at original
      exact original.1
  | inr blocked => exact (blocked.request_is_actually_rejected paid.accepted).elim

/-- A proof trace over the original consumed fee inputs. This is neither
a second responsibility account nor a replacement physical history. -/
inductive RejectedPrefix (start : Physical.Cursor Party Good Port Technology Instrument) :
    Physical.Cursor Party Good Port Technology Instrument →
      List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument) → Nat → Type
  | nil : RejectedPrefix start start prepared.candidates 0
  | snoc {current pair remaining paidCount}
      (prior : RejectedPrefix start current (pair :: remaining) paidCount)
      (payment : Review.PaymentAt input.law prepared.fee.request (rawAt current))
      (issue : Material.Issue input depth count prefixLimit renewalLimit prepared.task
        (Fees.feeTarget current prepared.fee) pair)
      (observed : Material.inspect input depth count prefixLimit renewalLimit prepared.task
        (Fees.feeTarget current prepared.fee) pair = .refused issue) :
      RejectedPrefix start (Fees.feeTarget current prepared.fee) remaining (paidCount + 1)

namespace RejectedPrefix
variable {input depth count prefixLimit renewalLimit located prepared}
  {start current : Physical.Cursor Party Good Port Technology Instrument}
  {remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)}
  {paidCount : Nat}
  (prior : RejectedPrefix input depth count prefixLimit renewalLimit located prepared start current remaining paidCount)

def payments : Review.PaidMicroRun input.law prepared.fee.request (rawAt start) (rawAt current) paidCount := by
  induction prior with
  | nil => exact .nil _
  | @snoc current pair remaining paidCount prior payment issue observed previous =>
      rw [paid_fee_target_is_the_original_microstep input depth count prefixLimit renewalLimit located prepared current payment]
      exact .snoc previous payment

include prior

theorem original_candidate_inventory :
    paidCount + remaining.length = prepared.candidates.length := by
  induction prior with
  | nil => simp
  | snoc prior payment issue observed previous =>
      simp only [List.length_cons] at previous
      omega

theorem original_fee_inputs_are_the_entire_consumed_suffix :
    current.past = start.past ++ List.replicate paidCount (Compile.RawInput.primitive prepared.fee.request) := by
  induction prior with
  | nil => simp
  | snoc prior payment issue observed previous =>
      dsimp only [Fees.feeTarget, Fees.feeInput, Physical.next, Physical.receive]
      rw [previous, List.replicate_succ']
      exact List.append_assoc _ _ _

theorem actual_payment_bound : paidCount ≤
    min (Review.physicalBudget prepared.fee.request prepared.fee.scope (rawAt start))
      prepared.candidates.length := by
  have resource := prior.payments.count_le_original_budget prepared.fee.scope
  have inventory := prior.original_candidate_inventory
  exact le_min resource (by omega)

theorem actual_material_cost :
    (rawAt current).stock prepared.fee.scope.payer prepared.fee.scope.good +
        (paidCount : ℚ) * prepared.fee.scope.amount =
      (rawAt start).stock prepared.fee.scope.payer prepared.fee.scope.good :=
  prior.payments.material_balance prepared.fee.scope

theorem no_old_claim_or_period_is_replaced :
    (rawAt current).claims = (rawAt start).claims ∧
      (rawAt current).clock = (rawAt start).clock ∧ (rawAt current).round = (rawAt start).round :=
  ⟨prior.payments.original_claims_unchanged prepared.fee.scope, prior.payments.same_period⟩

end RejectedPrefix

structure PendingAt (start current : Physical.Cursor Party Good Port Technology Instrument) where
  private mk ::
  paidCount : Nat
  remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
  rejected : RejectedPrefix input depth count prefixLimit renewalLimit located prepared start current remaining paidCount

def initialPending (start : Physical.Cursor Party Good Port Technology Instrument) :
    PendingAt input depth count prefixLimit renewalLimit located prepared start start :=
  ⟨0, prepared.candidates, .nil⟩

namespace PendingAt
variable {input depth count prefixLimit renewalLimit located prepared}
  {start current : Physical.Cursor Party Good Port Technology Instrument}
  (pending : PendingAt input depth count prefixLimit renewalLimit located prepared start current)

def afterRejected
    (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
    (remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument))
    (head : pending.remaining = pair :: remaining)
    (payment : Review.PaymentAt input.law prepared.fee.request (rawAt current))
    (issue : Material.Issue input depth count prefixLimit renewalLimit prepared.task (Fees.feeTarget current prepared.fee) pair)
    (observed : Material.inspect input depth count prefixLimit renewalLimit prepared.task
      (Fees.feeTarget current prepared.fee) pair = .refused issue) :
    PendingAt input depth count prefixLimit renewalLimit located prepared start (Fees.feeTarget current prepared.fee) :=
  ⟨pending.paidCount + 1, remaining, .snoc (head ▸ pending.rejected) payment issue observed⟩

theorem refusal_consumes_a_paid_candidate_without_refund
    (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
    (remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument))
    (head : pending.remaining = pair :: remaining)
    (payment : Review.PaymentAt input.law prepared.fee.request (rawAt current))
    (issue : Material.Issue input depth count prefixLimit renewalLimit prepared.task (Fees.feeTarget current prepared.fee) pair)
    (observed : Material.inspect input depth count prefixLimit renewalLimit prepared.task
      (Fees.feeTarget current prepared.fee) pair = .refused issue) :
    (pending.afterRejected pair remaining head payment issue observed).paidCount = pending.paidCount + 1 ∧
      (pending.afterRejected pair remaining head payment issue observed).remaining.length + 1 = pending.remaining.length := by
  change pending.paidCount + 1 = pending.paidCount + 1 ∧ remaining.length + 1 = pending.remaining.length
  rw [head]
  exact ⟨rfl, rfl⟩

end PendingAt

#print axioms initialPending
#print axioms RejectedPrefix.actual_payment_bound
#print axioms RejectedPrefix.actual_material_cost
#print axioms PendingAt.refusal_consumes_a_paid_candidate_without_refund

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
