import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Scan.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Migration

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

/-- This material candidate is generated after its actual fee. Native
responsibility disposition remains a separate required source consumer. -/
structure CandidateAt (start current : Physical.Cursor Party Good Port Technology Instrument) where
  private mk ::
  before : Physical.Cursor Party Good Port Technology Instrument
  prior : PendingAt input depth count prefixLimit renewalLimit located prepared start before
  pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument
  remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
  head : prior.remaining = pair :: remaining
  payment : Review.PaymentAt input.law prepared.fee.request (rawAt before)
  actual : current = Fees.feeTarget before prepared.fee
  checked : Material.Checks input depth count prefixLimit renewalLimit prepared.task current pair
  observed : Material.inspect input depth count prefixLimit renewalLimit prepared.task current pair = .accepted checked

namespace CandidateAt
variable {input depth count prefixLimit renewalLimit located prepared}
  {start current : Physical.Cursor Party Good Port Technology Instrument}
  (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start current)

theorem original_command_feed : Actual.Migration.Checks input (Actual.origin input depth count)
    (rawAt current) (Actual.members input depth count) candidate.pair :=
  Material.checked_pair_feeds_the_original_compiler input depth count prefixLimit renewalLimit
    current prepared.task candidate.pair candidate.checked.1

def frontTarget := Physical.next (Physical.receive current (.migrate candidate.pair))

theorem candidate_front_uses_the_original_compiler_and_locks_its_tail :
    (Physical.stateAt input depth count prefixLimit renewalLimit candidate.frontTarget.past).raw =
      input.law.next (rawAt current) candidate.pair.1 ∧
    (Physical.stateAt input depth count prefixLimit renewalLimit candidate.frontTarget.past).phase = .renewal candidate.pair.2 := by
  have actual := Physical.consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit
    (Physical.receive current (.migrate candidate.pair))
  dsimp only [frontTarget]
  rw [actual]
  exact (Compile.a_checked_migration_executes_its_front_and_fixes_its_own_tail input depth count prefixLimit renewalLimit
    (Physical.stateAt input depth count prefixLimit renewalLimit current.past) candidate.pair candidate.original_command_feed).2.2

def payments : Review.PaidMicroRun input.law prepared.fee.request (rawAt start) (rawAt current)
    (candidate.prior.paidCount + 1) := by
  have endpoint : rawAt current = candidate.payment.microNext :=
    (congrArg (Material.rawAt input depth count prefixLimit renewalLimit) candidate.actual).trans
      (paid_fee_target_is_the_original_microstep input depth count prefixLimit renewalLimit located prepared candidate.before candidate.payment)
  rw [endpoint]
  exact .snoc candidate.prior.rejected.payments candidate.payment

theorem selected_check_has_real_original_payment :
    candidate.prior.paidCount + 1 ≤ Review.physicalBudget prepared.fee.request prepared.fee.scope (rawAt start) ∧
      (rawAt current).stock prepared.fee.scope.payer prepared.fee.scope.good +
        ((candidate.prior.paidCount + 1 : Nat) : ℚ) * prepared.fee.scope.amount =
          (rawAt start).stock prepared.fee.scope.payer prepared.fee.scope.good :=
  ⟨candidate.payments.count_le_original_budget prepared.fee.scope,
    candidate.payments.material_balance prepared.fee.scope⟩

end CandidateAt

variable {start current : Physical.Cursor Party Good Port Technology Instrument}
  (pending : PendingAt input depth count prefixLimit renewalLimit located prepared start current)
  (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument)
  (remaining : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument))
  (head : pending.remaining = pair :: remaining)

inductive FeeResult : Type
  | candidate (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start
      (Fees.feeTarget current prepared.fee))
  | rejected (payment : Review.PaymentAt input.law prepared.fee.request (rawAt current))
      (issue : Material.Issue input depth count prefixLimit renewalLimit prepared.task (Fees.feeTarget current prepared.fee) pair)
      (observed : Material.inspect input depth count prefixLimit renewalLimit prepared.task
        (Fees.feeTarget current prepared.fee) pair = .refused issue)
      (after : PendingAt input depth count prefixLimit renewalLimit located prepared start (Fees.feeTarget current prepared.fee))
      (exactAfter : after = pending.afterRejected pair remaining head payment issue observed)
  | blocked (obstruction : Review.Blockage input.law prepared.fee.request prepared.fee.scope (rawAt current))
      (attempted : Review.attempt input.law prepared.fee.request prepared.fee.scope (rawAt current) = .inr obstruction)

/-- The only candidate-checking branch follows a genuine successful fee
attempt and reads its literal original Physical target. -/
def afterFee : FeeResult input depth count prefixLimit renewalLimit located prepared pending pair remaining head :=
  match attempted : Review.attempt input.law prepared.fee.request prepared.fee.scope (rawAt current) with
  | .inr obstruction => .blocked obstruction attempted
  | .inl payment =>
      match observed : Material.inspect input depth count prefixLimit renewalLimit prepared.task
          (Fees.feeTarget current prepared.fee) pair with
      | .accepted checked => .candidate ⟨current, pending, pair, remaining, head, payment, rfl, checked, observed⟩
      | .refused issue => .rejected payment issue observed
          (pending.afterRejected pair remaining head payment issue observed) rfl

#print axioms afterFee
#print axioms CandidateAt.selected_check_has_real_original_payment
#print axioms CandidateAt.candidate_front_uses_the_original_compiler_and_locks_its_tail

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
