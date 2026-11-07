import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Lifecycle

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def reviewOperation (claim : Claim input depth count)
    (kind : Financial.ReviewKind input) (quantity : ℚ) : Operation Party Good Technology Instrument :=
  match kind with
  | .payment holder => .settle (claim.instrument input depth count)
      (claim.debtor input depth count) holder quantity
  | .assignment sender receiver => .assign (claim.instrument input depth count)
      (claim.debtor input depth count) sender receiver quantity

structure Review (claim : Claim input depth count) where
  private mk ::
  origin : ActualItem input depth count
  kind : Financial.ReviewKind input
  quantity : ℚ
  operation : (origin.instruction input depth count).request.operation =
    reviewOperation input depth count claim kind quantity
  accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
    (origin.instruction input depth count).request

def readReview (claim : Claim input depth count) (origin : ActualItem input depth count) :
    Option (Review input depth count claim) :=
  if accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request then
    match operation : (origin.instruction input depth count).request.operation with
    | .settle instrument debtor holder quantity =>
        if sameInstrument : instrument = claim.instrument input depth count then
          if sameDebtor : debtor = claim.debtor input depth count then
            some ⟨origin, .payment holder, quantity,
              by simpa only [reviewOperation, ← sameInstrument, ← sameDebtor] using operation, accepted⟩
          else none
        else none
    | .assign instrument debtor sender receiver quantity =>
        if sameInstrument : instrument = claim.instrument input depth count then
          if sameDebtor : debtor = claim.debtor input depth count then
            some ⟨origin, .assignment sender receiver, quantity,
              by simpa only [reviewOperation, ← sameInstrument, ← sameDebtor] using operation, accepted⟩
          else none
        else none
    | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present => none
  else none

def Review.fromHolder {claim : Claim input depth count}
    (review : Review input depth count claim) : Party :=
  match review.kind with | .payment holder => holder | .assignment sender _ => sender

def Review.allocated {claim : Claim input depth count}
    (review : Review input depth count claim) (balance : Financial.Balance input) (available : ℚ) : ℚ :=
  min available (balance (review.fromHolder input depth count))

def Review.after {claim : Claim input depth count}
    (review : Review input depth count claim) (balance : Financial.Balance input) (available : ℚ) :
    Financial.Balance input :=
  let used := review.allocated input depth count balance available
  match review.kind with
  | .payment holder => Financial.pay input balance holder used
  | .assignment sender receiver => Financial.assign input balance sender receiver used

def claimInitial : Claim input depth count → Financial.Balance input
  | .inl claim => Financial.initialBalance input claim
  | .inr claim => Financial.initialShare input claim.holder claim.quantity

/-- The original computable balance constructor keeps the same mathematical
singleton while allowing the actual native payment to compute its terminal. -/
theorem new_initial_balance_is_the_same_single (claim : NewClaim input depth count) :
    claimInitial input depth count (.inr claim) = Finsupp.single claim.holder claim.quantity := by
  exact Financial.initialShare_eq_single input claim.holder claim.quantity

/-- The original event is retained as an object, including its original
review origin and receipts. New reviews use only actual epoch inventory. -/
inductive Event where
  | legacy (event : Financial.Event input)
  | birth (claim : NewClaim input depth count)
  | review (claim : Claim input depth count) (receipt : Review input depth count claim)
      (before : Financial.Balance input) (remaining : ℚ)

def Event.claim : Event input depth count → Claim input depth count
  | .legacy event => .inl (event.claim input)
  | .birth claim => .inr claim
  | .review claim _ _ _ => claim

def Event.before : Event input depth count → Financial.Balance input
  | .legacy event => event.before input
  | .birth claim => claimInitial input depth count (.inr claim)
  | .review _ _ balance _ => balance

def Event.after : Event input depth count → Financial.Balance input
  | .legacy event => event.after input
  | .birth claim => claimInitial input depth count (.inr claim)
  | .review _ receipt balance remaining => receipt.after input depth count balance remaining

def Event.Lawful : Event input depth count → Prop
  | .legacy event => event.Lawful input
  | .birth _ => True
  | .review _ receipt balance remaining =>
      Financial.Nonnegative input balance ∧ 0 ≤ remaining ∧ remaining ≤ receipt.quantity

def Event.CommitmentAt : Event input depth count → Claim input depth count → Type
  | .legacy event, .inl claim => Financial.Event.CommitmentAt input event claim
  | .birth original, claim => PLift (Sum.inr original = claim)
  | _, _ => PEmpty

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance
