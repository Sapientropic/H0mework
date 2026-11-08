import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Preservation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Requests
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- The requester is an actual original delivery creditor, not a caller-supplied role list. -/
structure Role (basis : State) where
  private mk ::
  slot : {slot // slot∈basis.delivery.current.slots}
  holder : (Financial.Family.slotClaim Finance.sources slot.val).2.holder=receiver

def role? (basis : State) : Option (Role basis) :=
  basis.delivery.current.slots.attach.findSome? fun slot =>
    if holder : (Financial.Family.slotClaim Finance.sources slot.val).2.holder=receiver then
      some ⟨slot,holder⟩ else none

def registration : JointAction := ⟨receiver,[],.audit (native .common),[],.present⟩
def application : JointAction :=
  ⟨receiver,[],.audit (native .common),[],.use receiver [(.energy,1)] .investment⟩

structure Submission where
  nonce : Nat
  registration : JointAction
  payment : JointAction

def signed (round : Nat) : Submission := ⟨round,registration,application⟩
def Shape (submission : Submission) (before : Current) : Prop :=
  submission.nonce=before.round ∧ submission.registration=registration ∧ submission.payment=application
instance (submission : Submission) (before : Current) : Decidable (Shape submission before) := by
  unfold Shape;infer_instance

/-- Only public cursor and current round reach the request producer. -/
abbrev Source := Nat → Nat → Option Submission
def finite (count : Nat) : Source := fun cursor round => if cursor<count then some (signed round) else none

def prepare (scope : Scope) (before : Current) : List JointAction :=
  let required := max 3 (if before.stock supplier .labor<2 then before.stock receiver .energy+2 else 3)
  Supply.fill scope required .normal (⌈max 0 required/2⌉₊+1) before

def word (basis : State) (scope : Scope) (before : Current) (submission : Submission) : List JointAction :=
  if Shape submission before ∧ (role? basis).isSome then
    prepare scope before ++ [submission.registration,submission.payment]
  else []

structure Receipt (basis : State) (scope : Scope) (before : Current)
    (submission : Submission) (actions : List JointAction) where
  private mk ::
  role : Role basis
  shape : Shape submission before
  registration : {item // item∈(law scope).rawItems before actions}
  registrationRequest : registration.val.request=submission.registration
  registrationPaid : (law scope).Valid registration.val.before registration.val.request
  fee : {item // item∈(law scope).rawItems before actions}
  feeRequest : fee.val.request=submission.payment
  feePaid : (law scope).Valid fee.val.before fee.val.request
  ordered : registration.val.index<fee.val.index

def receipt? (basis : State) (scope : Scope) (before : Current) (submission : Submission)
    (actions : List JointAction) : Option (Receipt basis scope before submission actions) := do
  let role ← role? basis
  if shape : Shape submission before then
    let items := ((law scope).rawItems before actions).attach
    items.findSome? fun registration =>
      if original : registration.val.request=submission.registration ∧
          (law scope).Valid registration.val.before registration.val.request then
        items.findSome? fun fee =>
          if paid : fee.val.request=submission.payment ∧ (law scope).Valid fee.val.before fee.val.request ∧
              registration.val.index<fee.val.index then
            some ⟨role,shape,registration,original.1,original.2,fee,paid.1,paid.2.1,paid.2.2⟩
          else none
      else none
  else none

structure Window (basis : State) where
  private mk ::
  id : Nat
  newIdentity : basis.taskId < id
  task : PublicTaskSpec Actor Good
  before : Current
  submission : Submission
  actions : List JointAction
  receipt : Receipt basis basis.origin.scope before submission actions
  exactTask : task=⟨Production.code.need.slots,before.clock+2,before.clock+2+Production.code.need.window,
    Production.code.need.positive⟩

def openWindow (basis : State) (cursor : Nat) (before : Current) (submission : Submission)
    (actions : List JointAction) (receipt : Receipt basis basis.origin.scope before submission actions) : Window basis :=
  ⟨basis.taskId+1+cursor,by omega,⟨Production.code.need.slots,before.clock+2,
    before.clock+2+Production.code.need.window,Production.code.need.positive⟩,before,submission,actions,receipt,rfl⟩

theorem window_comes_from_the_actual_paid_request {basis : State} (window : Window basis) :
    window.receipt.fee.val∈(law basis.origin.scope).rawItems window.before window.actions ∧
    (law basis.origin.scope).Valid window.receipt.fee.val.before window.receipt.fee.val.request ∧
    window.receipt.fee.val.request=application ∧
    window.receipt.registration.val.index<window.receipt.fee.val.index :=
  ⟨window.receipt.fee.property,window.receipt.feePaid,
    window.receipt.feeRequest.trans window.receipt.shape.2.2,window.receipt.ordered⟩

theorem original_window_is_not_rewritten {basis : State} (window : Window basis) :
    basis.taskId<window.id ∧ window.task.earliest=window.before.clock+2 ∧
    window.task.deadline=window.before.clock+2+Production.code.need.window := by
  rw [window.exactTask]
  exact ⟨window.newIdentity,rfl,rfl⟩

theorem request_word_preserves_old_instruments (basis : State) (scope : Scope) (before : Current)
    (submission : Submission) : ∀ action∈word basis scope before submission,Historical action := by
  unfold word
  split
  · rename_i accepted
    intro action member
    rcases List.mem_append.mp member with supply | request
    · exact Supply.fill_historical _ _ _ _ _ action supply
    · rcases List.mem_cons.mp request with rfl | rest
      · rw [accepted.1.2.1];trivial
      · obtain rfl := List.mem_singleton.mp rest
        rw [accepted.1.2.2];trivial
  · simp

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Requests
