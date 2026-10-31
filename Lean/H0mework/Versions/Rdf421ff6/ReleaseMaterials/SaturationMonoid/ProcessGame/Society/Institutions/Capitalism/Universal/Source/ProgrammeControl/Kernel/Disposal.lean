import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Access

/-! A disposal right is checked by a finite local source command.  This is
an executable alternative at an original intermediate current, not a claim
that the command actually occurred.  Actual use, accumulation and financial
changes remain separate observations and may be zero. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

structure DisposalProposal where
  position : OriginalItem law current word
  request : Request Party Good Port Technology Instrument
  good : Good
  allocations : List (OriginalItem law current word) := []

namespace DisposalProposal
variable (access : AccessProposal law current word) (proposal : DisposalProposal law current word)

def allocationRecipient (fallback : Party) (item : OriginalItem law current word) : Party :=
  match item.val.request.operation with
  | .transfer _ recipient _ | .settle _ _ recipient _ | .assign _ _ _ recipient _ |
      .issue _ _ recipient _ => recipient
  | _ => fallback

def AuthorizedAllocation (holder : Party) (item : OriginalItem law current word) : Prop :=
  law.Valid item.val.before item.val.request ∧
  match item.val.request.operation with
  | .transfer sender recipient _ | .settle _ sender recipient _ =>
      (sender = holder ∨ ∃ port ∈ law.requiredPorts item.val.before item.val.request,
        law.controller item.val.before.technology port = holder) ∧
      ∃ lot ∈ law.actualCredit item.val.before item.val.request, lot.1.1 = recipient ∧ 0 < lot.2
  | .issue _ issuer _ quantity => issuer = holder ∧ 0 < quantity
  | .assign _ _ sender _ quantity => sender = holder ∧ 0 < quantity
  | _ => False

instance (holder : Party) (item : OriginalItem law current word) :
    Decidable (AuthorizedAllocation law current word holder item) := by
  unfold AuthorizedAllocation
  cases item.val.request.operation <;> infer_instance

def AllocationChain : Party → Nat → List (OriginalItem law current word) → Nat → Prop
  | _, lower, [], upper => lower ≤ upper
  | holder, lower, item :: tail, upper => lower ≤ item.val.index ∧ item.val.index < upper ∧
      AuthorizedAllocation law current word holder item ∧
      AllocationChain (allocationRecipient law current word holder item) (item.val.index + 1) tail upper

instance (holder : Party) (lower upper : Nat) (allocations : List (OriginalItem law current word)) :
    Decidable (AllocationChain law current word holder lower allocations upper) := by
  induction allocations generalizing holder lower with
  | nil => unfold AllocationChain; infer_instance
  | cons head tail ih =>
      unfold AllocationChain
      letI := ih (allocationRecipient law current word holder head) (head.val.index + 1)
      infer_instance

def initialHolder : Party := match proposal.allocations with
  | [] => law.controller proposal.position.val.before.technology access.port
  | first :: _ => law.controller first.val.before.technology access.port

def holder : Party := proposal.allocations.foldl (allocationRecipient law current word)
  (proposal.initialHolder law current word access)

def allocationChecks : Prop := AllocationChain law current word
  (proposal.initialHolder law current word access) 0 proposal.allocations proposal.position.val.index

instance : Decidable (proposal.allocationChecks law current word access) := by
  unfold allocationChecks
  infer_instance

def DisposalKind : Prop := match proposal.request.operation with
  | .use bearer goods kind => bearer = proposal.holder law current word access ∧
      (kind = .external ∨ kind = .investment) ∧ 0 < amount Good goods proposal.good
  | .transfer custodian recipient goods => recipient = proposal.holder law current word access ∧
      custodian ≠ recipient ∧ 0 < amount Good goods proposal.good
  | .assign _ _ holder recipient quantity => holder = proposal.holder law current word access ∧
      recipient ≠ holder ∧ 0 < quantity
  | _ => False

instance : Decidable (proposal.DisposalKind law current word access) := by
  unfold DisposalKind
  cases proposal.request.operation <;> infer_instance

def Checks : Prop :=
  PrivatePhase law proposal.position.val.before access.port access.recipient ∧
  proposal.request.signer = proposal.holder law current word access ∧
  proposal.request.consents = [] ∧
  law.Valid proposal.position.val.before proposal.request ∧
  proposal.DisposalKind law current word access ∧ proposal.allocationChecks law current word access

instance : Decidable (proposal.Checks law current word access) := by unfold Checks; infer_instance
end DisposalProposal

#print axioms DisposalProposal.instDecidableChecks

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel
