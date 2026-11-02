import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Access

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

structure Disposal where
  position : Entry input endpoint
  request : Request Party Good Port Technology Instrument
  good : Good
  allocations : List (Entry input endpoint) := []

namespace Disposal
variable (access : Access input endpoint) (disposal : Disposal input endpoint)

def allocationRecipient (fallback : Party) (item : Entry input endpoint) : Party :=
  match (item.raw input).request.operation with
  | .transfer _ recipient _ | .settle _ _ recipient _ | .assign _ _ _ recipient _ |
      .issue _ _ recipient _ => recipient
  | _ => fallback

def AuthorizedAllocation (holder : Party) (item : Entry input endpoint) : Prop :=
  input.law.Valid (item.raw input).before (item.raw input).request ∧
  match (item.raw input).request.operation with
  | .transfer sender recipient _ | .settle _ sender recipient _ =>
      (sender = holder ∨ ∃ port ∈ input.law.requiredPorts (item.raw input).before (item.raw input).request,
        input.law.controller (item.raw input).before.technology port = holder) ∧
      ∃ lot ∈ input.law.actualCredit (item.raw input).before (item.raw input).request, lot.1.1 = recipient ∧ 0 < lot.2
  | .issue _ issuer _ quantity => issuer = holder ∧ 0 < quantity
  | .assign _ _ sender _ quantity => sender = holder ∧ 0 < quantity
  | _ => False

instance (holder : Party) (item : Entry input endpoint) :
    Decidable (AuthorizedAllocation input endpoint holder item) := by
  unfold AuthorizedAllocation
  cases (item.raw input).request.operation <;> infer_instance

def AllocationChain : Party → Nat → List (Entry input endpoint) → Nat → Prop
  | _, lower, [], upper => lower ≤ upper
  | holder, lower, item :: tail, upper => lower ≤ item.position input ∧ item.position input < upper ∧
      AuthorizedAllocation input endpoint holder item ∧
      AllocationChain (allocationRecipient input endpoint holder item) (item.position input + 1) tail upper

instance (holder : Party) (lower upper : Nat) (allocations : List (Entry input endpoint)) :
    Decidable (AllocationChain input endpoint holder lower allocations upper) := by
  induction allocations generalizing holder lower with
  | nil => unfold AllocationChain; infer_instance
  | cons head tail ih =>
      unfold AllocationChain
      letI := ih (allocationRecipient input endpoint holder head) (head.position input + 1)
      infer_instance

def initialHolder : Party := match disposal.allocations with
  | [] => input.law.controller (disposal.position.raw input).before.technology access.port
  | first :: _ => input.law.controller (first.raw input).before.technology access.port

def holder : Party := disposal.allocations.foldl (allocationRecipient input endpoint)
  (disposal.initialHolder input endpoint access)

def Kind : Prop := match disposal.request.operation with
  | .use bearer goods kind => bearer = disposal.holder input endpoint access ∧
      (kind = .external ∨ kind = .investment) ∧ 0 < amount Good goods disposal.good
  | .transfer custodian recipient goods => recipient = disposal.holder input endpoint access ∧
      custodian ≠ recipient ∧ 0 < amount Good goods disposal.good
  | .assign _ _ sender recipient quantity => sender = disposal.holder input endpoint access ∧
      recipient ≠ sender ∧ 0 < quantity
  | _ => False

instance : Decidable (disposal.Kind input endpoint access) := by
  unfold Kind
  cases disposal.request.operation <;> infer_instance

def Checks : Prop :=
  privateControl input endpoint (disposal.position.raw input).before access.port ∧
  disposal.request.signer = disposal.holder input endpoint access ∧ disposal.request.consents = [] ∧
  input.law.Valid (disposal.position.raw input).before disposal.request ∧
  disposal.Kind input endpoint access ∧
  AllocationChain input endpoint (disposal.initialHolder input endpoint access) 0
    disposal.allocations (disposal.position.position input)

instance : Decidable (disposal.Checks input endpoint access) := by unfold Checks; infer_instance

end Disposal

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
