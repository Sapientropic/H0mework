import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationReception

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AvailabilityAudit

open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

inductive Status where
  | bodyAcknowledged | pending | noDelivery | attemptedButUnaccepted
  deriving DecidableEq

def attempted (horizon : Nat) (wire : AttestationTransport.Wire source) : Bool :=
  (List.range horizon).any fun n => decide (wire.sendCut < n) &&
    AttestationReception.deliveredAt source input cut protocol rival n wire.serial

theorem attempted_iff (horizon : Nat) (wire : AttestationTransport.Wire source) :
    attempted source input cut protocol rival horizon wire = true ↔
      ∃ n < horizon, wire.sendCut < n ∧ AttestationReception.deliveredAt source input cut protocol rival n wire.serial = true := by
  simp [attempted, List.any_eq_true, Bool.and_eq_true]

/-- An omission is an expired source message with no actual delivery attempt.
It identifies a communication obstruction, not an intrinsically faulty actor. -/
def classify (receiver : Fin source.code.sites) (horizon : Nat) (wire : AttestationTransport.Wire source) : Status :=
  if (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver horizon).receipts.any
      (fun receipt => decide (receipt.wire.ballot = wire.ballot)) then .bodyAcknowledged
  else if horizon ≤ wire.sendCut + law.maxDelay then .pending
  else if attempted source input cut protocol rival horizon wire then .attemptedButUnaccepted
  else .noDelivery

def rows (receiver : Fin source.code.sites) (horizon : Nat) : List (Nat × AttestationTransport.Wire source × Status) :=
  (List.range horizon).filterMap fun n =>
    match AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n with
    | none => none
    | some wire => if wire.recipient = receiver then
        some (n, wire, classify source input cut protocol rival vocabulary encoding law receiver horizon wire) else none

theorem every_row_has_actual_emission (receiver : Fin source.code.sites) (horizon n : Nat)
    (wire : AttestationTransport.Wire source) (status : Status)
    (inside : (n, wire, status) ∈ rows source input cut protocol rival vocabulary encoding law receiver horizon) :
    n < horizon ∧ AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n = some wire ∧
      wire.recipient = receiver ∧
      status = classify source input cut protocol rival vocabulary encoding law receiver horizon wire := by
  obtain ⟨index, bounded, generated⟩ := List.mem_filterMap.mp inside
  split at generated <;> try contradiction
  rename_i actual issued
  split at generated <;> try contradiction
  rename_i who
  have same := Option.some.inj generated
  cases same
  exact ⟨List.mem_range.mp bounded, issued, who, rfl⟩

theorem no_delivery_has_expired_and_has_no_actual_attempt
    (receiver : Fin source.code.sites) (horizon : Nat) (wire : AttestationTransport.Wire source)
    (missed : classify source input cut protocol rival vocabulary encoding law receiver horizon wire = .noDelivery) :
    wire.sendCut + law.maxDelay < horizon ∧
      (∀ n < horizon, wire.sendCut < n → AttestationReception.deliveredAt source input cut protocol rival n wire.serial ≠ true) ∧
      (∀ receipt ∈ (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver horizon).receipts,
        receipt.wire.ballot ≠ wire.ballot) := by
  unfold classify at missed
  split at missed <;> try contradiction
  rename_i unacknowledged
  split at missed <;> try contradiction
  rename_i expired
  split at missed <;> try contradiction
  rename_i unattempted
  refine ⟨by omega, ?_, ?_⟩
  · intro n bounded earlier actual
    exact unattempted ((attempted_iff source input cut protocol rival horizon wire).mpr ⟨n, bounded, earlier, actual⟩)
  · intro receipt inside same
    exact unacknowledged ((List.any_eq_true).mpr ⟨receipt, inside, decide_eq_true same⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AvailabilityAudit
