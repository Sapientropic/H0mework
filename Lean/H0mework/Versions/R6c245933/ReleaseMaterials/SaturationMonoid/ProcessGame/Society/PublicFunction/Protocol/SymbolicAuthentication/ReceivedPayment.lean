import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationReception
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationConsumer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedPayment

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open AttestationTransport

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : Encoding source) (law : AttestationReception.ReceptionLaw source)

def support (observed : AttestationReception.Receiver source) (scope : Scope) : Finset (Fin source.code.sites) :=
  ((observed.receipts.filter fun receipt => decide
    (receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = true)).map
      fun receipt => receipt.wire.ballot.key).toFinset

def paymentAt (scope : Scope) (receipt : AttestationReception.Receipt source) :
    Option (AttestationReception.Receipt source × Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument)) :=
  match AttestationConsumer.confirm source input cut protocol rival vocabulary
      receipt.wire.ballot.cut receipt.wire.ballot.position with
  | .blocked _ => none
  | .confirmed ballot payment =>
      if ballot = receipt.wire.ballot ∧ ballot.scope = scope ∧ payment.scope = scope then some (receipt, payment) else none

inductive ResultData (Receipt Statement : Type) where
  | blocked
  | confirmed (receipt : Receipt) (payment : Statement)
  deriving DecidableEq

abbrev Result := ResultData (AttestationReception.Receipt source)
  (Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))

/-- The producer consumes its generated receipt history, not a caller certificate.
Threshold support and the payer's own received payment occurrence are both required. -/
def confirm (receiver : Fin source.code.sites) (horizon : Nat) (scope : Scope) (threshold : Nat) : Result source :=
  let observed := AttestationReception.run source input cut protocol rival vocabulary encoding law receiver horizon
  if threshold = 0 then .blocked
  else if (support source observed scope).card < threshold then .blocked
  else match (observed.receipts.filterMap (paymentAt source input cut protocol rival vocabulary scope))[0]? with
    | none => .blocked
    | some (receipt, payment) => .confirmed receipt payment

theorem confirmation_requires_actual_receipt_quorum_and_the_same_payment
    (receiver : Fin source.code.sites) (horizon : Nat) (scope : Scope) (threshold : Nat)
    (receipt : AttestationReception.Receipt source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (confirmed : confirm source input cut protocol rival vocabulary encoding law receiver horizon scope threshold =
      .confirmed receipt payment) :
    receipt ∈ (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver horizon).receipts ∧
      0 < threshold ∧ threshold ≤ (support source
        (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver horizon) scope).card ∧
      AttestationConsumer.confirm source input cut protocol rival vocabulary receipt.wire.ballot.cut receipt.wire.ballot.position =
        .confirmed receipt.wire.ballot payment ∧ receipt.wire.ballot.scope = scope ∧ payment.scope = scope := by
  unfold confirm at confirmed
  dsimp only at confirmed
  split at confirmed <;> try contradiction
  rename_i positive
  split at confirmed <;> try contradiction
  rename_i enough
  split at confirmed <;> try contradiction
  rename_i actualReceipt actualPayment first
  cases confirmed
  obtain ⟨original, inside, produced⟩ := List.mem_filterMap.mp (List.mem_of_getElem? first)
  unfold paymentAt at produced
  split at produced <;> try contradiction
  rename_i ballot statement actual
  split at produced <;> try contradiction
  rename_i aligned
  have pair := Option.some.inj produced
  cases pair
  exact ⟨inside, Nat.pos_of_ne_zero positive, by omega, aligned.1 ▸ actual,
    aligned.1 ▸ aligned.2.1, aligned.2.2⟩

theorem confirmation_has_real_communication_and_original_next
    (receiver : Fin source.code.sites) (horizon : Nat) (scope : Scope) (threshold : Nat)
    (receipt : AttestationReception.Receipt source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (confirmed : confirm source input cut protocol rival vocabulary encoding law receiver horizon scope threshold =
      .confirmed receipt payment) :
    AttestationReception.deliveredAt source input cut protocol rival receipt.delivery receipt.wire.serial = true ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary receipt.wire.ballot = true ∧
      receipt.wire.ballot.cut < receipt.wire.sendCut ∧ receipt.wire.sendCut < receipt.delivery ∧
      (OwnedAttestation.actual source input cut protocol rival).currentAt
          (source.history.length + 1 + (cut + receipt.wire.ballot.cut) + 2) =
        source.code.law.next ((OwnedAttestation.actual source input cut protocol rival).currentAt
          (source.history.length + 1 + (cut + receipt.wire.ballot.cut) + 1))
          (execution source input cut protocol rival receipt.wire.ballot.cut).submitted := by
  obtain ⟨inside, _, _, _, _, _⟩ := confirmation_requires_actual_receipt_quorum_and_the_same_payment
    source input cut protocol rival vocabulary encoding law receiver horizon scope threshold receipt payment confirmed
  obtain ⟨authenticated, delivered, _, _, earlier, _⟩ := AttestationReception.receipts_have_actual_communication
    source input cut protocol rival vocabulary encoding law receiver horizon receipt inside
  obtain ⟨_, _, owned, before, _⟩ := authenticated_wire_has_an_earlier_owned_paid_statement
    source input cut protocol rival vocabulary encoding receipt.wire authenticated
  exact ⟨delivered, owned, before, earlier, (OwnedAttestation.actual source input cut protocol rival).next_is_actual _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedPayment
