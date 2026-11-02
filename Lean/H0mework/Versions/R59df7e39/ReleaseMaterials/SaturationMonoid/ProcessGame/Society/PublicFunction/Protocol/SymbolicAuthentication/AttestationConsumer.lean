import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationConsumer

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

inductive Rejection where
  | noAttestation | declined | notPayment
  deriving DecidableEq

inductive ResultData (Ballot Statement : Type) where
  | blocked (reason : Rejection)
  | confirmed (ballot : Ballot) (payment : Statement)
  deriving DecidableEq

abbrev Result := ResultData (OwnedAttestation.Ballot source)
  (Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))

/-- The explicit choice and the payment must be the very same request occurrence.
An unrelated labelled resource debit cannot assent to another payment. -/
def confirm (n position : Nat) : Result source :=
  match OwnedAttestation.issuedAt source input cut protocol rival vocabulary n position with
  | none => .blocked .noAttestation
  | some ballot =>
    if ballot.choice then
      match Settlement.issuedAt source.code.law
          (OwnedAttestation.execution source input cut protocol rival n).before
          (OwnedAttestation.execution source input cut protocol rival n).submitted position with
      | none => .blocked .notPayment
      | some statement => .confirmed ballot statement
    else .blocked .declined

theorem confirmation_has_both_independently_generated_origins
    (n position : Nat) (ballot : OwnedAttestation.Ballot source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (confirmed : confirm source input cut protocol rival vocabulary n position = .confirmed ballot payment) :
    OwnedAttestation.issuedAt source input cut protocol rival vocabulary n position = some ballot ∧
      ballot.choice = true ∧
      Settlement.issuedAt source.code.law
        (OwnedAttestation.execution source input cut protocol rival n).before
        (OwnedAttestation.execution source input cut protocol rival n).submitted position = some payment := by
  unfold confirm at confirmed
  split at confirmed <;> try contradiction
  rename_i generated actualBallot
  split at confirmed <;> try contradiction
  rename_i affirmative
  split at confirmed <;> try contradiction
  rename_i statement actualPayment
  cases confirmed
  exact ⟨actualBallot, affirmative, actualPayment⟩

theorem confirmed_payment_enters_the_original_finance_inventory_and_next
    (n position : Nat) (ballot : OwnedAttestation.Ballot source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (confirmed : confirm source input cut protocol rival vocabulary n position = .confirmed ballot payment) :
    let actual := OwnedAttestation.actual source input cut protocol rival
    let depth := source.history.length + 1 + (cut + n)
    ∃ item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument,
      item ∈ (Financial.inventoryAt actual.input (ProgrammeHistory.visitAt actual.input (depth + 1))).filterMap
        (Financial.InstructionOrigin.instruction? actual.input) ∧
      source.code.law.Valid item.before item.request ∧
      item.request.signer = ballot.actor ∧ ballot.actor = payment.debtor ∧
      0 < payment.amount ∧
      flowAt (source.code.law.actualDebit item.before item.request) payment.debtor payment.unit = payment.amount ∧
      flowAt (source.code.law.actualCredit item.before item.request) payment.creditor payment.unit = payment.amount ∧
      (source.code.law.step item.before item.request).claims payment.instrument payment.debtor payment.creditor =
        payment.priorClaim - payment.quantity ∧
      actual.currentAt (depth + 2) = source.code.law.next (actual.currentAt (depth + 1))
        (OwnedAttestation.execution source input cut protocol rival n).submitted := by
  obtain ⟨attested, _, settled⟩ := confirmation_has_both_independently_generated_origins
    source input cut protocol rival vocabulary n position ballot payment confirmed
  obtain ⟨site, ownItem, _, ownActual, _, ownSigner, _, _, _, _, _, ownActor, _, _⟩ :=
    OwnedAttestation.attested_has_owned_paid_origin source input cut protocol rival vocabulary n position ballot attested
  obtain ⟨item, actualItem, valid, positive, _, debit, credit, balance⟩ :=
    Settlement.issued_payment_has_actual_material_and_claim_effects source.code.law
      (OwnedAttestation.execution source input cut protocol rival n).before
      (OwnedAttestation.execution source input cut protocol rival n).submitted position payment settled
  obtain ⟨other, otherActual, _, _, _, _, signer, debtor, _⟩ :=
    Settlement.issued_has_actual_paid_origin source.code.law
      (OwnedAttestation.execution source input cut protocol rival n).before
      (OwnedAttestation.execution source input cut protocol rival n).submitted position payment settled
  have ownSame : ownItem = item := Option.some.inj (ownActual.symm.trans actualItem)
  have otherSame : other = item := Option.some.inj (otherActual.symm.trans actualItem)
  subst ownItem
  subst other
  refine ⟨item, ?_, valid, ownSigner.trans ownActor.symm, ?_, positive, debit, credit, balance, ?_⟩
  · rw [Native.both_consumers_use_the_same_actual_word]
    exact List.mem_of_getElem? actualItem
  · exact ownActor.trans (ownSigner.symm.trans (signer.trans debtor))
  · exact (OwnedAttestation.actual source input cut protocol rival).next_is_actual _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationConsumer
