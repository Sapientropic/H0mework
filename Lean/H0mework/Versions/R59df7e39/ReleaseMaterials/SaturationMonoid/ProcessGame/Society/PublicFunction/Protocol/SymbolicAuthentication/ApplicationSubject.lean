import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AccountableDecision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ApplicationSubject

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

abbrev Subject := OwnedAttestation.Ballot source ×
  Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument)

def baseRound : Nat := source.code.initial.round + source.history.length + 2 + cut
def originCut (scope : Scope) : Nat := scope.epoch - baseRound source cut

/-- Application names use the already existing native settlement scope. The
resolver reads that actual source occurrence; it does not decode a supplied body. -/
def resolve (scope : Scope) : Option (Subject source) :=
  if scope.phase ≠ 0 then none
  else if ¬ baseRound source cut ≤ scope.epoch then none
  else match AttestationConsumer.confirm source input cut protocol rival vocabulary
      (originCut source cut scope) scope.instanceId with
    | .blocked _ => none
    | .confirmed ballot payment =>
      if ballot.scope = scope ∧ payment.scope = scope then some (ballot, payment) else none

def verify (scope : Scope) (candidate : Subject source) : Bool :=
  decide (resolve source input cut protocol rival vocabulary scope = some candidate)

theorem resolved_has_original_confirmation_and_exact_address (scope : Scope) (subject : Subject source)
    (resolved : resolve source input cut protocol rival vocabulary scope = some subject) :
    AttestationConsumer.confirm source input cut protocol rival vocabulary
        (originCut source cut scope) scope.instanceId = .confirmed subject.1 subject.2 ∧
      subject.1.scope = scope ∧ subject.2.scope = scope ∧ scope.phase = 0 ∧
      baseRound source cut + originCut source cut scope = scope.epoch := by
  unfold resolve at resolved
  split at resolved <;> try contradiction
  rename_i phase
  split at resolved <;> try contradiction
  rename_i bounded
  split at resolved <;> try contradiction
  rename_i ballot payment actual
  split at resolved <;> try contradiction
  rename_i aligned
  cases Option.some.inj resolved
  refine ⟨actual, aligned.1, aligned.2, by omega, ?_⟩
  unfold originCut
  omega

theorem resolved_origin_coordinates (scope : Scope) (subject : Subject source)
    (resolved : resolve source input cut protocol rival vocabulary scope = some subject) :
    subject.1.cut = originCut source cut scope ∧ subject.1.position = scope.instanceId := by
  have original := (resolved_has_original_confirmation_and_exact_address source input cut protocol rival vocabulary scope subject resolved).1
  have owned := (AttestationConsumer.confirmation_has_both_independently_generated_origins source input cut protocol rival vocabulary
    (originCut source cut scope) scope.instanceId subject.1 subject.2 original).1
  obtain ⟨_, _, _, _, _, _, _, _, coordinates, address, _⟩ := OwnedAttestation.attested_has_owned_paid_origin source input cut protocol rival vocabulary
    (originCut source cut scope) scope.instanceId subject.1 owned
  exact ⟨coordinates, address⟩

theorem resolved_execution_has_the_original_named_round (scope : Scope) (subject : Subject source)
    (resolved : resolve source input cut protocol rival vocabulary scope = some subject) :
    (OwnedAttestation.execution source input cut protocol rival (originCut source cut scope)).before.round = scope.epoch := by
  have address := (resolved_has_original_confirmation_and_exact_address source input cut protocol rival vocabulary scope subject resolved).2.2.2.2
  change ((OwnedAttestation.actual source input cut protocol rival).currentAt
    (source.history.length + 1 + (cut + originCut source cut scope) + 1)).round = _
  rw [Machine.current_round]
  change source.code.initial.round + (source.history.length + 1 + (cut + originCut source cut scope) + 1) = _
  unfold baseRound at address
  omega

def precedes (subject : Subject source) (ballot : OwnedAttestation.Ballot source) : Prop :=
  subject.1.cut < ballot.cut ∨ subject.1.cut = ballot.cut ∧ subject.1.position ≤ ballot.position

instance (subject : Subject source) (ballot : OwnedAttestation.Ballot source) : Decidable (precedes source subject ballot) := by
  unfold precedes
  infer_instance

/-- A later owned vote can refer to the original subject without repeating its
payment. Same-cut references must respect the actual request order. -/
def bind (ballot : OwnedAttestation.Ballot source) : Option (Subject source) :=
  if OwnedAttestation.verify source input cut protocol rival vocabulary ballot ≠ true then none
  else match resolve source input cut protocol rival vocabulary ballot.scope with
    | none => none
    | some subject => if precedes source subject ballot then some subject else none

def bindAt (scope : Scope) (ballot : OwnedAttestation.Ballot source) : Option (Subject source) :=
  if ballot.scope = scope then bind source input cut protocol rival vocabulary ballot else none

theorem bound_vote_is_authenticated_causal_and_on_the_same_subject
    (scope : Scope) (ballot : OwnedAttestation.Ballot source) (subject : Subject source)
    (bound : bindAt source input cut protocol rival vocabulary scope ballot = some subject) :
    ballot.scope = scope ∧ OwnedAttestation.verify source input cut protocol rival vocabulary ballot = true ∧
      resolve source input cut protocol rival vocabulary scope = some subject ∧ precedes source subject ballot := by
  unfold bindAt at bound
  split at bound <;> try contradiction
  rename_i same
  unfold bind at bound
  split at bound <;> try contradiction
  rename_i authenticated
  split at bound <;> try contradiction
  rename_i generated actual
  split at bound <;> try contradiction
  rename_i causal
  cases Option.some.inj bound
  exact ⟨same, by simpa using authenticated, same ▸ actual, causal⟩

variable (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

abbrev observed (receiver : Fin source.code.sites) (count : Nat) :=
  AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count

def received (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) : AttestationReception.Receiver source :=
  let actual := observed source input cut protocol rival vocabulary encoding law receiver count
  ⟨actual.receipts.filter (fun receipt => (bindAt source input cut protocol rival vocabulary scope receipt.wire.ballot).isSome), actual.audit⟩

theorem received_members_have_the_original_receipt_and_subject
    (receiver : Fin source.code.sites) (count : Nat) (scope : Scope)
    (receipt : AttestationReception.Receipt source)
    (inside : receipt ∈ (received source input cut protocol rival vocabulary encoding law receiver count scope).receipts) :
    receipt ∈ (observed source input cut protocol rival vocabulary encoding law receiver count).receipts ∧
      ∃ subject, bindAt source input cut protocol rival vocabulary scope receipt.wire.ballot = some subject := by
  obtain ⟨present, bound⟩ := List.mem_filter.mp inside
  exact ⟨present, Option.isSome_iff_exists.mp bound⟩

theorem support_is_from_the_actual_receiver
    (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) (value : Bool) :
    BallotQuorum.support source (received source input cut protocol rival vocabulary encoding law receiver count scope) scope value ⊆
      BallotQuorum.support source (observed source input cut protocol rival vocabulary encoding law receiver count) scope value := by
  intro key present
  obtain ⟨receipt, inside, same, choice, keyEq⟩ := (BallotQuorum.mem_support_iff source _ scope value key).mp present
  exact (BallotQuorum.mem_support_iff source _ scope value key).mpr
    ⟨receipt, (received_members_have_the_original_receipt_and_subject source input cut protocol rival vocabulary encoding law
      receiver count scope receipt inside).1, same, choice, keyEq⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ApplicationSubject
