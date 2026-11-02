import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptProgress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AvailabilityAudit
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Service

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationDuty

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle ComplementObservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source)

abbrev emitted (n : Nat) := AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n
abbrev Content := OwnedAttestation.Ballot source × Fin source.code.sites
def content (wire : AttestationTransport.Wire source) : Content source := (wire.ballot, wire.recipient)

/-- A machine transport role tracks unconfirmed content. This is neither human
consent nor a claim that the emitting site controls subsequent delivery. -/
structure Emission where
  private mk ::
  send : Nat
  wire : AttestationTransport.Wire source
  generated : emitted source input cut protocol rival vocabulary encoding send = some wire

def issue (n : Nat) : Option (Emission source input cut protocol rival vocabulary encoding) :=
  match actual : emitted source input cut protocol rival vocabulary encoding n with
  | none => none
  | some wire => some ⟨n, wire, actual⟩

/-- Retransmission continues the first content duty; it does not allocate another. -/
def birth (n : Nat) : Option (Emission source input cut protocol rival vocabulary encoding) :=
  match issue source input cut protocol rival vocabulary encoding n with
  | none => none
  | some emission =>
    if ((List.range n).filterMap (fun earlier => emitted source input cut protocol rival vocabulary encoding earlier)).any
        (fun previous => decide (content source previous = content source emission.wire)) then none
    else some emission

def origins (horizon : Nat) := (List.range horizon).filterMap
  (birth source input cut protocol rival vocabulary encoding)

def birthWire (n : Nat) : Option (AttestationTransport.Wire source) :=
  (emitted source input cut protocol rival vocabulary encoding n).bind fun wire =>
    if ((List.range n).filterMap (fun earlier => emitted source input cut protocol rival vocabulary encoding earlier)).any
        (fun previous => decide (content source previous = content source wire)) then none else some wire

theorem birth_wire_projection (n : Nat) :
    (birth source input cut protocol rival vocabulary encoding n).map (fun emission => emission.wire) =
      birthWire source input cut protocol rival vocabulary encoding n := by
  have raw : (issue source input cut protocol rival vocabulary encoding n).map (fun emission => emission.wire) =
      emitted source input cut protocol rival vocabulary encoding n := by
    unfold issue
    split <;> simp_all only [Option.map_none, Option.map_some]
  unfold birth
  cases actual : issue source input cut protocol rival vocabulary encoding n with
  | none =>
    rw [actual] at raw
    simp only [Option.map_none] at raw
    simp only [birthWire, ← raw, Option.map_none, Option.bind_none]
  | some emission =>
    rw [actual] at raw
    simp only [Option.map_some] at raw
    simp only [birthWire, ← raw, Option.bind_some]
    split_ifs <;> rfl

theorem origins_wire_projection (horizon : Nat) :
    (origins source input cut protocol rival vocabulary encoding horizon).map (fun emission => emission.wire) =
      (List.range horizon).filterMap (birthWire source input cut protocol rival vocabulary encoding) := by
  simp only [origins, List.map_filterMap]
  congr 1
  funext n
  exact birth_wire_projection source input cut protocol rival vocabulary encoding n

theorem birth_is_first (n : Nat) (emission : Emission source input cut protocol rival vocabulary encoding)
    (born : birth source input cut protocol rival vocabulary encoding n = some emission) :
    emission.send = n ∧ ∀ earlier < n, ∀ previous,
      emitted source input cut protocol rival vocabulary encoding earlier = some previous →
      content source previous ≠ content source emission.wire := by
  unfold birth at born
  split at born <;> try contradiction
  rename_i candidate actual
  split_ifs at born with old
  have same := Option.some.inj born
  subst emission
  have identity : candidate.send = n := by
    unfold issue at actual
    split at actual <;> try contradiction
    cases actual
    rfl
  refine ⟨identity, ?_⟩
  intro earlier bounded previous generated same
  apply old
  exact List.any_eq_true.mpr ⟨previous,
    List.mem_filterMap.mpr ⟨earlier, List.mem_range.mpr bounded, generated⟩, decide_eq_true same⟩

theorem one_content_has_one_birth (n m : Nat)
    (one two : Emission source input cut protocol rival vocabulary encoding)
    (first : birth source input cut protocol rival vocabulary encoding n = some one)
    (second : birth source input cut protocol rival vocabulary encoding m = some two)
    (same : content source one.wire = content source two.wire) : n = m := by
  obtain ⟨oneAt, noEarlierOne⟩ := birth_is_first source input cut protocol rival vocabulary encoding n one first
  obtain ⟨twoAt, noEarlierTwo⟩ := birth_is_first source input cut protocol rival vocabulary encoding m two second
  have originalOne := one.generated
  have originalTwo := two.generated
  rw [oneAt] at originalOne
  rw [twoAt] at originalTwo
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · exact noEarlierTwo n before one.wire originalOne same
  · exact noEarlierOne m after two.wire originalTwo same.symm

variable (law : AttestationReception.ReceptionLaw source)

abbrev received (n : Nat) (receiver : Fin source.code.sites) :=
  AttestationReception.run source input cut protocol rival vocabulary encoding law receiver n

def Acknowledged (emission : Emission source input cut protocol rival vocabulary encoding) (count : Nat) : Prop :=
  ∃ receipt ∈ (received source input cut protocol rival vocabulary encoding law count emission.wire.recipient).receipts,
    receipt.wire.ballot = emission.wire.ballot

instance (emission : Emission source input cut protocol rival vocabulary encoding) (count : Nat) :
    Decidable (Acknowledged source input cut protocol rival vocabulary encoding law emission count) := by
  unfold Acknowledged
  infer_instance

theorem acknowledgment_has_original_paid_communication
    (emission : Emission source input cut protocol rival vocabulary encoding) (count : Nat)
    (ack : Acknowledged source input cut protocol rival vocabulary encoding law emission count) :
    ∃ receipt, receipt ∈ (received source input cut protocol rival vocabulary encoding law count emission.wire.recipient).receipts ∧
      receipt.wire.ballot = emission.wire.ballot ∧
      AttestationTransport.verify source input cut protocol rival vocabulary encoding receipt.wire = true ∧
      AttestationReception.deliveredAt source input cut protocol rival receipt.delivery receipt.wire.serial = true ∧
      receipt.wire.recipient = emission.wire.recipient ∧ receipt.delivery < count := by
  obtain ⟨receipt, inside, same⟩ := ack
  obtain ⟨auth, delivered, _, recipient, _, bounded, _⟩ := AttestationReception.receipts_have_actual_communication
    source input cut protocol rival vocabulary encoding law emission.wire.recipient count receipt inside
  exact ⟨receipt, inside, same, auth, delivered, recipient, bounded⟩

theorem acknowledged_is_preserved (emission : Emission source input cut protocol rival vocabulary encoding)
    (n m : Nat) (later : n ≤ m)
    (ack : Acknowledged source input cut protocol rival vocabulary encoding law emission n) :
    Acknowledged source input cut protocol rival vocabulary encoding law emission m := by
  obtain ⟨receipt, inside, same⟩ := ack
  exact ⟨receipt, (ReceiptProgress.receipts_are_preserved source input cut protocol rival vocabulary encoding law
    emission.wire.recipient n m later).subset inside, same⟩

structure Event where
  emission : Emission source input cut protocol rival vocabulary encoding
  count : Nat

structure AdmissionAt (event : Event source input cut protocol rival vocabulary encoding) (body : Content source) where
  registration : Native.RegistrationReceipt (OwnedAttestation.actual source input cut protocol rival)
  at_emission : event.count = event.emission.send + 1
  original : body = content source event.emission.wire

structure AssumptionAt (bearer : Fin source.code.sites)
    (event : Event source input cut protocol rival vocabulary encoding) (body : Content source)
    extends AdmissionAt source input cut protocol rival vocabulary encoding event body where
  machine_role : bearer = event.emission.wire.ballot.key

def vocabularyLaw : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event source input cut protocol rival vocabulary encoding
  Content := Content source
  Residual := Content source
  Bearer := Fin source.code.sites
  ProtectedInterest := Fin source.code.sites
  Scope := Content source
  Lineage := Content source
  Incidence := Content source
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (content source event.emission.wire) (content source event.emission.wire)
  sourceIncidence := fun event => content source event.emission.wire
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := fun _ _ => Empty
  ActiveDependencyAt := AdmissionAt source input cut protocol rival vocabulary encoding
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt source input cut protocol rival vocabulary encoding
  AcceptedAt := AssumptionAt source input cut protocol rival vocabulary encoding
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun body scope => PLift (body = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := fun event body scope => PLift (body = content source event.emission.wire ∧ scope = body ∧
    ¬ Acknowledged source input cut protocol rival vocabulary encoding law event.emission event.count)
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := fun event body scope => PLift (body = content source event.emission.wire ∧ scope = body ∧
    Acknowledged source input cut protocol rival vocabulary encoding law event.emission event.count)
  WaivedAt := fun _ _ _ => Empty
  InvalidatedAt := fun _ _ _ => Empty
  AbandonedAt := fun _ _ _ => Empty
  ImpossibleResidueAcceptedAt := fun _ _ _ => Empty
  SupersessionAt := fun _ _ _ _ _ _ _ => Empty
  ReopenAt := fun _ _ _ _ _ _ _ => Empty
  JurisdictionEndedAt := fun _ _ _ => Empty
  ConsentRevokedAt := fun _ _ _ => Empty
  CapacityReleasedAt := fun _ _ _ => Empty
  UpperRouteAt := fun _ _ _ => Empty
  NextActorSignal := Nat
  AgeSignal := Nat
  TransferOfferSignal := Empty

abbrev V := vocabularyLaw source input cut protocol rival vocabulary encoding law

def admission (emission : Emission source input cut protocol rival vocabulary encoding) :
    NativeAdmissionPayload (V source input cut protocol rival vocabulary encoding law) where
  sourceEvent := ⟨emission, emission.send + 1⟩
  content := content source emission.wire
  residual := content source emission.wire
  bearer := emission.wire.ballot.key
  beneficiary := emission.wire.recipient
  scope := content source emission.wire
  lineage := content source emission.wire
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .activeDependency ⟨Native.registered _, rfl, rfl⟩
  authority := ⟨Native.registered _, rfl, rfl⟩
  assumption := .accepted ⟨⟨Native.registered _, rfl, rfl⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

abbrev obligation (emission : Emission source input cut protocol rival vocabulary encoding) :=
  (admission source input cut protocol rival vocabulary encoding law emission).toObligation

structure Review (duty : AdmittedObligation (V source input cut protocol rival vocabulary encoding law)) where
  emission : Emission source input cut protocol rival vocabulary encoding
  count : Nat
  content_eq : duty.content = content source emission.wire
  scope_eq : duty.scope = duty.content
  original : duty.admission.sourceEvent.emission = emission

def reviewSource {duty : AdmittedObligation (V source input cut protocol rival vocabulary encoding law)}
    (event : Review source input cut protocol rival vocabulary encoding law duty) :
    Event source input cut protocol rival vocabulary encoding := ⟨event.emission, event.count⟩

def disposition {duty : AdmittedObligation (V source input cut protocol rival vocabulary encoding law)}
    (event : Review source input cut protocol rival vocabulary encoding law duty) :
    BoundaryDisposition (V source input cut protocol rival vocabulary encoding law) duty
      (reviewSource source input cut protocol rival vocabulary encoding law event) :=
  if ack : Acknowledged source input cut protocol rival vocabulary encoding law event.emission event.count then
    .terminal (.final (.fulfilled ⟨event.content_eq, event.scope_eq, ack⟩))
  else .carry (.maintained ⟨event.content_eq, event.scope_eq, ack⟩)

def process : NativeResponsibilityProcess (V source input cut protocol rival vocabulary encoding law) where
  AdmissionEvent := Emission source input cut protocol rival vocabulary encoding
  admissionPayload := admission source input cut protocol rival vocabulary encoding law
  BoundaryEvent := Review source input cut protocol rival vocabulary encoding law
  boundarySource := reviewSource source input cut protocol rival vocabulary encoding law
  boundary_anchor_eq := by
    intro duty event
    change MinimalRegistrableSourceAnchor.canonical (content source event.emission.wire) _ =
      MinimalRegistrableSourceAnchor.canonical (content source duty.admission.sourceEvent.emission.wire) _
    rw [event.original]
    rfl
  boundary_incidence_eq := by
    intro duty event
    change content source event.emission.wire = content source duty.admission.sourceEvent.emission.wire
    rw [event.original]
  boundaryDisposition := disposition source input cut protocol rival vocabulary encoding law
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def review (emission : Emission source input cut protocol rival vocabulary encoding) (count : Nat) :
    Review source input cut protocol rival vocabulary encoding law
      (obligation source input cut protocol rival vocabulary encoding law emission) := ⟨emission, count, rfl, rfl, rfl⟩

def archive (emission : Emission source input cut protocol rival vocabulary encoding) (count : Nat)
    (ack : Acknowledged source input cut protocol rival vocabulary encoding law emission count) :
    TerminalArchive (V source input cut protocol rival vocabulary encoding law) :=
  ⟨obligation source input cut protocol rival vocabulary encoding law emission, ⟨emission, count⟩,
    .fulfilled ⟨rfl, rfl, ack⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationDuty
