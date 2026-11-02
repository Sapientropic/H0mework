import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePrefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDuty

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle ComplementObservation
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code))

abbrev Content := StageBudget.Ballot (code := code) × Fin code.sites
def content (wire : StageTransport.Wire (code := code)) : Content (code := code) := (wire.ballot, wire.recipient)

structure Emission where
  private mk ::
  birthStages : List (EventHistory.Stage (code := code))
  send : Nat
  at_birth : birthStages.length = send + 1
  wire : StageTransport.Wire (code := code)
  generated : StageTransport.issuedAt vocabulary encoding cursor birthStages send = some wire
  first : ∀ earlier < send, ∀ previous,
    StageTransport.issuedAt vocabulary encoding cursor birthStages earlier = some previous → content previous ≠ content wire

abbrev Emission.nativeSource (emission : Emission cursor vocabulary encoding) :=
  (EventHistory.execute cursor emission.birthStages).source

/-- A responsibility is admitted only at the end of its actual first-send prefix. -/
def birthPrefix (birthStages : List (EventHistory.Stage (code := code))) (index : Nat) : Option (Emission cursor vocabulary encoding) :=
  if length : birthStages.length = index + 1 then
    match actual : StageTransport.issuedAt vocabulary encoding cursor birthStages index with
    | none => none
    | some wire =>
      if old : ((List.range index).filterMap (StageTransport.issuedAt vocabulary encoding cursor birthStages)).any
          (fun previous => decide (content previous = content wire)) then none
      else some ⟨birthStages, index, length, wire, actual, by
        intro earlier before previous generated same
        apply old
        exact List.any_eq_true.mpr ⟨previous,
          List.mem_filterMap.mpr ⟨earlier, List.mem_range.mpr before, generated⟩, decide_eq_true same⟩⟩
  else none

def birth (stages : List (EventHistory.Stage (code := code))) (index : Nat) :=
  birthPrefix cursor vocabulary encoding (stages.take (index + 1)) index

def origins (stages : List (EventHistory.Stage (code := code))) :=
  (List.range stages.length).filterMap (birth cursor vocabulary encoding stages)

theorem birth_is_the_original_prefix (stages : List (EventHistory.Stage (code := code))) (index : Nat)
    (emission : Emission cursor vocabulary encoding)
    (born : birth cursor vocabulary encoding stages index = some emission) :
    emission.birthStages = stages.take (index + 1) ∧ emission.send = index := by
  unfold birth birthPrefix at born
  split at born <;> try contradiction
  split at born <;> try contradiction
  split at born <;> try contradiction
  cases Option.some.inj born
  exact ⟨rfl, rfl⟩

theorem birth_survives_extension (stages future : List (EventHistory.Stage (code := code))) (index : Nat)
    (bounded : index < stages.length) :
    birth cursor vocabulary encoding (stages ++ future) index = birth cursor vocabulary encoding stages index := by
  unfold birth
  rw [List.take_append_of_le_length (by omega : index + 1 ≤ stages.length)]

variable (law : StageReception.Law code)

abbrev received (emission : Emission cursor vocabulary encoding) (suffix : List (EventHistory.Stage (code := code))) :=
  StageReception.run vocabulary encoding law cursor (emission.birthStages ++ suffix) emission.wire.recipient
    (emission.birthStages ++ suffix).length

def Acknowledged (emission : Emission cursor vocabulary encoding) (suffix : List (EventHistory.Stage (code := code))) : Prop :=
  ∃ receipt ∈ (received cursor vocabulary encoding law emission suffix).receipts, receipt.wire.ballot = emission.wire.ballot

instance (emission : Emission cursor vocabulary encoding) (suffix : List (EventHistory.Stage (code := code))) :
    Decidable (Acknowledged cursor vocabulary encoding law emission suffix) := by unfold Acknowledged; infer_instance

theorem acknowledgment_has_actual_owned_paid_communication
    (emission : Emission cursor vocabulary encoding) (suffix : List (EventHistory.Stage (code := code)))
    (ack : Acknowledged cursor vocabulary encoding law emission suffix) :
    ∃ receipt ∈ (received cursor vocabulary encoding law emission suffix).receipts,
      receipt.wire.ballot = emission.wire.ballot ∧
      StageTransport.verify vocabulary encoding cursor (emission.birthStages ++ suffix) receipt.wire = true := by
  obtain ⟨receipt, inside, same⟩ := ack
  obtain ⟨row, seen, actual, _, _, accepted⟩ := StageReception.every_receipt_retains_its_actual_delivery
    vocabulary encoding law cursor (emission.birthStages ++ suffix) emission.wire.recipient _ receipt inside
  exact ⟨receipt, inside, same, (StageReception.check_sound vocabulary encoding law cursor
    (emission.birthStages ++ suffix) emission.wire.recipient row seen receipt.wire receipt.wire accepted).2.2.2.1⟩

theorem acknowledged_is_preserved (emission : Emission cursor vocabulary encoding)
    (suffix more : List (EventHistory.Stage (code := code)))
    (ack : Acknowledged cursor vocabulary encoding law emission suffix) :
    Acknowledged cursor vocabulary encoding law emission (suffix ++ more) := by
  obtain ⟨receipt, inside, same⟩ := ack
  refine ⟨receipt, ?_, same⟩
  simpa only [received, List.append_assoc] using
    (StagePrefix.receipts_survive_actual_extension cursor (emission.birthStages ++ suffix) more vocabulary encoding law
      emission.wire.recipient).subset inside

structure Event where
  emission : Emission cursor vocabulary encoding
  suffix : List (EventHistory.Stage (code := code))

structure AdmissionAt (event : Event cursor vocabulary encoding) (body : Content (code := code)) where
  registration : Native.RegistrationReceipt event.emission.nativeSource
  at_emission : event.suffix = []
  original : body = content event.emission.wire

structure AssumptionAt (bearer : Fin code.sites)
    (event : Event cursor vocabulary encoding) (body : Content (code := code))
    extends AdmissionAt cursor vocabulary encoding event body where
  machine_role : bearer = event.emission.wire.ballot.key

def vocabularyLaw : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event cursor vocabulary encoding
  Content := Content (code := code)
  Residual := Content (code := code)
  Bearer := Fin code.sites
  ProtectedInterest := Fin code.sites
  Scope := Content (code := code)
  Lineage := Content (code := code)
  Incidence := Content (code := code)
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (content event.emission.wire) (content event.emission.wire)
  sourceIncidence := fun event => content event.emission.wire
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := fun _ _ => Empty
  ActiveDependencyAt := AdmissionAt cursor vocabulary encoding
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt cursor vocabulary encoding
  AcceptedAt := AssumptionAt cursor vocabulary encoding
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun body scope => PLift (body = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := fun event body scope => PLift (body = content event.emission.wire ∧ scope = body ∧
    ¬ Acknowledged cursor vocabulary encoding law event.emission event.suffix)
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := fun event body scope => PLift (body = content event.emission.wire ∧ scope = body ∧
    Acknowledged cursor vocabulary encoding law event.emission event.suffix)
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

abbrev V := vocabularyLaw cursor vocabulary encoding law

def admission (emission : Emission cursor vocabulary encoding) :
    NativeAdmissionPayload (V cursor vocabulary encoding law) where
  sourceEvent := ⟨emission, []⟩
  content := content emission.wire
  residual := content emission.wire
  bearer := emission.wire.ballot.key
  beneficiary := emission.wire.recipient
  scope := content emission.wire
  lineage := content emission.wire
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .activeDependency ⟨Native.registered _, rfl, rfl⟩
  authority := ⟨Native.registered _, rfl, rfl⟩
  assumption := .accepted ⟨⟨Native.registered _, rfl, rfl⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

abbrev obligation (emission : Emission cursor vocabulary encoding) :=
  (admission cursor vocabulary encoding law emission).toObligation

structure Review (duty : AdmittedObligation (V cursor vocabulary encoding law)) where
  emission : Emission cursor vocabulary encoding
  suffix : List (EventHistory.Stage (code := code))
  content_eq : duty.content = content emission.wire
  scope_eq : duty.scope = duty.content
  original : duty.admission.sourceEvent.emission = emission

def reviewSource {duty : AdmittedObligation (V cursor vocabulary encoding law)}
    (event : Review cursor vocabulary encoding law duty) :
    Event cursor vocabulary encoding := ⟨event.emission, event.suffix⟩

def disposition {duty : AdmittedObligation (V cursor vocabulary encoding law)}
    (event : Review cursor vocabulary encoding law duty) :
    BoundaryDisposition (V cursor vocabulary encoding law) duty
      (reviewSource cursor vocabulary encoding law event) :=
  if ack : Acknowledged cursor vocabulary encoding law event.emission event.suffix then
    .terminal (.final (.fulfilled ⟨event.content_eq, event.scope_eq, ack⟩))
  else .carry (.maintained ⟨event.content_eq, event.scope_eq, ack⟩)

def process : NativeResponsibilityProcess (V cursor vocabulary encoding law) where
  AdmissionEvent := Emission cursor vocabulary encoding
  admissionPayload := admission cursor vocabulary encoding law
  BoundaryEvent := Review cursor vocabulary encoding law
  boundarySource := reviewSource cursor vocabulary encoding law
  boundary_anchor_eq := by
    intro duty event
    change MinimalRegistrableSourceAnchor.canonical (content event.emission.wire) _ =
      MinimalRegistrableSourceAnchor.canonical (content duty.admission.sourceEvent.emission.wire) _
    rw [event.original]
    rfl
  boundary_incidence_eq := by
    intro duty event
    change content event.emission.wire = content duty.admission.sourceEvent.emission.wire
    rw [event.original]
  boundaryDisposition := disposition cursor vocabulary encoding law
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def review (emission : Emission cursor vocabulary encoding) (suffix : List (EventHistory.Stage (code := code))) :
    Review cursor vocabulary encoding law
      (obligation cursor vocabulary encoding law emission) := ⟨emission, suffix, rfl, rfl, rfl⟩

def archive (emission : Emission cursor vocabulary encoding) (suffix : List (EventHistory.Stage (code := code)))
    (ack : Acknowledged cursor vocabulary encoding law emission suffix) :
    TerminalArchive (V cursor vocabulary encoding law) :=
  ⟨obligation cursor vocabulary encoding law emission, ⟨emission, suffix⟩,
    .fulfilled ⟨rfl, rfl, ack⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDuty
