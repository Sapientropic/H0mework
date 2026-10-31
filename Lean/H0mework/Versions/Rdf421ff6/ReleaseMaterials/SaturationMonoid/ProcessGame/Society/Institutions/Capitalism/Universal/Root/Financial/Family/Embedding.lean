import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.History

/-! The single-source account is embedded with its complete dependent admission,
archives and lifecycle records.  No aggregate balance supplies an origin. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument) (index : Index)

def event : Financial.Event (sources index) → Family.Event sources
  | .birth claim => .birth ⟨index, claim⟩
  | .review claim receipt before cap => .review ⟨index, claim⟩ (Review.ofOriginal sources index receipt) before cap

omit [DecidableEq Port] in
@[simp] theorem event_claim (source : Financial.Event (sources index)) :
    (event sources index source).claim sources = ⟨index, source.claim _⟩ := by cases source <;> rfl

omit [DecidableEq Port] in
@[simp] theorem event_before (source : Financial.Event (sources index)) :
    (event sources index source).before sources = source.before _ := by cases source <;> rfl

omit [DecidableEq Port] in
@[simp] theorem event_after (source : Financial.Event (sources index)) :
    (event sources index source).after sources = source.after _ := by
  cases source with
  | birth => rfl
  | review => exact Review.ofOriginal_after sources index _ _ _

omit [DecidableEq Port] in
@[simp] theorem event_lawful (source : Financial.Event (sources index)) :
    (event sources index source).Lawful sources ↔ source.Lawful _ := by
  cases source <;> rfl

def origin {source : Financial.Event (sources index)} {claim : IssuedClaim (sources index)} :
    ObligationOrigin (Financial.vocabulary (sources index)) source claim →
      ObligationOrigin (vocabulary sources) (event sources index source) ⟨index, claim⟩
  | .producerDemand demand .. => demand.obstruction.elim
  | .explicitCommitment receipt => by
      cases source with
      | birth original => exact .explicitCommitment ⟨congrArg (Sigma.mk index) receipt.down⟩
      | review => exact receipt.elim
  | .standingMandate receipt | .acceptedTask receipt | .activeDependency receipt | .protectedRisk receipt => receipt.elim

def assumption {source : Financial.Event (sources index)} {bearer : BirthActor (sources index)}
    {scope : InstructionOrigin (sources index)} :
    BearerAssumption (Financial.vocabulary (sources index)) source bearer scope →
      BearerAssumption (vocabulary sources) (event sources index source) ⟨index, bearer⟩ ⟨index, scope⟩
  | .accepted receipt => .accepted ⟨by
      rw [event_claim]
      exact ⟨congrArg (Sigma.mk index) receipt.down.1, congrArg (Sigma.mk index) receipt.down.2⟩⟩
  | .mandated receipt => receipt.elim

def payload (original : NativeAdmissionPayload (Financial.vocabulary (sources index))) :
    NativeAdmissionPayload (vocabulary sources) where
  sourceEvent := event sources index original.sourceEvent
  content := ⟨index, original.content⟩
  residual := original.residual
  bearer := ⟨index, original.bearer⟩
  beneficiary := ⟨index, original.beneficiary⟩
  scope := ⟨index, original.scope⟩
  lineage := ⟨index, original.lineage⟩
  anchor_scope_eq := by
    change (⟨index, original.scope⟩ : Origin sources) =
      claimOrigin sources ((event sources index original.sourceEvent).claim sources)
    rw [event_claim]
    exact congrArg (fun value : InstructionOrigin (sources index) => (⟨index, value⟩ : Origin sources)) original.anchor_scope_eq
  anchor_lineage_eq := by
    change (⟨index, original.lineage⟩ : Origin sources) =
      claimOrigin sources ((event sources index original.sourceEvent).claim sources)
    rw [event_claim]
    exact congrArg (fun value : InstructionOrigin (sources index) => (⟨index, value⟩ : Origin sources)) original.anchor_lineage_eq
  origin := origin sources index original.origin
  authority := ⟨by rw [event_claim]; exact congrArg (Sigma.mk index) original.authority.down⟩
  assumption := assumption sources index original.assumption
  dischargeJurisdiction := ⟨congrArg (Sigma.mk index) original.dischargeJurisdiction.down⟩

def obligation (original : AdmittedObligation (Financial.vocabulary (sources index))) :
    AdmittedObligation (vocabulary sources) where
  content := ⟨index, original.content⟩
  residual := original.residual
  bearer := ⟨index, original.bearer⟩
  beneficiary := ⟨index, original.beneficiary⟩
  scope := ⟨index, original.scope⟩
  admission := {
    sourceEvent := event sources index original.admission.sourceEvent
    admittedBearer := ⟨index, original.admission.admittedBearer⟩
    admittedScope := ⟨index, original.admission.admittedScope⟩
    lineage := ⟨index, original.admission.lineage⟩
    anchor_scope_eq := by
      change (⟨index, original.admission.admittedScope⟩ : Origin sources) =
        claimOrigin sources ((event sources index original.admission.sourceEvent).claim sources)
      rw [event_claim]
      exact congrArg (fun value : InstructionOrigin (sources index) => (⟨index, value⟩ : Origin sources)) original.admission.anchor_scope_eq
    anchor_lineage_eq := by
      change (⟨index, original.admission.lineage⟩ : Origin sources) =
        claimOrigin sources ((event sources index original.admission.sourceEvent).claim sources)
      rw [event_claim]
      exact congrArg (fun value : InstructionOrigin (sources index) => (⟨index, value⟩ : Origin sources)) original.admission.anchor_lineage_eq
    origin := origin sources index original.admission.origin
    authority := ⟨by rw [event_claim]; exact congrArg (Sigma.mk index) original.admission.authority.down⟩
    assumption := assumption sources index original.admission.assumption }
  dischargeJurisdiction := ⟨congrArg (Sigma.mk index) original.dischargeJurisdiction.down⟩

def final {original : AdmittedObligation (Financial.vocabulary (sources index))}
    {source : Financial.Event (sources index)} :
    FinalReceipt (Financial.vocabulary (sources index)) original source →
      FinalReceipt (vocabulary sources) (obligation sources index original) (event sources index source)
  | .fulfilled receipt => .fulfilled ⟨by
      refine ⟨(event_lawful sources index source).2 receipt.down.1, ?_,
        congrArg (Sigma.mk index) receipt.down.2.2.1, ?_⟩
      · rw [event_claim]; exact congrArg (Sigma.mk index) receipt.down.2.1
      · exact (event_after sources index source).trans receipt.down.2.2.2⟩
  | .waived receipt | .invalidated receipt | .abandonedWithConsequence receipt | .impossibleResidueAccepted receipt => receipt.elim

def archive (original : TerminalArchive (Financial.vocabulary (sources index))) :
    TerminalArchive (vocabulary sources) :=
  ⟨obligation sources index original.obligation, event sources index original.sourceEvent, final sources index original.receipt⟩

def slot : ObligationSlot (Financial.vocabulary (sources index)) → ObligationSlot (vocabulary sources)
  | .live original => .live (obligation sources index original)
  | .terminal original => .terminal (archive sources index original)

def carry {original : AdmittedObligation (Financial.vocabulary (sources index))}
    {source : Financial.Event (sources index)} :
    ActiveCarryDisposition (Financial.vocabulary (sources index)) original source →
      ActiveCarryDisposition (vocabulary sources) (obligation sources index original) (event sources index source)
  | .progressed after receipt => .progressed after ⟨by
      refine ⟨(event_lawful sources index source).2 receipt.down.1, ?_, ?_, ?_⟩
      · rw [event_claim]; exact congrArg (Sigma.mk index) receipt.down.2.1
      · exact receipt.down.2.2.1.trans (event_before sources index source).symm
      · exact receipt.down.2.2.2.trans (event_after sources index source).symm⟩
  | .progressedAndTransferred _ _ _ impossible | .maintained impossible | .deferred impossible
  | .narrowed _ impossible _ | .transferred _ impossible => impossible.elim

def record : LifecycleEvent (Financial.vocabulary (sources index)) → LifecycleEvent (vocabulary sources)
  | .admitted position original => .admitted position (payload sources index original)
  | .carried position original source receipt =>
      .carried position (obligation sources index original) (event sources index source) (carry sources index receipt)
  | .terminal position original source receipt =>
      .terminal position (obligation sources index original) (event sources index source) (final sources index receipt)
  | .superseded _ _ _ impossible => impossible.incidence.elim
  | .bearerReleased _ _ _ impossible => by cases impossible <;> exact PEmpty.elim (by assumption)
  | .reopened _ _ impossible => impossible.incidence.elim

def state (original : ResponsibilityState (Financial.vocabulary (sources index))) :
    ResponsibilityState (vocabulary sources) :=
  ⟨original.slots.map (slot sources index), original.history.map (record sources index)⟩

@[simp] theorem payload_admission (claim : IssuedClaim (sources index)) :
    payload sources index (Financial.admission (sources index) claim) = admission sources ⟨index, claim⟩ := rfl

@[simp] theorem obligation_admission (claim : IssuedClaim (sources index)) :
    obligation sources index (Financial.admission (sources index) claim).toObligation =
      (admission sources ⟨index, claim⟩).toObligation := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding
