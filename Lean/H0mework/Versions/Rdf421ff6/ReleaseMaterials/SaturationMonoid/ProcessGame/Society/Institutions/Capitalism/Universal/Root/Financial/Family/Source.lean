import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Instruction

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family

open ResponsibilityLifecycle Source.Program ComplementObservation

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Claim := (index : Index) × IssuedClaim (sources index)
abbrev Origin := (index : Index) × InstructionOrigin (sources index)
abbrev Actor := (index : Index) × BirthActor (sources index)
abbrev Shares := Party →₀ ℚ

def claimOrigin (claim : Claim sources) : Origin sources := ⟨claim.1, claim.2.origin⟩
def claimActor (claim : Claim sources) : Actor sources := ⟨claim.1, claim.2.debtorActor _⟩

structure Review (claim : Claim sources) where
  private mk ::
  origin : Origin sources
  instruction : ExecutionItem Party Good Port Technology Instrument
  original : origin.2.instruction? (sources origin.1) = some instruction
  kind : MovementKind
  sender : Party
  recipient : Party
  quantity : ℚ
  operation_exact : instruction.request.operation = match kind with
    | .payment => .settle claim.2.instrument claim.2.debtor sender quantity
    | .assignment => .assign claim.2.instrument claim.2.debtor sender recipient quantity
  accepted : (sources origin.1).law.Valid instruction.before instruction.request
  settlement_unit : (sources origin.1).law.settlementUnit claim.2.instrument =
    (sources claim.1).law.settlementUnit claim.2.instrument
  settlement_rate : (sources origin.1).law.settlementRate claim.2.instrument =
    (sources claim.1).law.settlementRate claim.2.instrument

def readReview (claim : Claim sources) (origin : Origin sources) : Option (Review sources claim) :=
  match readMovement (sources origin.1) origin.2 with
  | none => none
  | some movement =>
      if instrument : movement.instrument = claim.2.instrument then
        if debtor : movement.debtor = claim.2.debtor then
          if unit : (sources origin.1).law.settlementUnit claim.2.instrument =
              (sources claim.1).law.settlementUnit claim.2.instrument then
            if rate : (sources origin.1).law.settlementRate claim.2.instrument =
                (sources claim.1).law.settlementRate claim.2.instrument then
              some ⟨origin, movement.instruction, movement.original, movement.kind,
                movement.sender, movement.recipient, movement.quantity, by
                  cases kind : movement.kind <;>
                    simpa only [kind, instrument, debtor] using movement.operation_exact,
                movement.accepted, unit, rate⟩
            else none
          else none
        else none
      else none

def Review.after {claim : Claim sources} (review : Review sources claim)
    (before : Shares (Party := Party)) (cap : ℚ) : Shares (Party := Party) :=
  let used := min cap (before review.sender)
  match review.kind with
  | .payment => pay (sources claim.1) before review.sender used
  | .assignment => assign (sources claim.1) before review.sender review.recipient used

/-- The original receipt enters the common carrier at its literal source tag. -/
def Review.ofOriginal (index : Index) {claim : IssuedClaim (sources index)}
    (review : Financial.Review (sources index) claim) : Review sources ⟨index, claim⟩ where
  origin := ⟨index, review.origin⟩
  instruction := review.instruction
  original := review.instruction_exact
  kind := match review.kind with | .payment _ => .payment | .assignment .. => .assignment
  sender := review.fromHolder _
  recipient := review.toHolder _
  quantity := review.quantity
  operation_exact := by
    cases kind : review.kind <;>
      simpa only [kind, Financial.reviewOperation, Financial.Review.fromHolder,
        Financial.Review.toHolder, holderParty] using review.operation_exact
  accepted := review.accepted
  settlement_unit := rfl
  settlement_rate := rfl

omit [DecidableEq Port] in
theorem Review.ofOriginal_after (index : Index) {claim : IssuedClaim (sources index)}
    (review : Financial.Review (sources index) claim) (before : Shares (Party := Party)) (cap : ℚ) :
    (Review.ofOriginal sources index review).after sources before cap = review.after (sources index) before cap := by
  cases kind : review.kind <;>
    simp only [ofOriginal, after, Financial.Review.after, Financial.Review.allocated,
      Financial.Review.fromHolder, Financial.Review.toHolder, kind]

omit [DecidableEq Port] in
theorem Review.quantity_nonnegative {claim : Claim sources} (review : Review sources claim) :
    0 ≤ review.quantity := by
  have guard := review.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guard
  rw [review.operation_exact] at guard
  cases kind : review.kind <;> simp only [kind] at guard <;> exact guard.1

omit [DecidableEq Port] in
theorem Review.after_nonnegative {claim : Claim sources} (review : Review sources claim)
    (before : Shares (Party := Party)) (cap : ℚ) (positive : ∀ holder, 0 ≤ before holder)
    (available : 0 ≤ cap) : ∀ holder, 0 ≤ review.after sources before cap holder := by
  have used := le_min available (positive review.sender)
  cases kind : review.kind with
  | payment =>
      simpa only [Review.after, kind, Nonnegative] using
        pay_nonnegative (sources claim.1) before review.sender (min cap (before review.sender)) positive (min_le_right _ _)
  | assignment =>
      simpa only [Review.after, kind, Nonnegative] using
        assign_nonnegative (sources claim.1) before review.sender review.recipient (min cap (before review.sender))
          positive used (min_le_right _ _)

inductive Event
  | birth (claim : Claim sources)
  | review (claim : Claim sources) (receipt : Review sources claim)
      (before : Shares (Party := Party)) (cap : ℚ)

def Event.claim : Event sources → Claim sources
  | .birth claim => claim
  | .review claim .. => claim

def Event.before : Event sources → Shares (Party := Party)
  | .birth claim => initialBalance (sources claim.1) claim.2
  | .review _ _ before _ => before

def Event.after : Event sources → Shares (Party := Party)
  | .birth claim => initialBalance (sources claim.1) claim.2
  | .review _ receipt before cap => receipt.after sources before cap

def Event.Lawful : Event sources → Prop
  | .birth _ => True
  | .review _ receipt before cap => (∀ holder, 0 ≤ before holder) ∧ 0 ≤ cap ∧ cap ≤ receipt.quantity

def Event.CommitmentAt : Event sources → Claim sources → Type
  | .birth original, claim => PLift (original = claim)
  | .review .., _ => PEmpty

abbrev vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event sources
  Content := Claim sources
  Residual := Shares (Party := Party)
  Bearer := Actor sources
  ProtectedInterest := Claim sources
  Scope := Origin sources
  Lineage := Origin sources
  Incidence := Origin sources
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (claimOrigin sources (event.claim sources)) (claimOrigin sources (event.claim sources))
  sourceIncidence := fun event => claimOrigin sources (event.claim sources)
  ObstructionAt := fun _ => PEmpty
  demandContent := fun impossible => impossible.elim
  demandResidual := fun impossible => impossible.elim
  CommitmentAt := Event.CommitmentAt sources
  MandateOriginAt := fun _ _ => PEmpty
  AcceptedTaskAt := fun _ _ => PEmpty
  ActiveDependencyAt := fun _ _ => PEmpty
  ProtectedRiskAt := fun _ _ => PEmpty
  AdmissionAuthorityAt := fun event scope => PLift (scope = claimOrigin sources (event.claim sources))
  AcceptedAt := fun bearer event scope =>
    PLift (bearer = claimActor sources (event.claim sources) ∧ scope = claimOrigin sources (event.claim sources))
  StandingMandateAt := fun _ _ _ => PEmpty
  DischargeJurisdiction := fun claim scope => PLift (scope = claimOrigin sources claim)
  ProgressAt := fun event content before after =>
    PLift (event.Lawful sources ∧ event.claim sources = content ∧ before = event.before sources ∧ after = event.after sources)
  MaintenanceAt := fun _ _ _ => PEmpty
  TypedDeferAt := fun _ _ _ => PEmpty
  ScopeNarrowingAt := fun _ _ _ => PEmpty
  TransferAcceptedAt := fun _ _ _ _ => PEmpty
  FulfilledAt := fun event content scope =>
    PLift (event.Lawful sources ∧ event.claim sources = content ∧ scope = claimOrigin sources content ∧ event.after sources = 0)
  WaivedAt := fun _ _ _ => PEmpty
  InvalidatedAt := fun _ _ _ => PEmpty
  AbandonedAt := fun _ _ _ => PEmpty
  ImpossibleResidueAcceptedAt := fun _ _ _ => PEmpty
  SupersessionAt := fun _ _ _ _ _ _ _ => PEmpty
  ReopenAt := fun _ _ _ _ _ _ _ => PEmpty
  JurisdictionEndedAt := fun _ _ _ => PEmpty
  ConsentRevokedAt := fun _ _ _ => PEmpty
  CapacityReleasedAt := fun _ _ _ => PEmpty
  UpperRouteAt := fun _ _ _ => PEmpty
  NextActorSignal := PEmpty
  AgeSignal := PEmpty
  TransferOfferSignal := PEmpty

def admission (claim : Claim sources) : NativeAdmissionPayload (vocabulary sources) where
  sourceEvent := .birth claim
  content := claim
  residual := initialBalance (sources claim.1) claim.2
  bearer := claimActor sources claim
  beneficiary := claim
  scope := claimOrigin sources claim
  lineage := claimOrigin sources claim
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ⟨rfl⟩
  authority := ⟨rfl⟩
  assumption := .accepted ⟨rfl, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def Coherent (obligation : AdmittedObligation (vocabulary sources)) : Prop :=
  obligation.admission.sourceEvent.claim sources = obligation.content ∧
  obligation.scope = claimOrigin sources obligation.content ∧
  obligation.beneficiary = obligation.content ∧ obligation.bearer = claimActor sources obligation.content

structure Boundary (obligation : AdmittedObligation (vocabulary sources)) where
  private mk ::
  receipt : Review sources obligation.content
  cap : ℚ
  nonnegative : ∀ holder, 0 ≤ obligation.residual holder
  available : 0 ≤ cap
  within : cap ≤ receipt.quantity
  coherent : Coherent sources obligation

def Boundary.event {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation) :
    Event sources := .review obligation.content boundary.receipt obligation.residual boundary.cap

def Boundary.disposition {obligation : AdmittedObligation (vocabulary sources)} (boundary : Boundary sources obligation) :
    BoundaryDisposition (vocabulary sources) obligation (boundary.event sources) :=
  if cleared : boundary.receipt.after sources obligation.residual boundary.cap = 0 then
    .terminal (.final (.fulfilled ⟨⟨boundary.nonnegative, boundary.available, boundary.within⟩, rfl, boundary.coherent.2.1, cleared⟩))
  else .carry (.progressed _ ⟨⟨boundary.nonnegative, boundary.available, boundary.within⟩, rfl, rfl, rfl⟩)

def reviewBoundary (obligation : AdmittedObligation (vocabulary sources))
    (receipt : Review sources obligation.content) (cap : ℚ)
    (nonnegative : ∀ holder, 0 ≤ obligation.residual holder) (available : 0 ≤ cap)
    (within : cap ≤ receipt.quantity) (coherent : Coherent sources obligation) : Boundary sources obligation :=
  ⟨receipt, cap, nonnegative, available, within, coherent⟩

def process : NativeResponsibilityProcess (vocabulary sources) where
  AdmissionEvent := Claim sources
  admissionPayload := admission sources
  BoundaryEvent := Boundary sources
  boundarySource := Boundary.event sources
  boundary_anchor_eq := by
    intro obligation boundary
    change MinimalRegistrableSourceAnchor.canonical _ _ = MinimalRegistrableSourceAnchor.canonical _ _
    rw [boundary.coherent.1]
    rfl
  boundary_incidence_eq := by intro obligation boundary; exact congrArg (claimOrigin sources) boundary.coherent.1.symm
  boundaryDisposition := Boundary.disposition sources
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun impossible => impossible.elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family
