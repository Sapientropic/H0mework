import H0mework.Foundation.Responsibility.JointSource.Native.Receipt
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Projection
import H0mework.Versions.R2.Foundation.Authority.SourceProjectionInventory

/-! The original restructuring vocabulary and an independent mathematical
row retain disjoint source fibres. Every old admission field and receipt is
inherited as data; source/target rows are never identified by their content. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring
open SourceOperationEffects DebtActivationWorld

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (program : Program old.toLedgerRoot)
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)

abbrev originalLaw := old.source.restructuringSource.compiler.restructuringLaw
abbrev Original := (originalLaw old).vocabulary
abbrev MathLaw := Idle.law registered.input.environment registered.input.expression

private inductive MathScopeAt (support : N.Support) : N.Support → Type u
  | exact : MathScopeAt support support

def observation : ComplementObservation.ComplementObservationCarrier.{u} where
  Carrier := (Original old).base.SourceObservation.Carrier ⊕ (N.Anchor × Bool)
  null := .inl (Original old).base.SourceObservation.null
  complement := fun point => match point with
    | .inl prior => .inl ((Original old).base.SourceObservation.complement prior)
    | .inr current => .inr (current.1, !current.2)
  complement_involutive := by
    rintro (prior | ⟨anchor, bit⟩)
    · exact congrArg Sum.inl ((Original old).base.SourceObservation.complement_involutive prior)
    · cases bit <;> rfl
  null_ne_complement_null := fun same =>
    (Original old).base.SourceObservation.null_ne_complement_null (Sum.inl.inj same)

def oldAnchor (anchor : MinimalRegistrableSourceAnchor (Original old).base.SourceObservation
    (Original old).base.Scope (Original old).base.Lineage) :
    MinimalRegistrableSourceAnchor (observation old)
      ((Original old).base.Scope ⊕ N.Support) ((Original old).base.Lineage ⊕ N.Lineage) where
  identity := .inl anchor.identity
  identity_ne_complement_identity := fun same => anchor.identity_ne_complement_identity (Sum.inl.inj same)
  scope := .inl anchor.scope
  lineage := .inl anchor.lineage

def mathAnchor (support : N.Support) : MinimalRegistrableSourceAnchor (observation old)
    ((Original old).base.Scope ⊕ N.Support) ((Original old).base.Lineage ⊕ N.Lineage) where
  identity := .inr (N.anchorAt support, false)
  identity_ne_complement_identity := by
    intro same
    exact Bool.noConfusion (congrArg Prod.snd (Sum.inr.inj same))
  scope := .inr support
  lineage := .inr (N.lineageAt support)

def base : ResponsibilityLifecycle.Vocabulary.{u} where
  SourceEvent := (Original old).base.SourceEvent ⊕ (N.Support × (MathLaw old registered).DebtState)
  Content := (Original old).base.Content ⊕ (MathLaw old registered).DebtId
  Residual := (Original old).base.Residual ⊕ PUnit
  Bearer := (Original old).base.Bearer ⊕ PUnit
  ProtectedInterest := (Original old).base.ProtectedInterest ⊕ PUnit
  Scope := (Original old).base.Scope ⊕ N.Support
  Lineage := (Original old).base.Lineage ⊕ N.Lineage
  Incidence := (Original old).base.Incidence ⊕ N.Incidence
  SourceObservation := observation old
  sourceAnchor := fun event => match event with
    | .inl event => oldAnchor old ((Original old).base.sourceAnchor event)
    | .inr event => mathAnchor old event.1
  sourceIncidence := fun event => match event with
    | .inl event => .inl ((Original old).base.sourceIncidence event)
    | .inr event => .inr (N.incidenceAt event.1)
  ObstructionAt := fun event => match event with
    | .inl event => (Original old).base.ObstructionAt event
    | .inr _ => PEmpty
  demandContent := fun {event} obstruction => match event with
    | .inl _ => .inl ((Original old).base.demandContent obstruction)
    | .inr _ => nomatch obstruction
  demandResidual := fun {event} obstruction => match event with
    | .inl _ => .inl ((Original old).base.demandResidual obstruction)
    | .inr _ => nomatch obstruction
  CommitmentAt := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.CommitmentAt a b
    | .inr _, .inr b => ULift.{u, 0} (PLift (b = (MathLaw old registered).debtId))
    | _, _ => PEmpty
  MandateOriginAt := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.MandateOriginAt a b
    | _, _ => PEmpty
  AcceptedTaskAt := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.AcceptedTaskAt a b
    | _, _ => PEmpty
  ActiveDependencyAt := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.ActiveDependencyAt a b
    | _, _ => PEmpty
  ProtectedRiskAt := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.ProtectedRiskAt a b
    | _, _ => PEmpty
  AdmissionAuthorityAt := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.AdmissionAuthorityAt a b
    | .inr a, .inr b => MathScopeAt a.1 b
    | _, _ => PEmpty
  AcceptedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.AcceptedAt a b c
    | .inr _, .inr b, .inr c => MathScopeAt b.1 c
    | _, _, _ => PEmpty
  StandingMandateAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.StandingMandateAt a b c
    | _, _, _ => PEmpty
  DischargeJurisdiction := fun a b => match a, b with
    | .inl a, .inl b => (Original old).base.DischargeJurisdiction a b
    | .inr a, .inr _ => ULift.{u, 0} (PLift (a = (MathLaw old registered).debtId))
    | _, _ => PEmpty
  ProgressAt := fun a b c d => match a, b, c, d with
    | .inl a, .inl b, .inl c, .inl d => (Original old).base.ProgressAt a b c d
    | _, _, _, _ => PEmpty
  MaintenanceAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.MaintenanceAt a b c
    | _, _, _ => PEmpty
  TypedDeferAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.TypedDeferAt a b c
    | _, _, _ => PEmpty
  ScopeNarrowingAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.ScopeNarrowingAt a b c
    | _, _, _ => PEmpty
  TransferAcceptedAt := fun a b c d => match a, b, c, d with
    | .inl a, .inl b, .inl c, .inl d => (Original old).base.TransferAcceptedAt a b c d
    | _, _, _, _ => PEmpty
  FulfilledAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.FulfilledAt a b c
    | _, _, _ => PEmpty
  WaivedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.WaivedAt a b c
    | _, _, _ => PEmpty
  InvalidatedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.InvalidatedAt a b c
    | _, _, _ => PEmpty
  AbandonedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.AbandonedAt a b c
    | _, _, _ => PEmpty
  ImpossibleResidueAcceptedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.ImpossibleResidueAcceptedAt a b c
    | _, _, _ => PEmpty
  SupersessionAt := fun a b c d e f g => match a, b, c, d, e, f, g with
    | .inl a, .inl b, .inl c, .inl d, .inl e, .inl f, .inl g => (Original old).base.SupersessionAt a b c d e f g
    | _, _, _, _, _, _, _ => PEmpty
  ReopenAt := fun a b c d e f g => match a, b, c, d, e, f, g with
    | .inl a, .inl b, .inl c, .inl d, .inl e, .inl f, .inl g => (Original old).base.ReopenAt a b c d e f g
    | _, _, _, _, _, _, _ => PEmpty
  JurisdictionEndedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.JurisdictionEndedAt a b c
    | _, _, _ => PEmpty
  ConsentRevokedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.ConsentRevokedAt a b c
    | _, _, _ => PEmpty
  CapacityReleasedAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.CapacityReleasedAt a b c
    | _, _, _ => PEmpty
  UpperRouteAt := fun a b c => match a, b, c with
    | .inl a, .inl b, .inl c => (Original old).base.UpperRouteAt a b c
    | _, _, _ => PEmpty
  NextActorSignal := (Original old).base.NextActorSignal
  AgeSignal := (Original old).base.AgeSignal
  TransferOfferSignal := (Original old).base.TransferOfferSignal


def oldOrigin {event : (Original old).base.SourceEvent} {content : (Original old).base.Content} :
    ObligationOrigin (Original old).base event content → ObligationOrigin (base old registered) (.inl event) (.inl content)
  | .producerDemand demand eventEq contentEq =>
      .producerDemand ⟨.inl demand.sourceEvent, demand.obstruction⟩
        (congrArg Sum.inl eventEq) (congrArg Sum.inl contentEq)
  | .explicitCommitment receipt => .explicitCommitment receipt
  | .standingMandate receipt => .standingMandate receipt
  | .acceptedTask receipt => .acceptedTask receipt
  | .activeDependency receipt => .activeDependency receipt
  | .protectedRisk receipt => .protectedRisk receipt

def oldAssumption {event : (Original old).base.SourceEvent} {bearer : (Original old).base.Bearer}
    {scope : (Original old).base.Scope} : BearerAssumption (Original old).base event bearer scope →
      BearerAssumption (base old registered) (.inl event) (.inl bearer) (.inl scope)
  | .accepted receipt => .accepted receipt
  | .mandated receipt => .mandated receipt

def oldObligation (entry : (Original old).Obligation) : AdmittedObligation (base old registered) where
  content := .inl entry.content
  residual := .inl entry.residual
  bearer := .inl entry.bearer
  beneficiary := .inl entry.beneficiary
  scope := .inl entry.scope
  admission :=
    { sourceEvent := .inl entry.admission.sourceEvent
      admittedBearer := .inl entry.admission.admittedBearer
      admittedScope := .inl entry.admission.admittedScope
      lineage := .inl entry.admission.lineage
      anchor_scope_eq := congrArg Sum.inl entry.admission.anchor_scope_eq
      anchor_lineage_eq := congrArg Sum.inl entry.admission.anchor_lineage_eq
      origin := oldOrigin old registered entry.admission.origin
      authority := entry.admission.authority
      assumption := oldAssumption old registered entry.admission.assumption }
  dischargeJurisdiction := entry.dischargeJurisdiction

def mathObligation (support : N.Support) (state : (MathLaw old registered).DebtState) :
    AdmittedObligation (base old registered) :=
  (show NativeAdmissionPayload (base old registered) from
    { sourceEvent := .inr (support, state)
      content := .inr (MathLaw old registered).debtId
      residual := .inr PUnit.unit
      bearer := .inr PUnit.unit
      beneficiary := .inr PUnit.unit
      scope := .inr support
      lineage := .inr (N.lineageAt support)
      anchor_scope_eq := rfl
      anchor_lineage_eq := rfl
      origin := .explicitCommitment ⟨⟨rfl⟩⟩
      authority := .exact
      assumption := .accepted .exact
      dischargeJurisdiction := ⟨⟨rfl⟩⟩ }).toObligation


def readOrigin {event : (Original old).base.SourceEvent} {content : (Original old).base.Content}
    (receipt : ObligationOrigin (base old registered) (.inl event) (.inl content)) :
    ObligationOrigin (Original old).base event content := by
  cases receipt with
  | producerDemand demand eventEq contentEq =>
      rcases demand with ⟨source, obstruction⟩
      cases source with
      | inl source => exact .producerDemand ⟨source, obstruction⟩ (Sum.inl.inj eventEq) (Sum.inl.inj contentEq)
      | inr source => exact nomatch obstruction
  | explicitCommitment receipt => exact .explicitCommitment receipt
  | standingMandate receipt => exact .standingMandate receipt
  | acceptedTask receipt => exact .acceptedTask receipt
  | activeDependency receipt => exact .activeDependency receipt
  | protectedRisk receipt => exact .protectedRisk receipt

def readAssumption {event : (Original old).base.SourceEvent} {bearer : (Original old).base.Bearer}
    {scope : (Original old).base.Scope}
    (receipt : BearerAssumption (base old registered) (.inl event) (.inl bearer) (.inl scope)) :
    BearerAssumption (Original old).base event bearer scope := by
  cases receipt with
  | accepted receipt => exact .accepted receipt
  | mandated receipt => exact .mandated receipt

theorem readOrigin_old {event : (Original old).base.SourceEvent} {content : (Original old).base.Content}
    (receipt : ObligationOrigin (Original old).base event content) :
    readOrigin old registered (oldOrigin old registered receipt) = receipt := by
  cases receipt <;> rfl

theorem readAssumption_old {event : (Original old).base.SourceEvent} {bearer : (Original old).base.Bearer}
    {scope : (Original old).base.Scope} (receipt : BearerAssumption (Original old).base event bearer scope) :
    readAssumption old registered (oldAssumption old registered receipt) = receipt := by
  cases receipt <;> rfl

/-- A partial restriction of the disjoint vocabulary, retaining the entire
original obligation. It selects no lifecycle outcome or world branch. -/
def readOld (entry : AdmittedObligation (base old registered)) : Option (Original old).Obligation := by
  rcases entry with ⟨content, residual, bearer, beneficiary, scope, admission, discharge⟩
  rcases admission with ⟨event, admittedBearer, admittedScope, lineage, scopeEq, lineageEq, originReceipt, authority, assumption⟩
  cases content with
  | inr _ => exact none
  | inl content =>
      cases residual with
      | inr _ => exact none
      | inl residual =>
          cases bearer with
          | inr _ => exact none
          | inl bearer =>
              cases beneficiary with
              | inr _ => exact none
              | inl beneficiary =>
                  cases scope with
                  | inr _ => exact none
                  | inl scope =>
                      cases event with
                      | inr _ => exact none
                      | inl event =>
                          cases admittedBearer with
                          | inr _ => exact none
                          | inl admittedBearer =>
                              cases admittedScope with
                              | inr _ => exact none
                              | inl admittedScope =>
                                  cases lineage with
                                  | inr _ => exact none
                                  | inl lineage =>
                                      exact some
                                        { content := content
                                          residual := residual
                                          bearer := bearer
                                          beneficiary := beneficiary
                                          scope := scope
                                          admission :=
                                            { sourceEvent := event
                                              admittedBearer := admittedBearer
                                              admittedScope := admittedScope
                                              lineage := lineage
                                              anchor_scope_eq := Sum.inl.inj scopeEq
                                              anchor_lineage_eq := Sum.inl.inj lineageEq
                                              origin := readOrigin old registered originReceipt
                                              authority := authority
                                              assumption := readAssumption old registered assumption }
                                          dischargeJurisdiction := discharge }

theorem readOld_old (entry : (Original old).Obligation) :
    readOld old registered (oldObligation old registered entry) = some entry := by
  rcases entry with ⟨content, residual, bearer, beneficiary, scope, admission, discharge⟩
  rcases admission with ⟨event, admittedBearer, admittedScope, lineage, scopeEq, lineageEq, originReceipt, authority, assumption⟩
  simp only [oldObligation, readOld, readOrigin_old, readAssumption_old]

theorem oldObligation_injective : Function.Injective (oldObligation old registered) := by
  intro first second same
  exact Option.some.inj ((readOld_old old registered first).symm.trans
    ((congrArg (readOld old registered) same).trans (readOld_old old registered second)))

abbrev vocabulary : RestructuringVocabulary.{u} where
  base := base old registered
  DescendantAt := fun source parentIncidence parentContent childIncidence childContent =>
    match source, parentIncidence, parentContent, childIncidence, childContent with
    | .inl source, .inl parentIncidence, .inl parentContent, .inl childIncidence, .inl childContent =>
        (Original old).DescendantAt source parentIncidence parentContent childIncidence childContent
    | _, _, _, _, _ => PEmpty
  SplitCoverageAt := fun source parent children => match source, parent with
    | .inl source, .inl parent => Σ original : List (Original old).base.Content,
        PLift (children = original.map Sum.inl) × (Original old).SplitCoverageAt source parent original
    | _, _ => PEmpty
  MergeCoverageAt := fun source parents target => match source, target with
    | .inl source, .inl target => Σ original : List (Original old).base.Content,
        PLift (parents = original.map Sum.inl) × (Original old).MergeCoverageAt source original target
    | _, _ => PEmpty
  LocalDischargePreservedAt := fun source parent child => match source, parent, child with
    | .inl source, .inl parent, .inl child => (Original old).LocalDischargePreservedAt source parent child
    | _, _, _ => PEmpty
  RenameAt := fun source parent child => match source, parent, child with
    | .inl source, .inl parent, .inl child => (Original old).RenameAt source parent child
    | _, _, _ => PEmpty

/-- The registered root determines the restriction; the original source law
already distinguishes every proof-relevant old entry. -/
def obligationAt {current : Current registered}
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current)
    {support : (World registered).Support} (entry : OpenResponsibilityAt (World registered) support) :
    (vocabulary old registered).Obligation := by
  rcases support with ⟨support, state⟩
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl prior =>
      exact oldObligation old registered ((originalLaw old).obligationAt (originalOccurrence program registered occurrence) ⟨prior, opened⟩)
  | inr debt =>
      cases state with
      | none => exact nomatch opened
      | some state =>
          rcases opened with ⟨⟨same⟩⟩
          cases same
          exact mathObligation old registered support state

abbrev law : SourceNativeLedgerRestructuringLaw (source program registered) where
  vocabulary := vocabulary old registered
  sourceEventAt := fun occurrence => .inl ((originalLaw old).sourceEventAt (originalOccurrence program registered occurrence))
  obligationAt := obligationAt old program registered
  responsibilityKey := fun entry => match readOld old registered entry with
    | some prior => .inl ((originalLaw old).responsibilityKey prior)
    | none => .inr (MathLaw old registered).debtId
  anchorKey := fun identity => match identity with
    | .inl prior => (originalLaw old).anchorKey prior
    | .inr pair => pair.1
  incidenceKey := fun incidence => match incidence with
    | .inl prior => (originalLaw old).incidenceKey prior
    | .inr current => current
  lineageKey := fun lineage => match lineage with
    | .inl prior => (originalLaw old).lineageKey prior
    | .inr current => current
  responsibility_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior =>
        dsimp only [obligationAt]
        rw [readOld_old]
        exact congrArg Sum.inl ((originalLaw old).responsibility_commutes
          (originalOccurrence program registered occurrence) ⟨prior, opened⟩)
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  anchor_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact (originalLaw old).anchor_commutes (originalOccurrence program registered occurrence) ⟨prior, opened⟩
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  incidence_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact (originalLaw old).incidence_commutes (originalOccurrence program registered occurrence) ⟨prior, opened⟩
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  lineage_commutes := by
    intro current occurrence support entry
    rcases support with ⟨support, state⟩
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact (originalLaw old).lineage_commutes (originalOccurrence program registered occurrence) ⟨prior, opened⟩
    | inr debt =>
        cases state with
        | none => exact nomatch opened
        | some state => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  obligationAt_injective := by
    intro current occurrence support first second same
    rcases support with ⟨support, state⟩
    rcases first with ⟨first, firstOpen⟩
    rcases second with ⟨second, secondOpen⟩
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            exact congrArg (oldEntry (law := MathLaw old registered) (state? := state))
              ((originalLaw old).obligationAt_injective (originalOccurrence program registered occurrence)
                (oldObligation_injective old registered same))
        | inr second =>
            cases state with
            | none => exact nomatch secondOpen
            | some state => rcases secondOpen with ⟨⟨sameId⟩⟩; cases sameId; exact nomatch congrArg AdmittedObligation.content same
    | inr first =>
        cases state with
        | none => exact nomatch firstOpen
        | some state =>
            rcases firstOpen with ⟨⟨sameId⟩⟩
            cases sameId
            cases second with
            | inl second => exact nomatch congrArg AdmittedObligation.content same
            | inr second => rcases secondOpen with ⟨⟨sameId⟩⟩; cases sameId; rfl

end RootGeneratedDebtActivationJointSource.Native.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
