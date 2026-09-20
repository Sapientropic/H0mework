import H0mework.Foundation.Ledger.Restructuring

/-!
# Proof-relevant whole-ledger restructuring

An identity ledger evolution must not require proof irrelevance of the
world's `OpenAt` fibres.  This kernel presents the complete indexed open entry
itself as lifecycle content.  Distinct open witnesses therefore remain
distinct obligations, while identity source/target maps can still receive
the existing no-split/no-merge restructuring certification.

The construction is source-neutral.  It supplies no effect, obstruction,
projection, settlement or generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedProofRelevantRestructuring

universe u

/-- Full proof-relevant world-ledger entry, including its support index. -/
abbrev WorldOpenEntry (W : WorldRelationNetwork.{u}) :=
  Σ support : W.Support, OpenResponsibilityAt W support

private def complementObservation
    (W : WorldRelationNetwork.{u}) (focus : W.Support) :
    ComplementObservation.ComplementObservationCarrier.{u} where
  Carrier := W.Anchor × Bool
  null := (W.anchorAt focus, false)
  complement := fun point => (point.1, !point.2)
  complement_involutive := by
    rintro ⟨anchor, bit⟩
    cases bit <;> rfl
  null_ne_complement_null := by
    intro equality
    exact Bool.noConfusion (congrArg Prod.snd equality)

/-- Lifecycle vocabulary whose content retains the complete open-entry
identity.  Equality seals keep source, scope and discharge jurisdiction tied
to that entry instead of replacing them by an inhabited unit field. -/
def vocabulary
    (W : WorldRelationNetwork.{u}) (focus : W.Support) :
    RestructuringVocabulary.{u} where
  base := {
    SourceEvent := W.Support
    Content := WorldOpenEntry W
    Residual := PUnit
    Bearer := PUnit
    ProtectedInterest := PUnit
    Scope := W.Support
    Lineage := W.Lineage
    Incidence := W.Incidence
    SourceObservation := complementObservation W focus
    sourceAnchor := fun support => {
      identity := (W.anchorAt support, false)
      identity_ne_complement_identity := by
        intro equality
        exact Bool.noConfusion (congrArg Prod.snd equality)
      scope := support
      lineage := W.lineageAt support }
    sourceIncidence := W.incidenceAt
    ObstructionAt := fun _ => PEmpty
    demandContent := fun {_} obstruction => nomatch obstruction
    demandResidual := fun {_} obstruction => nomatch obstruction
    CommitmentAt := fun source content =>
      ULift.{u, 0} (PLift (content.1 = source))
    MandateOriginAt := fun _ _ => PEmpty
    AcceptedTaskAt := fun _ _ => PEmpty
    ActiveDependencyAt := fun _ _ => PEmpty
    ProtectedRiskAt := fun _ _ => PEmpty
    AdmissionAuthorityAt := fun source scope =>
      ULift.{u, 0} (PLift (scope = source))
    AcceptedAt := fun _ source scope =>
      ULift.{u, 0} (PLift (scope = source))
    StandingMandateAt := fun _ _ _ => PEmpty
    DischargeJurisdiction := fun content scope =>
      ULift.{u, 0} (PLift (content.1 = scope))
    ProgressAt := fun _ _ _ _ => PEmpty
    MaintenanceAt := fun _ _ _ => PEmpty
    TypedDeferAt := fun _ _ _ => PEmpty
    ScopeNarrowingAt := fun _ _ _ => PEmpty
    TransferAcceptedAt := fun _ _ _ _ => PEmpty
    FulfilledAt := fun _ _ _ => PEmpty
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
    TransferOfferSignal := PEmpty }
  DescendantAt := fun _ _ _ _ _ => PEmpty
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ _ _ => PEmpty
  RenameAt := fun _ _ _ => PEmpty

def payload
    (W : WorldRelationNetwork.{u}) (focus : W.Support)
    {support : W.Support} (entry : OpenResponsibilityAt W support) :
    NativeAdmissionPayload (vocabulary W focus).base where
  sourceEvent := support
  content := ⟨support, entry⟩
  residual := PUnit.unit
  bearer := PUnit.unit
  beneficiary := PUnit.unit
  scope := support
  lineage := W.lineageAt support
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment (ULift.up (PLift.up rfl))
  authority := ULift.up (PLift.up rfl)
  assumption := .accepted (ULift.up (PLift.up rfl))
  dischargeJurisdiction := ULift.up (PLift.up rfl)

def obligationAt
    (W : WorldRelationNetwork.{u}) (focus : W.Support)
    {support : W.Support} (entry : OpenResponsibilityAt W support) :
    (vocabulary W focus).Obligation :=
  (payload W focus entry).toObligation

/-- Obligation identity retains the complete proof-relevant open entry. -/
theorem obligationAt_injective
    (W : WorldRelationNetwork.{u}) (focus : W.Support)
    {support : W.Support} :
    Function.Injective (obligationAt W focus (support := support)) := by
  intro left right equality
  have content_eq := congrArg AdmittedObligation.content equality
  change (⟨support, left⟩ : WorldOpenEntry W) = ⟨support, right⟩ at content_eq
  cases content_eq
  rfl

/-- Source-fixed restructuring presentation for arbitrary proof-relevant
world ledgers.  Actual split/merge authority remains empty; a compiler may use
this law only after proving its origin and destination maps injective. -/
def law
    {V : Vocabulary.{u}} (W : WorldRelationNetwork.{u}) (focus : W.Support)
    (source : SourceNativeSource W V) :
    SourceNativeLedgerRestructuringLaw source where
  vocabulary := vocabulary W focus
  sourceEventAt := fun occurrence => occurrence.1
  obligationAt := by
    intro _current _occurrence _support entry
    exact obligationAt W focus entry
  responsibilityKey := fun obligation => obligation.content.2.1
  anchorKey := Prod.fst
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by
    intro _current _occurrence _support _entry
    rfl
  anchor_commutes := by
    intro _current _occurrence _support _entry
    rfl
  incidence_commutes := by
    intro _current _occurrence _support _entry
    rfl
  lineage_commutes := by
    intro _current _occurrence _support _entry
    rfl
  obligationAt_injective := by
    intro _current _occurrence _support
    exact obligationAt_injective W focus

end RootGeneratedProofRelevantRestructuring
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
