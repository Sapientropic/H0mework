import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Schema

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open ResponsibilityLifecycle ComplementObservation
noncomputable section

/-- The source anchor retains its actual non-self-complement identity,
registered scope and debt lineage. -/
structure Operations (sorts : Sorts) (families : Families sorts) where
  null : sorts 8
  complement : sorts 8 → sorts 8
  involutive : Function.Involutive complement
  nontrivial : null ≠ complement null
  anchorIdentity : sorts 0 → sorts 8
  anchorScope : sorts 0 → sorts 5
  anchorLineage : sorts 0 → sorts 6
  anchorRegistered : ∀ source, anchorIdentity source ≠ complement (anchorIdentity source)
  incidence : sorts 0 → sorts 7
  demandContent : {source : sorts 0} → families 0 (source, PUnit.unit) → sorts 1
  demandResidual : {source : sorts 0} → families 0 (source, PUnit.unit) → sorts 2

def observation {sorts : Sorts} {families : Families sorts} (ops : Operations sorts families) : ComplementObservationCarrier where
  Carrier := sorts 8
  null := ops.null
  complement := ops.complement
  complement_involutive := ops.involutive
  null_ne_complement_null := ops.nontrivial

def vocabulary (sorts : Sorts) (families : Families sorts) (ops : Operations sorts families) :
    ResponsibilityLifecycle.Vocabulary where
  SourceEvent := sorts 0
  Content := sorts 1
  Residual := sorts 2
  Bearer := sorts 3
  ProtectedInterest := sorts 4
  Scope := sorts 5
  Lineage := sorts 6
  Incidence := sorts 7
  SourceObservation := observation ops
  sourceAnchor := fun source => {
    identity := ops.anchorIdentity source
    identity_ne_complement_identity := ops.anchorRegistered source
    scope := ops.anchorScope source
    lineage := ops.anchorLineage source }
  sourceIncidence := ops.incidence
  ObstructionAt := fun source => families 0 (source, PUnit.unit)
  demandContent := ops.demandContent
  demandResidual := ops.demandResidual
  CommitmentAt := fun source content => families 1 (source, content, PUnit.unit)
  MandateOriginAt := fun source content => families 2 (source, content, PUnit.unit)
  AcceptedTaskAt := fun source content => families 3 (source, content, PUnit.unit)
  ActiveDependencyAt := fun source content => families 4 (source, content, PUnit.unit)
  ProtectedRiskAt := fun source content => families 5 (source, content, PUnit.unit)
  AdmissionAuthorityAt := fun source scope => families 6 (source, scope, PUnit.unit)
  AcceptedAt := fun bearer source scope => families 7 (bearer, source, scope, PUnit.unit)
  StandingMandateAt := fun bearer source scope => families 8 (bearer, source, scope, PUnit.unit)
  DischargeJurisdiction := fun content scope => families 9 (content, scope, PUnit.unit)
  ProgressAt := fun source content before after => families 10 (source, content, before, after, PUnit.unit)
  MaintenanceAt := fun source content scope => families 11 (source, content, scope, PUnit.unit)
  TypedDeferAt := fun source content scope => families 12 (source, content, scope, PUnit.unit)
  ScopeNarrowingAt := fun source before after => families 13 (source, before, after, PUnit.unit)
  TransferAcceptedAt := fun source before after scope => families 14 (source, before, after, scope, PUnit.unit)
  FulfilledAt := fun source content scope => families 15 (source, content, scope, PUnit.unit)
  WaivedAt := fun source content scope => families 16 (source, content,scope,PUnit.unit)
  InvalidatedAt := fun source content scope => families 17 (source,content,scope,PUnit.unit)
  AbandonedAt := fun source content scope => families 18 (source,content,scope,PUnit.unit)
  ImpossibleResidueAcceptedAt := fun source content scope => families 19 (source,content,scope,PUnit.unit)
  SupersessionAt := fun source a x b y scope target => families 20 (source,a,x,b,y,scope,target,PUnit.unit)
  ReopenAt := fun source a x b y scope target => families 21 (source,a,x,b,y,scope,target,PUnit.unit)
  JurisdictionEndedAt := fun source content scope => families 22 (source,content,scope,PUnit.unit)
  ConsentRevokedAt := fun source content scope => families 23 (source,content,scope,PUnit.unit)
  CapacityReleasedAt := fun source content scope => families 24 (source,content,scope,PUnit.unit)
  UpperRouteAt := fun source content scope => families 25 (source,content,scope,PUnit.unit)
  NextActorSignal := sorts 9
  AgeSignal := sorts 10
  TransferOfferSignal := sorts 11

def restructuring (sorts : Sorts) (families : Families sorts) (ops : Operations sorts families) : RestructuringVocabulary where
  base := vocabulary sorts families ops
  DescendantAt := fun source a x b y => families 26 (source,a,x,b,y,PUnit.unit)
  SplitCoverageAt := fun source parent children => families 27 (source,parent,children,PUnit.unit)
  MergeCoverageAt := fun source parents child => families 28 (source,parents,child,PUnit.unit)
  LocalDischargePreservedAt := fun source parent child => families 29 (source,parent,child,PUnit.unit)
  RenameAt := fun source before after => families 30 (source,before,after,PUnit.unit)

def familiesOf (R : RestructuringVocabulary) : Families (sortsOf R.base)
  | 0, args => R.base.ObstructionAt args.1
  | 1, args => R.base.CommitmentAt args.1 args.2.1
  | 2, args => R.base.MandateOriginAt args.1 args.2.1
  | 3, args => R.base.AcceptedTaskAt args.1 args.2.1
  | 4, args => R.base.ActiveDependencyAt args.1 args.2.1
  | 5, args => R.base.ProtectedRiskAt args.1 args.2.1
  | 6, args => R.base.AdmissionAuthorityAt args.1 args.2.1
  | 7, args => R.base.AcceptedAt args.1 args.2.1 args.2.2.1
  | 8, args => R.base.StandingMandateAt args.1 args.2.1 args.2.2.1
  | 9, args => R.base.DischargeJurisdiction args.1 args.2.1
  | 10, args => R.base.ProgressAt args.1 args.2.1 args.2.2.1 args.2.2.2.1
  | 11, args => R.base.MaintenanceAt args.1 args.2.1 args.2.2.1
  | 12, args => R.base.TypedDeferAt args.1 args.2.1 args.2.2.1
  | 13, args => R.base.ScopeNarrowingAt args.1 args.2.1 args.2.2.1
  | 14, args => R.base.TransferAcceptedAt args.1 args.2.1 args.2.2.1 args.2.2.2.1
  | 15, args => R.base.FulfilledAt args.1 args.2.1 args.2.2.1
  | 16, args => R.base.WaivedAt args.1 args.2.1 args.2.2.1
  | 17, args => R.base.InvalidatedAt args.1 args.2.1 args.2.2.1
  | 18, args => R.base.AbandonedAt args.1 args.2.1 args.2.2.1
  | 19, args => R.base.ImpossibleResidueAcceptedAt args.1 args.2.1 args.2.2.1
  | 20, args => R.base.SupersessionAt args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2.1 args.2.2.2.2.2.1 args.2.2.2.2.2.2.1
  | 21, args => R.base.ReopenAt args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2.1 args.2.2.2.2.2.1 args.2.2.2.2.2.2.1
  | 22, args => R.base.JurisdictionEndedAt args.1 args.2.1 args.2.2.1
  | 23, args => R.base.ConsentRevokedAt args.1 args.2.1 args.2.2.1
  | 24, args => R.base.CapacityReleasedAt args.1 args.2.1 args.2.2.1
  | 25, args => R.base.UpperRouteAt args.1 args.2.1 args.2.2.1
  | 26, args => R.DescendantAt args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2.1
  | 27, args => R.SplitCoverageAt args.1 args.2.1 args.2.2.1
  | 28, args => R.MergeCoverageAt args.1 args.2.1 args.2.2.1
  | 29, args => R.LocalDischargePreservedAt args.1 args.2.1 args.2.2.1
  | 30, args => R.RenameAt args.1 args.2.1 args.2.2.1
  | ⟨index + 31, bound⟩, _ => False.elim (by omega)

def operationsOf (R : RestructuringVocabulary) : Operations (sortsOf R.base) (familiesOf R) where
  null := R.base.SourceObservation.null
  complement := R.base.SourceObservation.complement
  involutive := R.base.SourceObservation.complement_involutive
  nontrivial := R.base.SourceObservation.null_ne_complement_null
  anchorIdentity := fun source => (R.base.sourceAnchor source).identity
  anchorScope := fun source => (R.base.sourceAnchor source).scope
  anchorLineage := fun source => (R.base.sourceAnchor source).lineage
  anchorRegistered := fun source => (R.base.sourceAnchor source).identity_ne_complement_identity
  incidence := R.base.sourceIncidence
  demandContent := R.base.demandContent
  demandResidual := R.base.demandResidual

theorem restructuring_original (R : RestructuringVocabulary) :
    restructuring (sortsOf R.base) (familiesOf R) (operationsOf R) = R := by
  cases R
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
