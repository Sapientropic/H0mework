import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Families

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def base : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := SourceEvent root boundary
  Content := Content root boundary
  Residual := (Original root).base.Residual ⊕ PUnit
  Bearer := (Original root).base.Bearer ⊕ PUnit
  ProtectedInterest := (Original root).base.ProtectedInterest ⊕ PUnit
  Scope := Scope root boundary
  Lineage := Lineage root
  Incidence := (Original root).base.Incidence ⊕ N.Incidence
  SourceObservation := observation root
  sourceAnchor := fun event => match event with
    | .inl old => oldAnchor root boundary ((Original root).base.sourceAnchor old)
    | .inr support => addedAnchor root boundary support
  sourceIncidence := fun event => match event with
    | .inl old => .inl ((Original root).base.sourceIncidence old)
    | .inr support => .inr ((W root boundary).incidenceAt support)
  ObstructionAt := fun event => match event with
    | .inl old => OldDemandAt root boundary old
    | .inr _ => PEmpty
  demandContent := fun {event} demand => match event with
    | .inl _ => .old demand.1 demand.2.1
    | .inr _ => nomatch demand
  demandResidual := fun {event} demand => match event with
    | .inl _ => .inl ((Original root).base.demandResidual demand.2.2.1)
    | .inr _ => nomatch demand
  CommitmentAt := contentFamily root boundary (Original root).base.CommitmentAt (fun support row => PLift (row.1 = support))
  MandateOriginAt := contentFamily root boundary (Original root).base.MandateOriginAt (fun _ _ => PEmpty)
  AcceptedTaskAt := contentFamily root boundary (Original root).base.AcceptedTaskAt (fun _ _ => PEmpty)
  ActiveDependencyAt := contentFamily root boundary (Original root).base.ActiveDependencyAt (fun _ _ => PEmpty)
  ProtectedRiskAt := contentFamily root boundary (Original root).base.ProtectedRiskAt (fun _ _ => PEmpty)
  AdmissionAuthorityAt := both2 (Original root).base.AdmissionAuthorityAt (fun source support => PLift (support = source))
  AcceptedAt := both3 (Original root).base.AcceptedAt (fun _ source support => PLift (support = source))
  StandingMandateAt := both3 (Original root).base.StandingMandateAt (fun _ _ _ => PEmpty)
  DischargeJurisdiction := jurisdiction root boundary
  ProgressAt := progress root boundary
  MaintenanceAt := contentScope root boundary (Original root).base.MaintenanceAt
  TypedDeferAt := contentScope root boundary (Original root).base.TypedDeferAt
  ScopeNarrowingAt := both3 (Original root).base.ScopeNarrowingAt (fun _ _ _ => PEmpty)
  TransferAcceptedAt := old4 (Original root).base.TransferAcceptedAt
  FulfilledAt := contentScope root boundary (Original root).base.FulfilledAt
  WaivedAt := contentScope root boundary (Original root).base.WaivedAt
  InvalidatedAt := contentScope root boundary (Original root).base.InvalidatedAt
  AbandonedAt := contentScope root boundary (Original root).base.AbandonedAt
  ImpossibleResidueAcceptedAt := contentScope root boundary (Original root).base.ImpossibleResidueAcceptedAt
  SupersessionAt := replacement root boundary (Original root).base.SupersessionAt
  ReopenAt := replacement root boundary (Original root).base.ReopenAt
  JurisdictionEndedAt := contentScope root boundary (Original root).base.JurisdictionEndedAt
  ConsentRevokedAt := contentScope root boundary (Original root).base.ConsentRevokedAt
  CapacityReleasedAt := contentScope root boundary (Original root).base.CapacityReleasedAt
  UpperRouteAt := contentScope root boundary (Original root).base.UpperRouteAt
  NextActorSignal := (Original root).base.NextActorSignal
  AgeSignal := (Original root).base.AgeSignal
  TransferOfferSignal := (Original root).base.TransferOfferSignal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
