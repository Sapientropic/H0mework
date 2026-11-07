import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Events

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle ComplementObservation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

abbrev vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event sources depths counts
  Content := Claim sources depths counts
  Residual := Balance (Party := Party)
  Bearer := Actor sources depths counts
  ProtectedInterest := Claim sources depths counts
  Scope := Origin sources depths counts
  Lineage := Origin sources depths counts
  Incidence := Origin sources depths counts
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (claimOrigin sources depths counts (event.claim sources depths counts))
    (claimOrigin sources depths counts (event.claim sources depths counts))
  sourceIncidence := fun event => claimOrigin sources depths counts (event.claim sources depths counts)
  ObstructionAt := fun _ => PEmpty
  demandContent := fun impossible => impossible.elim
  demandResidual := fun impossible => impossible.elim
  CommitmentAt := Event.CommitmentAt sources depths counts
  MandateOriginAt := fun _ _ => PEmpty
  AcceptedTaskAt := fun _ _ => PEmpty
  ActiveDependencyAt := fun _ _ => PEmpty
  ProtectedRiskAt := fun _ _ => PEmpty
  AdmissionAuthorityAt := fun event scope => PLift
    (scope = claimOrigin sources depths counts (event.claim sources depths counts))
  AcceptedAt := fun bearer event scope => PLift
    (bearer = claimActor sources depths counts (event.claim sources depths counts) ∧
      scope = claimOrigin sources depths counts (event.claim sources depths counts))
  StandingMandateAt := fun _ _ _ => PEmpty
  DischargeJurisdiction := fun claim scope => PLift (scope = claimOrigin sources depths counts claim)
  ProgressAt := fun event content before after => PLift
    (event.Lawful sources depths counts ∧ event.claim sources depths counts = content ∧
      before = event.before sources depths counts ∧ after = event.after sources depths counts)
  MaintenanceAt := fun _ _ _ => PEmpty
  TypedDeferAt := fun _ _ _ => PEmpty
  ScopeNarrowingAt := fun _ _ _ => PEmpty
  TransferAcceptedAt := fun _ _ _ _ => PEmpty
  FulfilledAt := fun event content scope => PLift
    (event.Lawful sources depths counts ∧ event.claim sources depths counts = content ∧
      scope = claimOrigin sources depths counts content ∧ event.after sources depths counts = 0)
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

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
