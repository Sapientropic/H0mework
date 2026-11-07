import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Events

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle ComplementObservation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

/-- The existing native responsibility vocabulary, conservatively extended
only in its source, claim and generated-actor coordinates. -/
abbrev vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event input depth count
  Content := Claim input depth count
  Residual := Financial.Balance input
  Bearer := Interface.Actors.Image input depth count
  ProtectedInterest := Claim input depth count
  Scope := Origin input depth count
  Lineage := Origin input depth count
  Incidence := Origin input depth count
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    ((event.claim input depth count).origin input depth count)
    ((event.claim input depth count).origin input depth count)
  sourceIncidence := fun event => (event.claim input depth count).origin input depth count
  ObstructionAt := fun _ => PEmpty
  demandContent := fun impossible => impossible.elim
  demandResidual := fun impossible => impossible.elim
  CommitmentAt := Event.CommitmentAt input depth count
  MandateOriginAt := fun _ _ => PEmpty
  AcceptedTaskAt := fun _ _ => PEmpty
  ActiveDependencyAt := fun _ _ => PEmpty
  ProtectedRiskAt := fun _ _ => PEmpty
  AdmissionAuthorityAt := fun event scope => PLift (scope =
    (event.claim input depth count).origin input depth count)
  AcceptedAt := fun bearer event scope => PLift
    (bearer = (event.claim input depth count).debtorActor input depth count ∧
      scope = (event.claim input depth count).origin input depth count)
  StandingMandateAt := fun _ _ _ => PEmpty
  DischargeJurisdiction := fun claim scope => PLift (scope = claim.origin input depth count)
  ProgressAt := fun event content before after => PLift
    (event.Lawful input depth count ∧ event.claim input depth count = content ∧
      before = event.before input depth count ∧ after = event.after input depth count)
  MaintenanceAt := fun _ _ _ => PEmpty
  TypedDeferAt := fun _ _ _ => PEmpty
  ScopeNarrowingAt := fun _ _ _ => PEmpty
  TransferAcceptedAt := fun _ _ _ _ => PEmpty
  FulfilledAt := fun event content scope => PLift
    (event.Lawful input depth count ∧ event.claim input depth count = content ∧
      scope = content.origin input depth count ∧ event.after input depth count = 0)
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
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance
