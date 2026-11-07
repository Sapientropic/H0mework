import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Obligation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def admission : Claim input depth count → NativeAdmissionPayload (vocabulary input depth count)
  | .inl claim => Legacy.payload input depth count (Financial.admission input claim)
  | .inr claim => {
      sourceEvent := .birth claim
      content := .inr claim
      residual := claimInitial input depth count (.inr claim)
      bearer := claim.debtorBirth.actor input depth count
      beneficiary := .inr claim
      scope := .epoch claim.origin
      lineage := .epoch claim.origin
      anchor_scope_eq := rfl
      anchor_lineage_eq := rfl
      origin := .explicitCommitment ⟨rfl⟩
      authority := ⟨rfl⟩
      assumption := .accepted ⟨rfl, rfl⟩
      dischargeJurisdiction := ⟨rfl⟩ }

structure Boundary (obligation : AdmittedObligation (vocabulary input depth count)) where
  event : Event input depth count
  lawful : event.Lawful input depth count
  content_eq : event.claim input depth count = obligation.content
  before_eq : obligation.residual = event.before input depth count
  owns : SourceOwnsResponsibilityIncidence (vocabulary input depth count) event obligation
  scope_eq : obligation.scope = obligation.content.origin input depth count

def boundaryDisposition {obligation : AdmittedObligation (vocabulary input depth count)}
    (boundary : Boundary input depth count obligation) :
    BoundaryDisposition (vocabulary input depth count) obligation boundary.event :=
  if cleared : boundary.event.after input depth count = 0 then
    .terminal (.final (.fulfilled ⟨boundary.lawful, boundary.content_eq, boundary.scope_eq, cleared⟩))
  else .carry (.progressed (boundary.event.after input depth count)
    ⟨boundary.lawful, boundary.content_eq, boundary.before_eq, rfl⟩)

def process : NativeResponsibilityProcess (vocabulary input depth count) where
  AdmissionEvent := Claim input depth count
  admissionPayload := admission input depth count
  BoundaryEvent := Boundary input depth count
  boundarySource := fun boundary => boundary.event
  boundary_anchor_eq := fun boundary => boundary.owns.anchor_eq
  boundary_incidence_eq := fun boundary => boundary.owns.incidence_eq
  boundaryDisposition := boundaryDisposition input depth count
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun impossible => impossible.elim

def Legacy.boundary {old : AdmittedObligation (Financial.vocabulary input)}
    (boundary : Financial.Boundary input old) :
    Boundary input depth count (Legacy.obligation input depth count old) where
  event := .legacy boundary.event
  lawful := boundary.lawful
  content_eq := congrArg Sum.inl boundary.content_eq
  before_eq := boundary.before_eq
  owns := {
    anchor_eq := by
      have same : (boundary.event.claim input).origin = (old.admission.sourceEvent.claim input).origin :=
        congrArg MinimalRegistrableSourceAnchor.scope boundary.owns.anchor_eq
      exact congrArg (fun original : Financial.InstructionOrigin input =>
        MinimalRegistrableSourceAnchor.canonical
          (Origin.original original : Origin input depth count) (Origin.original original)) same
    incidence_eq := congrArg Origin.original boundary.owns.incidence_eq }
  scope_eq := congrArg Origin.original boundary.scope_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance
