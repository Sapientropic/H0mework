import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding.Payload

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat)

def admission (claim : Claim sources depths counts) :
    NativeAdmissionPayload (vocabulary sources depths counts) :=
  Embedding.payload sources depths counts claim.1
    (Finance.admission (sources claim.1) (depths claim.1) (counts claim.1) claim.2)

structure Boundary (obligation : AdmittedObligation (vocabulary sources depths counts)) where
  event : Event sources depths counts
  lawful : event.Lawful sources depths counts
  content_eq : event.claim sources depths counts = obligation.content
  before_eq : obligation.residual = event.before sources depths counts
  owns : SourceOwnsResponsibilityIncidence (vocabulary sources depths counts) event obligation
  scope_eq : obligation.scope = claimOrigin sources depths counts obligation.content

def boundaryDisposition {obligation : AdmittedObligation (vocabulary sources depths counts)}
    (boundary : Boundary sources depths counts obligation) :
    BoundaryDisposition (vocabulary sources depths counts) obligation boundary.event :=
  if cleared : boundary.event.after sources depths counts = 0 then
    .terminal (.final (.fulfilled ⟨boundary.lawful, boundary.content_eq, boundary.scope_eq, cleared⟩))
  else .carry (.progressed (boundary.event.after sources depths counts)
    ⟨boundary.lawful, boundary.content_eq, boundary.before_eq, rfl⟩)

/-- One common native process extends the original epoch account. Birth
and review still come from their literal source epochs, with no reset edge. -/
def process : NativeResponsibilityProcess (vocabulary sources depths counts) where
  AdmissionEvent := Claim sources depths counts
  admissionPayload := admission sources depths counts
  BoundaryEvent := Boundary sources depths counts
  boundarySource := fun boundary => boundary.event
  boundary_anchor_eq := fun boundary => boundary.owns.anchor_eq
  boundary_incidence_eq := fun boundary => boundary.owns.incidence_eq
  boundaryDisposition := boundaryDisposition sources depths counts
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun impossible => impossible.elim

#print axioms process

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family
