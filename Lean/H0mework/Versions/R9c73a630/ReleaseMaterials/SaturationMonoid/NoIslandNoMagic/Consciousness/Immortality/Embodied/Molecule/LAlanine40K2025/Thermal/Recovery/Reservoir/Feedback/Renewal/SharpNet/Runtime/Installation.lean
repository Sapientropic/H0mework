import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.SharpNet.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Runtime.Consumers
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.SharpNet.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
open LAlanine40K2025.Thermal.Recovery.Runtime
open LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime
noncomputable section

abbrev ParentBase := LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime.authoritySource
abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource

inductive Projection
  | comparison

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} occurrence _ =>
    SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × SharpNet.Material
  project := by
    intro projection current occurrence active
    cases projection
    exact (ParentLedger.ledgerCompiler.compile occurrence,SharpNet.material)

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN RenewalV where
  source := authoritySource
  emitted := LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime.authoritativeRoot.emitted
  compiler_commutes := LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure RecoveryN RenewalV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.SharpNet.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
