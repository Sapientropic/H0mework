import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Source

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

abbrev ParentBase := Spatial.Runtime.authoritySource
abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource
abbrev Ready := Spatial.Runtime.Ready

inductive Projection
  | material | certificate

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {current} _ => PLift (Ready current)
  InactiveAt := fun _ {current} _ => PLift (¬Ready current)
  classify := by
    classical
    exact fun _ {current} _ => if h : Ready current then .inl ⟨h⟩ else .inr ⟨h⟩
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × Coulomb.Material
    | .certificate => PLift (Coulomb.Closure (materialOf (ReceiverBody.Runtime.currentResult current)))
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,
        materialOf (ReceiverBody.Runtime.currentResult current))
    | certificate =>
      cases current with
      | ingress => exact False.elim active.down
      | ready result =>
        have equal : result=ReceiverBody.Runtime.sourceOutput := active.down
        subst result
        exact ⟨sourceClosure⟩

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN ReceiverBody.Runtime.BodyV where
  source := authoritySource
  emitted := Spatial.Runtime.authoritativeRoot.emitted
  compiler_commutes := Spatial.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure RecoveryN ReceiverBody.Runtime.BodyV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource=ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission=ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface=ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem rootCompiler_unchanged (current : ReceiverBody.Runtime.BodyCurrent) :
    authoritativeRoot.toLedgerRoot.generatedLedgerAt current=
      Spatial.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Runtime
