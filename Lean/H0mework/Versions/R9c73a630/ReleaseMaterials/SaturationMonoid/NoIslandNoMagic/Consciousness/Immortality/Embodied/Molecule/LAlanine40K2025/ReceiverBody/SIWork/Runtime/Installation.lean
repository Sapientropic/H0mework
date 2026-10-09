import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

abbrev ParentBase := FiniteContinuation.Runtime.authoritySource
abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource

inductive Projection
  | work | certificate

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .work => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × WorkReadout
    | .certificate => PLift (CalibratedAction current)
  project := by
    intro projection current occurrence active
    cases projection with
    | work => exact (ParentLedger.ledgerCompiler.compile occurrence,workOf current.1)
    | certificate => exact ⟨calibratedAction current⟩

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN FiniteContinuation.Runtime.BodyV where
  source := authoritySource
  emitted := FiniteContinuation.Runtime.authoritativeRoot.emitted
  compiler_commutes := FiniteContinuation.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure RecoveryN FiniteContinuation.Runtime.BodyV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource=ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission=ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface=ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem rootCompiler_unchanged (current : FiniteContinuation.Runtime.State) :
    authoritativeRoot.toLedgerRoot.generatedLedgerAt current=
      FiniteContinuation.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime
