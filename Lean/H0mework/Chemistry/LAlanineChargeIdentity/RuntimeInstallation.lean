import H0mework.Chemistry.LAlanineChargeIdentity.ProducerSourceGeneratedChargeIdentity
import H0mework.Realization.Faces.ProjectionCoface

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

structure ChargeMaterial where
  parent : BondReadout.Runtime.BondMaterial
  decoded : Force.Interface.Atom → Int
  sourceTrace : String

def generatedChargeMaterial : ChargeMaterial :=
  ⟨chargeParentMaterial, Source.decodedCharge, Source.sourcePacketText⟩

inductive ChargeProjection
  | material | certificate

def chargeProjectionLaw : SourceNativeProjectionLaw ChargeLedger where
  Projection := ChargeProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt ChargeLedger.source occurrence × ChargeMaterial
    | .certificate => PLift Producer.chargeIdentityClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (ChargeLedger.ledgerCompiler.compile occurrence, generatedChargeMaterial)
    | certificate => exact ⟨Producer.sourceGeneratedChargeIdentity⟩

def chargeAuthoritySource := ChargeBase.withProjectionCoface chargeProjectionLaw

def chargeComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt chargeProjectionLaw chargeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ChargeBase chargeProjectionLaw

def chargeInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt ChargeBase.projectionLaw chargeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ChargeBase chargeProjectionLaw

def chargeAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := chargeAuthoritySource
  emitted := BondReadout.Runtime.bondAuthoritativeRoot.emitted
  compiler_commutes := BondReadout.Runtime.bondAuthoritativeRoot.compiler_commutes

def chargeLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  chargeAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem charge_source_and_law_unchanged :
    chargeAuthoritySource.restructuringSource = ChargeBase.restructuringSource ∧
    chargeAuthoritySource.lawSurface = ChargeBase.lawSurface := ⟨rfl, rfl⟩

theorem charge_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    chargeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      BondReadout.Runtime.bondAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.ChargeIdentity.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
