import H0mework.Versions.AB.Chemistry.LAlanineBondReadout.ProducerSourceGeneratedBondReadout

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

structure BondMaterial where
  physical : JointNext.Runtime.JointResult
  history : Reentry.Runtime.ReentryHistory
  pair : Interface.ASUHeavyPair → Interface.PairPhysicalReadout
  pairReceipt : Interface.ASUHeavyPair → String
  sourceTrace : String

def generatedBondMaterial : BondMaterial :=
  ⟨bondParentResult, bondParentHistory, Source.pairReadoutAt, Source.pairReceiptText, Source.sourcePacketText⟩

inductive BondProjection
  | material | certificate

def bondProjectionLaw : SourceNativeProjectionLaw BondLedger where
  Projection := BondProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt BondLedger.source occurrence × BondMaterial
    | .certificate => PLift Producer.bondReadoutClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (BondLedger.ledgerCompiler.compile occurrence, generatedBondMaterial)
    | certificate => exact ⟨Producer.sourceGeneratedBondReadout⟩

def bondAuthoritySource := BondBase.withProjectionCoface bondProjectionLaw

def bondComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt bondProjectionLaw bondAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface BondBase bondProjectionLaw

def bondInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt BondBase.projectionLaw bondAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface BondBase bondProjectionLaw

def bondAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := bondAuthoritySource
  emitted := Reentry.Runtime.reentryEmitted
  compiler_commutes := Reentry.Runtime.reentryAuthoritativeRoot.compiler_commutes

def bondLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  bondAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem bond_restructuring_unchanged :
    bondAuthoritySource.restructuringSource = BondBase.restructuringSource := rfl

theorem bond_lawSurface_unchanged : bondAuthoritySource.lawSurface = BondBase.lawSurface := rfl

theorem bond_emitted_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    bondAuthoritativeRoot.emitted current = Reentry.Runtime.reentryAuthoritativeRoot.emitted current := rfl

theorem bond_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    bondAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      Reentry.Runtime.reentryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BondReadout.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
