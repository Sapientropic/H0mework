import H0mework.Chemistry.LAlanineBasinPartition.ProducerSourceGeneratedBasinPartition
import H0mework.Realization.Faces.ProjectionCoface

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

structure BasinMaterial where
  parent : ChargeIdentity.Runtime.ChargeMaterial
  integral : SourceData.Bucket → SourceData.Field → Int
  count : SourceData.Bucket → Nat
  blockIntegrals : SourceData.GridBlock → SourceData.Bucket → SourceData.Field → Int
  blockCounts : SourceData.GridBlock → SourceData.Bucket → Nat
  sourceTrace : String

def generatedBasinMaterial : BasinMaterial :=
  ⟨basinParentMaterial, Calculation.basinIntegral, Calculation.basinCount,
    Source.bucketIntegrals, Source.bucketCounts, Source.sourcePacketText⟩

inductive BasinProjection
  | material | certificate

def basinProjectionLaw : SourceNativeProjectionLaw BasinLedger where
  Projection := BasinProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt BasinLedger.source occurrence × BasinMaterial
    | .certificate => PLift Producer.basinPartitionClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (BasinLedger.ledgerCompiler.compile occurrence, generatedBasinMaterial)
    | certificate => exact ⟨Producer.sourceGeneratedBasinPartition⟩

def basinAuthoritySource := BasinBase.withProjectionCoface basinProjectionLaw

def basinComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt basinProjectionLaw basinAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface BasinBase basinProjectionLaw

def basinInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt BasinBase.projectionLaw basinAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface BasinBase basinProjectionLaw

def basinAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := basinAuthoritySource
  emitted := ChargeIdentity.Runtime.chargeAuthoritativeRoot.emitted
  compiler_commutes := ChargeIdentity.Runtime.chargeAuthoritativeRoot.compiler_commutes

def basinLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  basinAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem basin_source_and_law_unchanged :
    basinAuthoritySource.restructuringSource = BasinBase.restructuringSource ∧
    basinAuthoritySource.lawSurface = BasinBase.lawSurface := ⟨rfl, rfl⟩

theorem basin_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    basinAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      ChargeIdentity.Runtime.chargeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinPartition.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
