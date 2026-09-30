import H0mework.Chemistry.LAlanineForce.NativeForceRenewal

/-!
# Electronic propagation on the original L-alanine row

The force target supplies the material source. The electronic source generates
its density at the fixed duration; the renewal retains this native operator.
The all-time law is a mathematical readout, while the standing stores one slice.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Root

noncomputable section

open _root_.SaturationMonoid.ProcessGame
open _root_.SaturationMonoid.ProcessGame.Society.Renewal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root

inductive ElectronicRenewalSeed where
  | settleNativeElectronicNext
  deriving DecidableEq, Repr

def electronicSeedAt (source : LocalSource) (stage : LAlanineStage)
    (_seed : ElectronicRenewalSeed) : Prop :=
  source = LAlanine40K2025.Source.key ∧ stage = .forceDrivenMaterialNextCertified

def electronicSourceSeed :
    SourceSeed occurrenceOf ElectronicRenewalSeed electronicSeedAt game.source := by
  refine ⟨.settleNativeElectronicNext, ?_⟩
  refine ⟨.forceDrivenMaterialNextCertified, ?_, rfl, rfl⟩
  decide

/-- Both raw matrix coordinates and the preceding material update remain available. -/
structure ElectronicRenewalConsumerAt
    (_seed : SourceSeed occurrenceOf ElectronicRenewalSeed electronicSeedAt game.source) : Type where
  sourceMatrices : Interface.ElectronicPropagationSource
  sourceMatricesExact : sourceMatrices = Source.electronicSource
  materialSource : Force.Interface.NuclearUpdateReadout
  materialSourceExact : materialSource = Force.Source.updateReadout

/-- The only target operator is the source law's fixed-duration slice. -/
structure ElectronicRenewalDispositionAt
    (_seed : SourceSeed occurrenceOf ElectronicRenewalSeed electronicSeedAt game.source) : Type where
  target : LAlanineStage
  targetExact : target = .electronicPropagationCertified
  nativeTarget : Dynamics.ElectronicOperator
  nativeTargetExact : nativeTarget = Dynamics.densityEvolution Source.electronicSource 1
  electronicPropagation : Producer.SourceGeneratedLAlanineElectronicPropagationCrown

def electronicRenewalConsumer : ElectronicRenewalConsumerAt electronicSourceSeed :=
  ⟨Source.electronicSource, rfl, Force.Source.updateReadout, rfl⟩

def electronicRenewalDisposition : ElectronicRenewalDispositionAt electronicSourceSeed :=
  ⟨.electronicPropagationCertified, rfl, Producer.nativeElectronicNext, rfl,
    Producer.sourceGeneratedLAlanineElectronicPropagation_crown⟩

def electronicRenewalRootShell : SourceNativeRenewalRootShellAt ledgerSource where
  ActiveAt := fun {current} _occurrence => electronicProjectionActiveAt current
  InactiveAt := fun {current} _occurrence => electronicProjectionInactiveAt current
  classify := by
    intro current _occurrence
    cases current with
    | targetErasedDensityBCPCensusFrozen => exact .inr PUnit.unit
    | physicalChemicalBondIncidenceCertified => exact .inr PUnit.unit
    | molecularEnergyLedgerCertified => exact .inr PUnit.unit
    | forceDrivenMaterialNextCertified => exact .inl PUnit.unit
    | electronicPropagationCertified => exact .inr PUnit.unit
    | nativeElectronicCurrent _time => exact .inr PUnit.unit
  sourceEntry := fun occurrence _active => sourceEntryAt occurrence
  selectedRow := fun occurrence _active => sourceRow occurrence
  successor := fun occurrence _active => successor occurrence
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence leftActive rightActive
    cases leftCurrent with
    | targetErasedDensityBCPCensusFrozen => exact nomatch leftActive
    | physicalChemicalBondIncidenceCertified => exact nomatch leftActive
    | molecularEnergyLedgerCertified => exact nomatch leftActive
    | forceDrivenMaterialNextCertified =>
        cases rightCurrent with
        | targetErasedDensityBCPCensusFrozen => exact nomatch rightActive
        | physicalChemicalBondIncidenceCertified => exact nomatch rightActive
        | molecularEnergyLedgerCertified => exact nomatch rightActive
        | forceDrivenMaterialNextCertified =>
            cases occurrence_unique leftOccurrence rightOccurrence
            rfl
        | electronicPropagationCertified => exact nomatch rightActive
        | nativeElectronicCurrent _time => exact nomatch rightActive
    | electronicPropagationCertified => exact nomatch leftActive
    | nativeElectronicCurrent _time => exact nomatch leftActive

def electronicRenewalLaw : SourceNativeRenewalProjectionLaw ledgerSource game
    ElectronicRenewalSeed electronicSeedAt ElectronicRenewalConsumerAt
      ElectronicRenewalDispositionAt :=
  SourceNativeRenewalProjectionLaw.ofRootShell electronicRenewalRootShell electronicSourceSeed
    electronicRenewalConsumer electronicRenewalDisposition

end

end LAlanine40K2025.Propagation.Root
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
