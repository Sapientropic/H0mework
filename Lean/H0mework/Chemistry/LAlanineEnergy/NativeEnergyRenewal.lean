import H0mework.Chemistry.LAlanineSource.NativeBondDensityRoot

/-!
# Same-root molecular-energy renewal

The already generated bond-incidence current opens its energy coordinate on
the original one-row ledger. Density and energy remain material readouts of
the same calculation, not separate roots or molecular time steps.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Energy.Root

noncomputable section

open _root_.SaturationMonoid.ProcessGame
open _root_.SaturationMonoid.ProcessGame.Society.Renewal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root

inductive EnergyRenewalSeed where
  | settleSameCalculationEnergyLedger
  deriving DecidableEq, Repr

def energySeedAt (source : LocalSource) (stage : LAlanineStage)
    (_seed : EnergyRenewalSeed) : Prop :=
  source = LAlanine40K2025.Source.key ∧
    stage = .physicalChemicalBondIncidenceCertified

def energySourceSeed :
    SourceSeed occurrenceOf EnergyRenewalSeed energySeedAt game.source := by
  refine ⟨.settleSameCalculationEnergyLedger, ?_⟩
  refine ⟨.physicalChemicalBondIncidenceCertified, ?_, rfl, rfl⟩
  decide

/-- The consumer retains both material outputs, with their exact source binding. -/
structure EnergyRenewalConsumerAt
    (_seed : SourceSeed occurrenceOf EnergyRenewalSeed energySeedAt game.source) : Type where
  density : LAlanine40K2025.Interface.SourceRecordedTargetErasedDensityAt
  densityExact : density = LAlanine40K2025.Source.sourceRecorded
  ledger : Interface.MolecularEnergyLedger
  ledgerExact : ledger = Source.energyLedger

structure EnergyRenewalDispositionAt
    (_seed : SourceSeed occurrenceOf EnergyRenewalSeed energySeedAt game.source) : Type where
  target : LAlanineStage
  targetExact : target = .molecularEnergyLedgerCertified
  energy : Producer.SourceGeneratedLAlanineEnergyCrown

def energyRenewalConsumer : EnergyRenewalConsumerAt energySourceSeed :=
  ⟨LAlanine40K2025.Source.sourceRecorded, rfl, Source.energyLedger, rfl⟩

def energyRenewalDisposition : EnergyRenewalDispositionAt energySourceSeed :=
  ⟨.molecularEnergyLedgerCertified, rfl, Producer.sourceGeneratedLAlanineEnergy_crown⟩

def energyRenewalRootShell : SourceNativeRenewalRootShellAt ledgerSource where
  ActiveAt := fun {current} _occurrence => energyProjectionActiveAt current
  InactiveAt := fun {current} _occurrence => energyProjectionInactiveAt current
  classify := by
    intro current _occurrence
    cases current with
    | targetErasedDensityBCPCensusFrozen => exact .inr PUnit.unit
    | physicalChemicalBondIncidenceCertified => exact .inl PUnit.unit
    | molecularEnergyLedgerCertified => exact .inr PUnit.unit
    | forceDrivenMaterialNextCertified => exact .inr PUnit.unit
    | electronicPropagationCertified => exact .inr PUnit.unit
    | nativeElectronicCurrent _time => exact .inr PUnit.unit
  sourceEntry := fun occurrence _active => sourceEntryAt occurrence
  selectedRow := fun occurrence _active => sourceRow occurrence
  successor := fun occurrence _active => successor occurrence
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence leftActive rightActive
    cases leftCurrent with
    | targetErasedDensityBCPCensusFrozen => exact nomatch leftActive
    | physicalChemicalBondIncidenceCertified =>
        cases rightCurrent with
        | targetErasedDensityBCPCensusFrozen => exact nomatch rightActive
        | physicalChemicalBondIncidenceCertified =>
            cases occurrence_unique leftOccurrence rightOccurrence
            rfl
        | molecularEnergyLedgerCertified => exact nomatch rightActive
        | forceDrivenMaterialNextCertified => exact nomatch rightActive
        | electronicPropagationCertified => exact nomatch rightActive
        | nativeElectronicCurrent _time => exact nomatch rightActive
    | molecularEnergyLedgerCertified => exact nomatch leftActive
    | forceDrivenMaterialNextCertified => exact nomatch leftActive
    | electronicPropagationCertified => exact nomatch leftActive
    | nativeElectronicCurrent _time => exact nomatch leftActive

def energyRenewalLaw : SourceNativeRenewalProjectionLaw ledgerSource game
    EnergyRenewalSeed energySeedAt EnergyRenewalConsumerAt EnergyRenewalDispositionAt :=
  SourceNativeRenewalProjectionLaw.ofRootShell energyRenewalRootShell energySourceSeed
    energyRenewalConsumer energyRenewalDisposition

end

end LAlanine40K2025.Energy.Root
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
