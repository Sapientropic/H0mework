import H0mework.Versions.AB.Chemistry.LAlanineEnergy.NativeEnergyRenewal

/-!
# Force-driven material renewal on the original L-alanine row

The energy-certified current opens a material-update coordinate of the same
root. Its target positions are computed from source positions and gradient;
the whole-ledger successor remains a research-source settlement, not an
empirically observed molecular trajectory.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Force.Root

noncomputable section

open _root_.SaturationMonoid.ProcessGame
open _root_.SaturationMonoid.ProcessGame.Society.Renewal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root

inductive ForceRenewalSeed where
  | settleForceGeneratedMaterialNext
  deriving DecidableEq, Repr

def forceSeedAt (source : LocalSource) (stage : LAlanineStage)
    (_seed : ForceRenewalSeed) : Prop :=
  source = LAlanine40K2025.Source.key ∧ stage = .molecularEnergyLedgerCertified

def forceSourceSeed :
    SourceSeed occurrenceOf ForceRenewalSeed forceSeedAt game.source := by
  refine ⟨.settleForceGeneratedMaterialNext, ?_⟩
  refine ⟨.molecularEnergyLedgerCertified, ?_, rfl, rfl⟩
  decide

/-- The consumer keeps the actual update and its previously settled source energy. -/
structure ForceRenewalConsumerAt
    (_seed : SourceSeed occurrenceOf ForceRenewalSeed forceSeedAt game.source) : Type where
  update : Interface.NuclearUpdateReadout
  updateExact : update = Source.updateReadout
  sourceEnergy : Energy.Interface.MolecularEnergyLedger
  sourceEnergyExact : sourceEnergy = Energy.Source.energyLedger

/-- Material next is calculated here; no caller-selected target enters the renewal. -/
structure ForceRenewalDispositionAt
    (_seed : SourceSeed occurrenceOf ForceRenewalSeed forceSeedAt game.source) : Type where
  target : LAlanineStage
  targetExact : target = .forceDrivenMaterialNextCertified
  materialTarget : Interface.NuclearCoordinates
  materialTargetExact : materialTarget = Interface.generatedTarget
    Source.updateReadout.sourcePositions Source.updateReadout.gradient
  forceUpdate : Producer.SourceGeneratedLAlanineForceUpdateCrown

def forceRenewalConsumer : ForceRenewalConsumerAt forceSourceSeed :=
  ⟨Source.updateReadout, rfl, Energy.Source.energyLedger, rfl⟩

def forceRenewalDisposition : ForceRenewalDispositionAt forceSourceSeed :=
  ⟨.forceDrivenMaterialNextCertified, rfl,
    Interface.generatedTarget Source.updateReadout.sourcePositions Source.updateReadout.gradient,
    rfl, Producer.sourceGeneratedLAlanineForceUpdate_crown⟩

def forceRenewalRootShell : SourceNativeRenewalRootShellAt ledgerSource where
  ActiveAt := fun {current} _occurrence => forceProjectionActiveAt current
  InactiveAt := fun {current} _occurrence => forceProjectionInactiveAt current
  classify := by
    intro current _occurrence
    cases current with
    | targetErasedDensityBCPCensusFrozen => exact .inr PUnit.unit
    | physicalChemicalBondIncidenceCertified => exact .inr PUnit.unit
    | molecularEnergyLedgerCertified => exact .inl PUnit.unit
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
    | physicalChemicalBondIncidenceCertified => exact nomatch leftActive
    | molecularEnergyLedgerCertified =>
        cases rightCurrent with
        | targetErasedDensityBCPCensusFrozen => exact nomatch rightActive
        | physicalChemicalBondIncidenceCertified => exact nomatch rightActive
        | molecularEnergyLedgerCertified =>
            cases occurrence_unique leftOccurrence rightOccurrence
            rfl
        | forceDrivenMaterialNextCertified => exact nomatch rightActive
        | electronicPropagationCertified => exact nomatch rightActive
        | nativeElectronicCurrent _time => exact nomatch rightActive
    | forceDrivenMaterialNextCertified => exact nomatch leftActive
    | electronicPropagationCertified => exact nomatch leftActive
    | nativeElectronicCurrent _time => exact nomatch leftActive

def forceRenewalLaw : SourceNativeRenewalProjectionLaw ledgerSource game
    ForceRenewalSeed forceSeedAt ForceRenewalConsumerAt ForceRenewalDispositionAt :=
  SourceNativeRenewalProjectionLaw.ofRootShell forceRenewalRootShell forceSourceSeed
    forceRenewalConsumer forceRenewalDisposition

end

end LAlanine40K2025.Force.Root
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
