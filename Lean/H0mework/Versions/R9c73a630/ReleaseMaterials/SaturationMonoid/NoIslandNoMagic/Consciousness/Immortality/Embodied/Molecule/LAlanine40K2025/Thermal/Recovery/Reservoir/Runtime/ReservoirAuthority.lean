import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirReadouts
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedBodyReadoutKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedBodyMeasurement

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime
noncomputable section

private def reservoirRestructuringLaw : SourceNativeLedgerRestructuringLaw reservoirSource :=
  identityOnlyWorldLedgerRestructuringLaw reservoirSource LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility, left⟩ : OpenResponsibilityAt RecoveryN support) = ⟨responsibility, right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def reservoirRestructuringCompiler : SourceNativeRestructuringLedgerCompiler reservoirSource where
  ledgerCompiler := reservoirLedgerCompiler
  restructuringLaw := reservoirRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def reservoirRestructuringSource : SourceNativeRestructuringLedgerSource RecoveryN ReservoirV where
  source := reservoirSource
  compiler := reservoirRestructuringCompiler

inductive ReservoirProjection
  | current | next | joint | body | donor | control | energies | capacities
  | entropy | freeEnergy | netAccount | firstSupply | wholeLedger

def reservoirProjectionLaw : SourceNativeProjectionLaw reservoirRestructuringSource.toLedgerSource where
  Projection := ReservoirProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstSupply => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstSupply => match current with | .ingress => PEmpty | .running _ => PUnit
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    cases current with
    | ingress => exact .inl PUnit.unit
    | running _ => exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .current | .next => Current.State
    | .joint => Current.FullJoint × Current.FullJoint × PLift (type_of% (reservoirNext_joint current))
    | .body => Load.Source.LoadedJoint × Load.Source.LoadedJoint
    | .donor => Matrix Load.Source.PairController Load.Source.PairController ℂ ×
        Matrix Load.Source.PairController Load.Source.PairController ℂ
    | .control => ReservoirControlRead × PLift (type_of% (reservoirControl_work current) ∧
        type_of% (reservoirControl_exponential current) ∧ type_of% (reservoirControl_positive current) ∧
        type_of% (reservoirNext_clock current))
    | .energies => (ℝ × ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ × ℝ) ×
        PLift (type_of% (reservoirNext_energyBalance current))
    | .capacities => (ℝ × ℝ) × (ℝ × ℝ) ×
        PLift (type_of% (Readout.donor_available_range (reservoirCurrentState (reservoirNext current))))
    | .entropy => ℝ × ℝ × PLift (0 ≤ Current.entropyProduction (reservoirCurrentState (reservoirNext current)))
    | .freeEnergy => ℝ × ℝ
    | .netAccount => ℝ × ℝ × PLift (type_of% (reservoirNext_netAccount current))
    | .firstSupply => PLift (type_of% Producer.sourceGeneratedFiniteReservoir ∧
        type_of% BodyKernel.sourceGeneratedBodyReadoutKernel ∧ type_of% Measurement.sourceGeneratedBodyMeasurement)
    | .wholeLedger => SourceNativeLedgerEvolutionAt reservoirSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => reservoirCurrentState current
    | .next => reservoirCurrentState (reservoirNext current)
    | .joint => ((reservoirCurrentState current).joint, (reservoirCurrentState (reservoirNext current)).joint,
        ⟨reservoirNext_joint current⟩)
    | .body => (Incidence.bodyRead (reservoirCurrentState current).joint,
        Incidence.bodyRead (reservoirCurrentState (reservoirNext current)).joint)
    | .donor => (Readout.donorMatrix (reservoirCurrentState current),
        Readout.donorMatrix (reservoirCurrentState (reservoirNext current)))
    | .control => (reservoirControlRead current, ⟨reservoirControl_work current, reservoirControl_exponential current,
        reservoirControl_positive current, reservoirNext_clock current⟩)
    | .energies => (reservoirEnergyRead (reservoirCurrentState current),
        reservoirEnergyRead (reservoirCurrentState (reservoirNext current)), ⟨reservoirNext_energyBalance current⟩)
    | .capacities => (reservoirCapacityRead (reservoirCurrentState current),
        reservoirCapacityRead (reservoirCurrentState (reservoirNext current)),
        ⟨Readout.donor_available_range (reservoirCurrentState (reservoirNext current))⟩)
    | .entropy => (Current.entropyProduction (reservoirCurrentState current),
        Current.entropyProduction (reservoirCurrentState (reservoirNext current)),
        ⟨Current.entropyProduction_nonnegative _⟩)
    | .freeEnergy => (Thermo.freeEnergy (reservoirCurrentState current), Thermo.freeEnergy (reservoirCurrentState (reservoirNext current)))
    | .netAccount => (reservoirEventWork current, reservoirAccumulatedWork current, ⟨reservoirNext_netAccount current⟩)
    | .firstSupply => ⟨Producer.sourceGeneratedFiniteReservoir, BodyKernel.sourceGeneratedBodyReadoutKernel,
        Measurement.sourceGeneratedBodyMeasurement⟩
    | .wholeLedger => reservoirLedgerCompiler.compile occurrence

def reservoirAuthoritySource : SourceNativeAuthoritySource RecoveryN ReservoirV where
  restructuringSource := reservoirRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal reservoirRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := reservoirProjectionLaw

def reservoirAuthoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN ReservoirV where
  source := reservoirAuthoritySource
  emitted := reservoirEmitted
  compiler_commutes := fun _ => rfl

def reservoirLivingRoot : SourceNativeLivingRootClosure RecoveryN ReservoirV :=
  reservoirAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def reservoirInitialVisit : SourceNativeTemporalVisitAt reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite reservoirLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def reservoirInitialGenerated := reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit reservoirInitialVisit
def reservoirInitialEntry := recoveryEntry reservoirSupport

def reservoirInitialEntryRow : reservoirInitialGenerated.GeneratedEntryRowAt reservoirInitialEntry :=
  (reservoirInitialGenerated.canonicalGeneratedEntryRow? reservoirInitialEntry).get (by rfl)

def reservoirFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    reservoirInitialGenerated.occurrence reservoirInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? reservoirInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
