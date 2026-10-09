import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadActionLedger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadFreeEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineStrictThermalCost
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.InitialHeatJet

/-! # The controlled law installs its material and quantitative consumers before emission -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source

noncomputable section

private def loadRestructuringLaw : SourceNativeLedgerRestructuringLaw loadSource :=
  identityOnlyWorldLedgerRestructuringLaw loadSource LAlanine40K2025.Source.key (by
    intro support responsibility
    cases support with
    | inl poweredSupport =>
      cases poweredSupport with
      | inl fieldSupport =>
        cases fieldSupport with
        | inl stage => exact Root.networkOpenAtSubsingleton stage responsibility
        | inr _ => exact inferInstanceAs (Subsingleton PUnit)
      | inr _ => exact inferInstanceAs (Subsingleton PUnit)
    | inr _ =>
      change Subsingleton PUnit
      infer_instance)

private def loadRestructuringCompiler : SourceNativeRestructuringLedgerCompiler loadSource where
  ledgerCompiler := loadLedgerCompiler
  restructuringLaw := loadRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (loadEntry_unique _ left).trans (loadEntry_unique _ right).symm)
    (fun left right _ => (loadEntry_unique _ left).trans (loadEntry_unique _ right).symm)

def loadRestructuringSource : SourceNativeRestructuringLedgerSource LoadN LoadV where
  source := loadSource
  compiler := loadRestructuringCompiler

inductive LoadProjection
  | initial
  | current
  | next
  | pcEnergy
  | environmentEnergy
  | boundaryEnergy
  | energyBalance
  | entropy
  | entropyDisposition
  | signedEntropy
  | freeEnergy
  | freeEnergyBalance
  | initialStrictCost
  | wholeLedger

def loadEntropyRead (current : LoadState) : ℝ × ℝ × ℝ :=
  (loadEntropyProduction current, loadMutualInformation current, loadGibbsExcess current)

def loadFreeEnergyRead (current : LoadState) : ℝ × ℝ × ℝ :=
  (loadPCEntropy current, loadPCFreeEnergy current, loadBindingAccountedFreeEnergy current)

def loadProjectionLaw : SourceNativeProjectionLaw loadRestructuringSource.toLedgerSource where
  Projection := LoadProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .initialStrictCost => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .initialStrictCost => match current with | .ingress => PEmpty | .running _ => PUnit
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    cases current with
    | ingress => exact .inl PUnit.unit
    | running _ => exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .initial | .current | .next => LoadState
    | .pcEnergy | .environmentEnergy | .boundaryEnergy => ℝ
    | .energyBalance => PLift (type_of% (loadStateNext_energyBalance (loadCurrentState current)))
    | .entropy | .freeEnergy => (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)
    | .entropyDisposition => PLift (type_of% (loadEntropy_disposition (loadStateNext (loadCurrentState current))) ∧
        0 ≤ loadEntropyProduction (loadStateNext (loadCurrentState current)))
    | .signedEntropy => ℝ × PLift (type_of% (loadStateNext_signedEntropy (loadCurrentState current)))
    | .freeEnergyBalance => PLift (loadEntropyProduction loadInitialState = 0 ∧
        type_of% (loadStateNext_freeEnergyBalance (loadCurrentState current)))
    | .initialStrictCost => PLift (type_of% loadFirst_sourceGeneratedThermodynamicCost ∧
        type_of% loadFirstEnvironmentHeat_deriv_zero ∧ type_of% loadFirstEnvironmentHeat_secondDeriv)
    | .wholeLedger => SourceNativeLedgerEvolutionAt loadSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .initial => loadInitialState
    | .current => loadCurrentState current
    | .next => loadStateNext (loadCurrentState current)
    | .pcEnergy => pcEnergy (loadCurrentState current).joint
    | .environmentEnergy => environmentEnergy (loadCurrentState current).joint
    | .boundaryEnergy => boundaryEnergy (loadCurrentState current).joint
    | .energyBalance => ⟨loadStateNext_energyBalance (loadCurrentState current)⟩
    | .entropy => (loadEntropyRead (loadCurrentState current),
        loadEntropyRead (loadStateNext (loadCurrentState current)))
    | .entropyDisposition => ⟨loadEntropy_disposition (loadStateNext (loadCurrentState current)),
        loadEntropy_nonnegative (loadStateNext (loadCurrentState current))⟩
    | .signedEntropy => (loadEntropyProduction (loadStateNext (loadCurrentState current)) -
        loadEntropyProduction (loadCurrentState current), ⟨loadStateNext_signedEntropy (loadCurrentState current)⟩)
    | .freeEnergy => (loadFreeEnergyRead (loadCurrentState current),
        loadFreeEnergyRead (loadStateNext (loadCurrentState current)))
    | .freeEnergyBalance => ⟨loadEntropy_initial_zero, loadStateNext_freeEnergyBalance (loadCurrentState current)⟩
    | .initialStrictCost => ⟨loadFirst_sourceGeneratedThermodynamicCost,
        loadFirstEnvironmentHeat_deriv_zero, loadFirstEnvironmentHeat_secondDeriv⟩
    | .wholeLedger => loadLedgerCompiler.compile occurrence

def loadAuthoritySource : SourceNativeAuthoritySource LoadN LoadV where
  restructuringSource := loadRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal loadRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic LoadN
  projectionLaw := loadProjectionLaw

def loadAuthoritativeRoot : SourceNativeAuthoritativeRootClosure LoadN LoadV where
  source := loadAuthoritySource
  emitted := loadEmitted
  compiler_commutes := fun _ => rfl

def loadLivingRoot : SourceNativeLivingRootClosure LoadN LoadV :=
  loadAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def loadInitialVisit : SourceNativeTemporalVisitAt loadLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite loadLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def loadInitialGenerated :=
  loadLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit loadInitialVisit

def loadInitialEntry := loadEntry (loadCurrentSupport .ingress)

def loadInitialEntryRow : loadInitialGenerated.GeneratedEntryRowAt loadInitialEntry :=
  (loadInitialGenerated.canonicalGeneratedEntryRow? loadInitialEntry).get (by rfl)

def loadFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    loadInitialGenerated.occurrence loadInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? loadInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
