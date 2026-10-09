import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionLedger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionReadouts
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Producer.SourceGeneratedStrictRefill

/-! # One recovery authority installs its complete dependent face before emission -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Load.Source Load.Producer Recovery.Producer Recovery.StrictRefill

noncomputable section

private def recoveryRestructuringLaw : SourceNativeLedgerRestructuringLaw recoverySource :=
  identityOnlyWorldLedgerRestructuringLaw recoverySource LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility, left⟩ : OpenResponsibilityAt RecoveryN support) =
        ⟨responsibility, right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def recoveryRestructuringCompiler : SourceNativeRestructuringLedgerCompiler recoverySource where
  ledgerCompiler := recoveryLedgerCompiler
  restructuringLaw := recoveryRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def recoveryRestructuringSource : SourceNativeRestructuringLedgerSource RecoveryN RecoveryV where
  source := recoverySource
  compiler := recoveryRestructuringCompiler

inductive RecoveryProjection
  | current
  | next
  | joint
  | control
  | energies
  | energyBalance
  | entropy
  | entropyDisposition
  | freeEnergy
  | netAccount
  | capacities
  | firstRecovery
  | wholeLedger

def recoveryProjectionLaw : SourceNativeProjectionLaw recoveryRestructuringSource.toLedgerSource where
  Projection := RecoveryProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstRecovery => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstRecovery => match current with | .ingress => PEmpty | .running _ => PUnit
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    cases current with
    | ingress => exact .inl PUnit.unit
    | running _ => exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .current | .next => LoadState
    | .joint => LoadedJoint × LoadedJoint × PLift (type_of% (recoveryNext_joint current))
    | .control => RecoveryControlRead × PLift (type_of% (recoveryControl_work current) ∧
        type_of% (recoveryControl_duration_positive current) ∧ type_of% (recoveryNext_clock current))
    | .energies => RecoveryEnergyRead × RecoveryEnergyRead
    | .energyBalance => PLift (type_of% (recoveryNext_energyBalance current) ∧
        type_of% (recoveryNext_workBalance current))
    | .entropy | .freeEnergy => (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)
    | .entropyDisposition => PLift
        (type_of% (loadEntropy_disposition (recoveryCurrentState (recoveryNext current))) ∧
          0 ≤ loadEntropyProduction (recoveryCurrentState (recoveryNext current)))
    | .netAccount => ℝ × ℝ × PLift (type_of% (recoveryNext_netAccount current))
    | .capacities => RecoveryCapacityRead × RecoveryCapacityRead
    | .firstRecovery => PLift (type_of% sourceGeneratedRecovery ∧ type_of% sourceGeneratedStrictRefill ∧
        type_of% (recoveryStep_entropy recoveryReceivedState) ∧
        type_of% (recoveryStep_gibbs recoveryReceivedState) ∧
        type_of% (recoveryStep_environmentEnergy recoveryReceivedState))
    | .wholeLedger => SourceNativeLedgerEvolutionAt recoverySource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => recoveryCurrentState current
    | .next => recoveryCurrentState (recoveryNext current)
    | .joint => ((recoveryCurrentState current).joint,
        (recoveryCurrentState (recoveryNext current)).joint, ⟨recoveryNext_joint current⟩)
    | .control => (recoveryControlRead current, ⟨recoveryControl_work current,
        recoveryControl_duration_positive current, recoveryNext_clock current⟩)
    | .energies => (recoveryEnergyRead (recoveryCurrentState current),
        recoveryEnergyRead (recoveryCurrentState (recoveryNext current)))
    | .energyBalance => ⟨recoveryNext_energyBalance current, recoveryNext_workBalance current⟩
    | .entropy => (Load.Runtime.loadEntropyRead (recoveryCurrentState current),
        Load.Runtime.loadEntropyRead (recoveryCurrentState (recoveryNext current)))
    | .entropyDisposition => ⟨loadEntropy_disposition (recoveryCurrentState (recoveryNext current)),
        loadEntropy_nonnegative (recoveryCurrentState (recoveryNext current))⟩
    | .freeEnergy => (Load.Runtime.loadFreeEnergyRead (recoveryCurrentState current),
        Load.Runtime.loadFreeEnergyRead (recoveryCurrentState (recoveryNext current)))
    | .netAccount => (recoveryEventWork current, recoveryAccumulatedWork current,
        ⟨recoveryNext_netAccount current⟩)
    | .capacities => (recoveryCapacityRead (recoveryCurrentState current),
        recoveryCapacityRead (recoveryCurrentState (recoveryNext current)))
    | .firstRecovery => ⟨sourceGeneratedRecovery, sourceGeneratedStrictRefill, recoveryStep_entropy recoveryReceivedState,
        recoveryStep_gibbs recoveryReceivedState, recoveryStep_environmentEnergy recoveryReceivedState⟩
    | .wholeLedger => recoveryLedgerCompiler.compile occurrence

def recoveryAuthoritySource : SourceNativeAuthoritySource RecoveryN RecoveryV where
  restructuringSource := recoveryRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal recoveryRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := recoveryProjectionLaw

def recoveryAuthoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN RecoveryV where
  source := recoveryAuthoritySource
  emitted := recoveryEmitted
  compiler_commutes := fun _ => rfl

def recoveryLivingRoot : SourceNativeLivingRootClosure RecoveryN RecoveryV :=
  recoveryAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def recoveryInitialVisit : SourceNativeTemporalVisitAt recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite recoveryLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def recoveryInitialGenerated :=
  recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit recoveryInitialVisit

def recoveryInitialEntry := recoveryEntry (recoveryCurrentSupport .ingress)

def recoveryInitialEntryRow : recoveryInitialGenerated.GeneratedEntryRowAt recoveryInitialEntry :=
  (recoveryInitialGenerated.canonicalGeneratedEntryRow? recoveryInitialEntry).get (by rfl)

def recoveryFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    recoveryInitialGenerated.occurrence recoveryInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? recoveryInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
