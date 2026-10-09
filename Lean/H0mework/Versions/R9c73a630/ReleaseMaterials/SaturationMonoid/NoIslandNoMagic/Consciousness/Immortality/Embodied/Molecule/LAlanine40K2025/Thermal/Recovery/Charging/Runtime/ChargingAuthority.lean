import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Runtime.ChargingReadouts

/-! # One charging authority installs its complete dependent face before emission -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Load.Source Load.Producer Recovery.Runtime
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Producer

noncomputable section

private def chargingRestructuringLaw : SourceNativeLedgerRestructuringLaw chargingSource :=
  identityOnlyWorldLedgerRestructuringLaw chargingSource LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility, left⟩ : OpenResponsibilityAt RecoveryN support) =
        ⟨responsibility, right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def chargingRestructuringCompiler : SourceNativeRestructuringLedgerCompiler chargingSource where
  ledgerCompiler := chargingLedgerCompiler
  restructuringLaw := chargingRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def chargingRestructuringSource : SourceNativeRestructuringLedgerSource RecoveryN ChargingV where
  source := chargingSource
  compiler := chargingRestructuringCompiler

inductive ChargingProjection
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
  | firstCharge
  | wholeLedger

def chargingProjectionLaw : SourceNativeProjectionLaw chargingRestructuringSource.toLedgerSource where
  Projection := ChargingProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstCharge => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstCharge => match current with | .ingress => PEmpty | .running _ => PUnit
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
    | .joint => LoadedJoint × LoadedJoint × PLift (type_of% (chargingNext_joint current))
    | .control => RecoveryControlRead × PLift (type_of% (chargingControl_work current) ∧
        type_of% (chargingControl_duration_positive current) ∧ type_of% (chargingNext_clock current))
    | .energies => RecoveryEnergyRead × RecoveryEnergyRead
    | .energyBalance => PLift (type_of% (chargingNext_energyBalance current) ∧
        type_of% (chargingNext_workBalance current))
    | .entropy | .freeEnergy => (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)
    | .entropyDisposition => PLift
        (type_of% (loadEntropy_disposition (chargingCurrentState (chargingNext current))) ∧
          0 ≤ loadEntropyProduction (chargingCurrentState (chargingNext current)))
    | .netAccount => ℝ × ℝ × PLift (type_of% (chargingNext_netAccount current))
    | .capacities => RecoveryCapacityRead × RecoveryCapacityRead
    | .firstCharge => PLift (type_of% sourceGeneratedWholePCCharging)
    | .wholeLedger => SourceNativeLedgerEvolutionAt chargingSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => chargingCurrentState current
    | .next => chargingCurrentState (chargingNext current)
    | .joint => ((chargingCurrentState current).joint,
        (chargingCurrentState (chargingNext current)).joint, ⟨chargingNext_joint current⟩)
    | .control => (chargingControlRead current, ⟨chargingControl_work current,
        chargingControl_duration_positive current, chargingNext_clock current⟩)
    | .energies => (recoveryEnergyRead (chargingCurrentState current),
        recoveryEnergyRead (chargingCurrentState (chargingNext current)))
    | .energyBalance => ⟨chargingNext_energyBalance current, chargingNext_workBalance current⟩
    | .entropy => (Load.Runtime.loadEntropyRead (chargingCurrentState current),
        Load.Runtime.loadEntropyRead (chargingCurrentState (chargingNext current)))
    | .entropyDisposition => ⟨loadEntropy_disposition (chargingCurrentState (chargingNext current)),
        loadEntropy_nonnegative (chargingCurrentState (chargingNext current))⟩
    | .freeEnergy => (Load.Runtime.loadFreeEnergyRead (chargingCurrentState current),
        Load.Runtime.loadFreeEnergyRead (chargingCurrentState (chargingNext current)))
    | .netAccount => (chargingEventWork current, chargingAccumulatedWork current,
        ⟨chargingNext_netAccount current⟩)
    | .capacities => (recoveryCapacityRead (chargingCurrentState current),
        recoveryCapacityRead (chargingCurrentState (chargingNext current)))
    | .firstCharge => ⟨sourceGeneratedWholePCCharging⟩
    | .wholeLedger => chargingLedgerCompiler.compile occurrence

def chargingAuthoritySource : SourceNativeAuthoritySource RecoveryN ChargingV where
  restructuringSource := chargingRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal chargingRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := chargingProjectionLaw

def chargingAuthoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN ChargingV where
  source := chargingAuthoritySource
  emitted := chargingEmitted
  compiler_commutes := fun _ => rfl

def chargingLivingRoot : SourceNativeLivingRootClosure RecoveryN ChargingV :=
  chargingAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def chargingInitialVisit : SourceNativeTemporalVisitAt chargingLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite chargingLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def chargingInitialGenerated :=
  chargingLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit chargingInitialVisit

def chargingInitialEntry := recoveryEntry (chargingCurrentSupport .ingress)

def chargingInitialEntryRow : chargingInitialGenerated.GeneratedEntryRowAt chargingInitialEntry :=
  (chargingInitialGenerated.canonicalGeneratedEntryRow? chargingInitialEntry).get (by rfl)

def chargingFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    chargingInitialGenerated.occurrence chargingInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? chargingInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end

end LAlanine40K2025.Thermal.Recovery.Charging.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
