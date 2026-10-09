import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerReadouts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime
noncomputable section

private def pointerRestructuringLaw : SourceNativeLedgerRestructuringLaw pointerSource :=
  identityOnlyWorldLedgerRestructuringLaw pointerSource LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility, left⟩ : OpenResponsibilityAt RecoveryN support) = ⟨responsibility, right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def pointerRestructuringCompiler : SourceNativeRestructuringLedgerCompiler pointerSource where
  ledgerCompiler := pointerLedgerCompiler
  restructuringLaw := pointerRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def pointerRestructuringSource : SourceNativeRestructuringLedgerSource RecoveryN PointerV where
  source := pointerSource
  compiler := pointerRestructuringCompiler

inductive PointerProjection
  | current | next | joint | body | pointer | control | energies | thermal
  | entropy | freeEnergy | netAccount | firstMeasurement | wholeLedger

def pointerProjectionLaw : SourceNativeProjectionLaw pointerRestructuringSource.toLedgerSource where
  Projection := PointerProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstMeasurement => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstMeasurement => match current with | .ingress => PEmpty | .running _ => PUnit
    | _ => PEmpty
  classify := by
    intro projection current occurrence
    cases projection <;> try exact .inl PUnit.unit
    cases current with
    | ingress => exact .inl PUnit.unit
    | running _ => exact .inr PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .current | .next => Live.State
    | .joint => PointerJoint × PointerJoint × PLift (type_of% (pointerNext_joint current))
    | .body => Current.FullJoint × Current.FullJoint
    | .pointer => Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ ×
        PLift (type_of% (pointerMatrix_positive (pointerCurrentState (pointerNext current))) ∧
          type_of% (pointerMatrix_trace (pointerCurrentState (pointerNext current))))
    | .control => PointerControlRead × PLift (type_of% (pointerControl_work current) ∧
        type_of% (pointerControl_exponential current) ∧ type_of% (pointerControl_positive current) ∧
        type_of% (pointerNext_clock current))
    | .energies => (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ) × PLift (type_of% (pointerNext_energyBalance current))
    | .thermal => PLift (type_of% (Live.thermalJoint_generated (pointerCurrentState (pointerNext current))) ∧
        type_of% (Live.entropyProduction_disposition (pointerCurrentState (pointerNext current))))
    | .entropy => ℝ × ℝ × PLift (0 ≤ Live.entropyProduction (pointerCurrentState (pointerNext current)))
    | .freeEnergy => ℝ × ℝ
    | .netAccount => ℝ × ℝ × PLift (type_of% (pointerNext_netAccount current))
    | .firstMeasurement => PLift (type_of% sourceGeneratedPointerInstrument)
    | .wholeLedger => SourceNativeLedgerEvolutionAt pointerSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => pointerCurrentState current
    | .next => pointerCurrentState (pointerNext current)
    | .joint => ((pointerCurrentState current).joint, (pointerCurrentState (pointerNext current)).joint, ⟨pointerNext_joint current⟩)
    | .body => (bodyRead (pointerCurrentState current).joint, bodyRead (pointerCurrentState (pointerNext current)).joint)
    | .pointer => (pointerMatrix (pointerCurrentState current).joint, pointerMatrix (pointerCurrentState (pointerNext current)).joint,
        ⟨pointerMatrix_positive _, pointerMatrix_trace _⟩)
    | .control => (pointerControlRead current, ⟨pointerControl_work current, pointerControl_exponential current,
        pointerControl_positive current, pointerNext_clock current⟩)
    | .energies => (pointerEnergyRead (pointerCurrentState current), pointerEnergyRead (pointerCurrentState (pointerNext current)),
        ⟨pointerNext_energyBalance current⟩)
    | .thermal => ⟨Live.thermalJoint_generated _, Live.entropyProduction_disposition _⟩
    | .entropy => (Live.entropyProduction (pointerCurrentState current), Live.entropyProduction (pointerCurrentState (pointerNext current)),
        ⟨Live.entropyProduction_nonnegative _⟩)
    | .freeEnergy => (Live.freeEnergy (pointerCurrentState current), Live.freeEnergy (pointerCurrentState (pointerNext current)))
    | .netAccount => (pointerEventWork current, pointerAccumulatedWork current, ⟨pointerNext_netAccount current⟩)
    | .firstMeasurement => ⟨sourceGeneratedPointerInstrument⟩
    | .wholeLedger => pointerLedgerCompiler.compile occurrence

def pointerAuthoritySource : SourceNativeAuthoritySource RecoveryN PointerV where
  restructuringSource := pointerRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal pointerRestructuringSource (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := pointerProjectionLaw

def pointerAuthoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN PointerV where
  source := pointerAuthoritySource
  emitted := pointerEmitted
  compiler_commutes := fun _ => rfl

def pointerLivingRoot : SourceNativeLivingRootClosure RecoveryN PointerV :=
  pointerAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def pointerInitialVisit : SourceNativeTemporalVisitAt pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite pointerLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def pointerInitialGenerated := pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit pointerInitialVisit
def pointerInitialEntry := recoveryEntry reservoirSupport

def pointerInitialEntryRow : pointerInitialGenerated.GeneratedEntryRowAt pointerInitialEntry :=
  (pointerInitialGenerated.canonicalGeneratedEntryRow? pointerInitialEntry).get (by rfl)

def pointerFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    pointerInitialGenerated.occurrence pointerInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? pointerInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
