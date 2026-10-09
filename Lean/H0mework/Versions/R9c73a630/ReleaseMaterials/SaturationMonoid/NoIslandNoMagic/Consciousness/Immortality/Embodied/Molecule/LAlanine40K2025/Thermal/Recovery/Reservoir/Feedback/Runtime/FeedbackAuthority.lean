import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackReadouts
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedPointerFeedback
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.Holevo
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Cross.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.FullGamma.Information

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Pointer.Runtime
noncomputable section

private def feedbackRestructuringLaw : SourceNativeLedgerRestructuringLaw feedbackSource :=
  identityOnlyWorldLedgerRestructuringLaw feedbackSource LAlanine40K2025.Source.key (by
    intro support responsibility
    refine ⟨fun left right => ?_⟩
    have same : (⟨responsibility, left⟩ : OpenResponsibilityAt RecoveryN support) = ⟨responsibility, right⟩ :=
      (recoveryEntry_unique _ _).trans (recoveryEntry_unique _ _).symm
    exact eq_of_heq (Sigma.mk.inj same).2)

private def feedbackRestructuringCompiler : SourceNativeRestructuringLedgerCompiler feedbackSource where
  ledgerCompiler := feedbackLedgerCompiler
  restructuringLaw := feedbackRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)
    (fun left right _ => (recoveryEntry_unique _ left).trans (recoveryEntry_unique _ right).symm)

def feedbackRestructuringSource : SourceNativeRestructuringLedgerSource RecoveryN FeedbackV where
  source := feedbackSource
  compiler := feedbackRestructuringCompiler

inductive FeedbackProjection
  | current | next | joint | body | pointer | control | energies | thermal
  | entropy | freeEnergy | netAccount | resources | firstResponse | wholeLedger

def feedbackProjectionLaw : SourceNativeProjectionLaw feedbackRestructuringSource.toLedgerSource where
  Projection := FeedbackProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .firstResponse => match current with | .ingress => PUnit | .running _ => PEmpty
    | _ => PUnit
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .firstResponse => match current with | .ingress => PEmpty | .running _ => PUnit
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
    | .joint => PointerJoint × PointerJoint × PLift (type_of% (feedbackNext_joint current))
    | .body => Current.FullJoint × Current.FullJoint
    | .pointer => Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ ×
        PLift (type_of% (pointerMatrix_positive (feedbackCurrentState (feedbackNext current))) ∧
          type_of% (pointerMatrix_trace (feedbackCurrentState (feedbackNext current))))
    | .control => PointerControlRead × PLift (type_of% (feedbackControl_work current) ∧
        type_of% (feedbackControl_exponential current) ∧ type_of% (feedbackControl_positive current) ∧
        type_of% (feedbackNext_clock current))
    | .energies => (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ) × PLift (type_of% (feedbackNext_energyBalance current))
    | .thermal => PLift (type_of% (Live.thermalJoint_generated (feedbackCurrentState (feedbackNext current))) ∧
        type_of% (Live.entropyProduction_disposition (feedbackCurrentState (feedbackNext current))))
    | .entropy => ℝ × ℝ × PLift (0 ≤ Live.entropyProduction (feedbackCurrentState (feedbackNext current)))
    | .freeEnergy => ℝ × ℝ
    | .netAccount => ℝ × ℝ × PLift (type_of% (feedbackNext_netAccount current))
    | .resources => (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) ×
        PLift (type_of% (Resource.current_total (feedbackCurrentState current)) ∧
          type_of% (Resource.current_total (feedbackCurrentState (feedbackNext current))) ∧
          type_of% (Resource.remaining_range (feedbackCurrentState current)) ∧
          type_of% (Resource.remaining_range (feedbackCurrentState (feedbackNext current))) ∧
          type_of% (feedbackNext_resourceBalance current))
    | .firstResponse => PLift (type_of% sourceGeneratedPointerFeedback ∧
        type_of% Resource.sourceGeneratedFeedbackResources ∧
        type_of% SourceGeneratedBodyEnsemble.source_mixture ∧
        (∀ index : Current.FullIndex,
          type_of% (SourceGeneratedBodyEnsemble.source_index_left index) ∧
          type_of% (SourceGeneratedBodyEnsemble.source_index_right index)) ∧
        (∀ value : SourceGeneratedWorkInformation.Value,
          type_of% (SourceGeneratedBodyEnsemble.source_joint_left_value value) ∧
          type_of% (SourceGeneratedBodyEnsemble.source_joint_right_value value)) ∧
        type_of% SourceGeneratedBodyEnsemble.source_defect_conditional ∧
        type_of% SourceGeneratedBodyEnsemble.ValueCoarsening.original_joint_coarsens_index ∧
        type_of% SourceGeneratedBodyEnsemble.ValueCoarsening.value_information_le_index ∧
        type_of% SourceGeneratedBodyEnsemble.ValueCoarsening.value_information_loss_entropy ∧
        type_of% SourceGeneratedBodyEnsemble.original_marginal_as_body_diagonal ∧
        type_of% SourceGeneratedBodyEnsemble.value_information_quantum_gap ∧
        type_of% SourceGeneratedBodyEnsemble.holevoInformationLoss_nonnegative ∧
        type_of% SourceGeneratedBodyEnsemble.original_holevo_residual_account ∧
        type_of% FullGammaCross.received_cross_eq ∧
        type_of% FullGammaCross.received_cross_nonzero ∧
        type_of% FullGammaCross.first_cross_nonzero ∧
        type_of% SourceGeneratedBodyEnsemble.originalBlockQuantumInformation_eq_holevo ∧
        type_of% SourceGeneratedBodyEnsemble.originalFullQuantumInformation_coherence ∧
        type_of% SourceGeneratedBodyEnsemble.originalFullQuantumInformation_account)
    | .wholeLedger => SourceNativeLedgerEvolutionAt feedbackSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => feedbackCurrentState current
    | .next => feedbackCurrentState (feedbackNext current)
    | .joint => ((feedbackCurrentState current).joint, (feedbackCurrentState (feedbackNext current)).joint, ⟨feedbackNext_joint current⟩)
    | .body => (bodyRead (feedbackCurrentState current).joint, bodyRead (feedbackCurrentState (feedbackNext current)).joint)
    | .pointer => (pointerMatrix (feedbackCurrentState current).joint, pointerMatrix (feedbackCurrentState (feedbackNext current)).joint,
        ⟨pointerMatrix_positive _, pointerMatrix_trace _⟩)
    | .control => (feedbackControlRead current, ⟨feedbackControl_work current, feedbackControl_exponential current,
        feedbackControl_positive current, feedbackNext_clock current⟩)
    | .energies => (pointerEnergyRead (feedbackCurrentState current), pointerEnergyRead (feedbackCurrentState (feedbackNext current)),
        ⟨feedbackNext_energyBalance current⟩)
    | .thermal => ⟨Live.thermalJoint_generated _, Live.entropyProduction_disposition _⟩
    | .entropy => (Live.entropyProduction (feedbackCurrentState current), Live.entropyProduction (feedbackCurrentState (feedbackNext current)),
        ⟨Live.entropyProduction_nonnegative _⟩)
    | .freeEnergy => (Live.freeEnergy (feedbackCurrentState current), Live.freeEnergy (feedbackCurrentState (feedbackNext current)))
    | .netAccount => (feedbackEventWork current, feedbackAccumulatedWork current, ⟨feedbackNext_netAccount current⟩)
    | .resources => (Resource.values (feedbackCurrentState current), Resource.values (feedbackCurrentState (feedbackNext current)),
        (Resource.donorRemainingOf (Resource.suppliedBlock (feedbackCurrentState current)),
          Resource.donorRemainingOf (Resource.suppliedBlock (feedbackCurrentState (feedbackNext current)))),
        ⟨Resource.current_total _, Resource.current_total _, Resource.remaining_range _, Resource.remaining_range _,
          feedbackNext_resourceBalance current⟩)
    | .firstResponse => ⟨sourceGeneratedPointerFeedback,
        Resource.sourceGeneratedFeedbackResources,
        SourceGeneratedBodyEnsemble.source_mixture,
        (fun index => ⟨SourceGeneratedBodyEnsemble.source_index_left index,
          SourceGeneratedBodyEnsemble.source_index_right index⟩),
        (fun value => ⟨SourceGeneratedBodyEnsemble.source_joint_left_value value,
          SourceGeneratedBodyEnsemble.source_joint_right_value value⟩),
        SourceGeneratedBodyEnsemble.source_defect_conditional,
        SourceGeneratedBodyEnsemble.ValueCoarsening.original_joint_coarsens_index,
        SourceGeneratedBodyEnsemble.ValueCoarsening.value_information_le_index,
        SourceGeneratedBodyEnsemble.ValueCoarsening.value_information_loss_entropy,
        SourceGeneratedBodyEnsemble.original_marginal_as_body_diagonal,
        SourceGeneratedBodyEnsemble.value_information_quantum_gap,
        SourceGeneratedBodyEnsemble.holevoInformationLoss_nonnegative,
        SourceGeneratedBodyEnsemble.original_holevo_residual_account,
        FullGammaCross.received_cross_eq,
        FullGammaCross.received_cross_nonzero,
        FullGammaCross.first_cross_nonzero,
        SourceGeneratedBodyEnsemble.originalBlockQuantumInformation_eq_holevo,
        SourceGeneratedBodyEnsemble.originalFullQuantumInformation_coherence,
        SourceGeneratedBodyEnsemble.originalFullQuantumInformation_account⟩
    | .wholeLedger => feedbackLedgerCompiler.compile occurrence

def feedbackAuthoritySource : SourceNativeAuthoritySource RecoveryN FeedbackV where
  restructuringSource := feedbackRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal feedbackRestructuringSource (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecoveryN
  projectionLaw := feedbackProjectionLaw

def feedbackAuthoritativeRoot : SourceNativeAuthoritativeRootClosure RecoveryN FeedbackV where
  source := feedbackAuthoritySource
  emitted := feedbackEmitted
  compiler_commutes := fun _ => rfl

def feedbackLivingRoot : SourceNativeLivingRootClosure RecoveryN FeedbackV :=
  feedbackAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def feedbackInitialVisit : SourceNativeTemporalVisitAt feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite feedbackLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def feedbackInitialGenerated := feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit feedbackInitialVisit
def feedbackInitialEntry := recoveryEntry reservoirSupport

def feedbackInitialEntryRow : feedbackInitialGenerated.GeneratedEntryRowAt feedbackInitialEntry :=
  (feedbackInitialGenerated.canonicalGeneratedEntryRow? feedbackInitialEntry).get (by rfl)

def feedbackFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    feedbackInitialGenerated.occurrence feedbackInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? feedbackInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
