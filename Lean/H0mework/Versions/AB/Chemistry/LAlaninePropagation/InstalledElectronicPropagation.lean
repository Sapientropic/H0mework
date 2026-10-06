import H0mework.Versions.AB.Chemistry.LAlanineForce.InstalledForceUpdate

/-!
# The original L-alanine root consumes its native electronic next

The force target becomes this occurrence's source. Its source matrices,
Hamiltonian, density law, initial density and fixed-duration target are installed
before the emitter. The literal next retains the matrices and native operator;
independent numerical exponentials are not written into this standing.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Installation

noncomputable section

open _root_.SaturationMonoid.ProcessGame
open _root_.SaturationMonoid.ProcessGame.Society.Renewal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root LAlanine40K2025.Installation
open LAlanine40K2025.Energy.Installation LAlanine40K2025.Force.Installation
open LAlanine40K2025.Propagation.Root LAlanine40K2025.Propagation.Producer

def visit4 : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot :=
  visit3.next rfl

def electronicRenewalInstallation : SourceNativeProjectionLaw.InstallationAt
    electronicRenewalLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw :=
  (((renewalComponent baseAuthoritySource electronicRenewalLaw).trans
    (inheritedByRenewal electronicAuthoritySource Force.Root.forceRenewalLaw)).trans
      (inheritedByRenewal forceAuthoritySource renewalLaw)).trans
        (inheritedByRenewal incidenceAuthoritySource Energy.Root.energyRenewalLaw)

def electronicRecognition : SourceNativeRenewalRecognitionAt root game
    ElectronicRenewalSeed electronicSeedAt ElectronicRenewalConsumerAt
      ElectronicRenewalDispositionAt where
  law := electronicRenewalLaw
  installation := electronicRenewalInstallation

def installedElectronic : SourceInstalledRenewalAt electronicRecognition visit3 :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

theorem generatedElectronicNext_eq :
    root.generatedNextCurrentAt visit3 =
      ⟨V, root.toAuthoritativeRoot, visit4⟩ := by
  rfl

theorem forceTarget_is_electronicSource :
    installedForce.operationalAuthority.operationalStanding =
      installedElectronic.payload.sourceEntry := by
  rfl

theorem electronicDisposition_is_literalNext :
    installedElectronic.payload.disposition.target = visit4.current := by
  rfl

theorem electronicSourceProjection_is_sourceMaterial :
    baseProjectionLaw.outcomeAt .electronicPropagationSource
        (root.emitted visit3.current) =
      (.inl ⟨PUnit.unit, Source.electronicSource⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .electronicPropagationSource
          (root.emitted visit3.current)) := by
  rfl

theorem electronicHamiltonianProjection_is_generated :
    baseProjectionLaw.outcomeAt .electronicHamiltonian
        (root.emitted visit3.current) =
      (.inl ⟨PUnit.unit, Dynamics.hamiltonian Source.electronicSource⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .electronicHamiltonian
          (root.emitted visit3.current)) := by
  rfl

theorem electronicDensityLawProjection_is_generated :
    baseProjectionLaw.outcomeAt .electronicDensityLaw
        (root.emitted visit3.current) =
      (.inl ⟨PUnit.unit, Dynamics.densityEvolution Source.electronicSource⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .electronicDensityLaw
          (root.emitted visit3.current)) := by
  rfl

theorem electronicCurrentDensityProjection_is_sourceMaterial :
    baseProjectionLaw.outcomeAt .electronicCurrentDensity
        (root.emitted visit3.current) =
      (.inl ⟨PUnit.unit, Dynamics.initialDensity Source.electronicSource⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .electronicCurrentDensity
          (root.emitted visit3.current)) := by
  rfl

theorem electronicTargetProjection_is_nativeNext :
    baseProjectionLaw.outcomeAt .electronicNativeTarget
        (root.emitted visit3.current) =
      (.inl ⟨PUnit.unit, nativeElectronicNext⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .electronicNativeTarget
          (root.emitted visit3.current)) := by
  rfl

theorem electronicSourceHamiltonianJointFactorization :
    type_of% ((root.canonicalCausalAnswerAndNext (ULift.up visit3))
      |>.installedJointSubsystemAuthority_factorizes
        siblingInstallation siblingInstallation
        LAlanineSiblingProjection.electronicPropagationSource
        LAlanineSiblingProjection.electronicHamiltonian) :=
  (root.canonicalCausalAnswerAndNext (ULift.up visit3))
    |>.installedJointSubsystemAuthority_factorizes
      siblingInstallation siblingInstallation
      LAlanineSiblingProjection.electronicPropagationSource
      LAlanineSiblingProjection.electronicHamiltonian

theorem electronicHamiltonianLawJointFactorization :
    type_of% ((root.canonicalCausalAnswerAndNext (ULift.up visit3))
      |>.installedJointSubsystemAuthority_factorizes
        siblingInstallation siblingInstallation
        LAlanineSiblingProjection.electronicHamiltonian
        LAlanineSiblingProjection.electronicDensityLaw) :=
  (root.canonicalCausalAnswerAndNext (ULift.up visit3))
    |>.installedJointSubsystemAuthority_factorizes
      siblingInstallation siblingInstallation
      LAlanineSiblingProjection.electronicHamiltonian
      LAlanineSiblingProjection.electronicDensityLaw

theorem electronicLawCurrentJointFactorization :
    type_of% ((root.canonicalCausalAnswerAndNext (ULift.up visit3))
      |>.installedJointSubsystemAuthority_factorizes
        siblingInstallation siblingInstallation
        LAlanineSiblingProjection.electronicDensityLaw
        LAlanineSiblingProjection.electronicCurrentDensity) :=
  (root.canonicalCausalAnswerAndNext (ULift.up visit3))
    |>.installedJointSubsystemAuthority_factorizes
      siblingInstallation siblingInstallation
      LAlanineSiblingProjection.electronicDensityLaw
      LAlanineSiblingProjection.electronicCurrentDensity

theorem electronicLawTargetJointFactorization :
    type_of% ((root.canonicalCausalAnswerAndNext (ULift.up visit3))
      |>.installedJointSubsystemAuthority_factorizes
        siblingInstallation siblingInstallation
        LAlanineSiblingProjection.electronicDensityLaw
        LAlanineSiblingProjection.electronicNativeTarget) :=
  (root.canonicalCausalAnswerAndNext (ULift.up visit3))
    |>.installedJointSubsystemAuthority_factorizes
      siblingInstallation siblingInstallation
      LAlanineSiblingProjection.electronicDensityLaw
      LAlanineSiblingProjection.electronicNativeTarget

theorem electronicSource_keeps_materialPayload :
    installedElectronic.payload.consumer.sourceMatrices = Source.electronicSource ∧
      installedElectronic.payload.consumer.materialSource = Force.Source.updateReadout :=
  ⟨installedElectronic.payload.consumer.sourceMatricesExact,
    installedElectronic.payload.consumer.materialSourceExact⟩

theorem electronicSourceGeometry_is_forceTarget :
    installedElectronic.payload.consumer.materialSource.recordedTargetPositions =
      installedForce.operationalAuthority.operationalStanding.2.update.recordedTargetPositions := by
  rfl

theorem electronicCurrent_is_lawZero :
    Dynamics.densityEvolution installedElectronic.payload.consumer.sourceMatrices 0 =
      Dynamics.initialDensity installedElectronic.payload.consumer.sourceMatrices :=
  Dynamics.densityEvolution_zero _

theorem electronicTarget_is_sourceGenerated :
    installedElectronic.payload.disposition.nativeTarget =
      Dynamics.densityEvolution installedElectronic.payload.consumer.sourceMatrices 1 := by
  exact installedElectronic.payload.disposition.nativeTargetExact

theorem generatedTargetRow_keeps_sourceMatrices :
    installedElectronic.operationalAuthority.operationalStanding.2.sourceMatrices =
      installedElectronic.payload.consumer.sourceMatrices := by
  rfl

theorem generatedTargetRow_keeps_nativeTarget :
    installedElectronic.operationalAuthority.operationalStanding.2.nativeTarget =
      installedElectronic.payload.disposition.nativeTarget := by
  rfl

theorem generatedTargetRow_keeps_nativeNext :
    installedElectronic.operationalAuthority.operationalStanding.2.nativeTarget =
      nativeElectronicNext := by
  rfl

/-- Actual next consumes only its recorded source and the fixed duration. -/
theorem generatedTargetRow_density_commutes :
    let standing := installedElectronic.operationalAuthority.operationalStanding.2
    standing.nativeTarget = Dynamics.densityEvolution standing.sourceMatrices 1 :=
  installedElectronic.operationalAuthority.operationalStanding.2.nativeTargetExact

theorem electronicClaim_preserved :
    installedElectronic.payload.sourceEntry.claim =
      installedElectronic.operationalAuthority.operationalStanding.claim :=
  installedElectronic.operationalAuthority.debtLineage.claim_eq

theorem electronicLineage_preserved :
    type_of% installedElectronic.operationalAuthority.debtLineage.lineage_eq :=
  installedElectronic.operationalAuthority.debtLineage.lineage_eq

theorem electronicBudgets_eq_zero :
    installedElectronic.payload.sourceEntry.progressBudget = 0 ∧
      installedElectronic.operationalAuthority.operationalStanding.progressBudget = 0 := by
  exact ⟨rfl, rfl⟩

theorem electronicBudget_not_refilled :
    installedElectronic.operationalAuthority.operationalStanding.progressBudget ≤
      installedElectronic.payload.sourceEntry.progressBudget :=
  installedElectronic.operationalAuthority.progressBudget_not_refilled

theorem noInitialElectronicActivation :
    IsEmpty (SourceInstalledRenewalAt electronicRecognition visit0) :=
  ⟨fun premature => nomatch premature.active⟩

theorem noIncidenceElectronicActivation :
    IsEmpty (SourceInstalledRenewalAt electronicRecognition visit1) :=
  ⟨fun premature => nomatch premature.active⟩

theorem noEnergyElectronicActivation :
    IsEmpty (SourceInstalledRenewalAt electronicRecognition visit2) :=
  ⟨fun premature => nomatch premature.active⟩

theorem noRepeatedElectronicActivation :
    IsEmpty (SourceInstalledRenewalAt electronicRecognition visit4) :=
  ⟨fun repeated => nomatch repeated.active⟩

structure SourceInstalledLAlanine40KElectronicPropagationRootCrown : Prop where
  forceCheckpoint : SourceInstalledLAlanine40KForceUpdateRootCrown
  sourceCurrent : visit3.current = .forceDrivenMaterialNextCertified
  targetCurrent : visit4.current = .electronicPropagationCertified
  electronicProducer : SourceGeneratedLAlanineElectronicPropagationCrown
  forceTargetBecomesSource : type_of% forceTarget_is_electronicSource
  sourceProjection : type_of% electronicSourceProjection_is_sourceMaterial
  hamiltonianProjection : type_of% electronicHamiltonianProjection_is_generated
  lawProjection : type_of% electronicDensityLawProjection_is_generated
  currentProjection : type_of% electronicCurrentDensityProjection_is_sourceMaterial
  targetProjection : type_of% electronicTargetProjection_is_nativeNext
  sourceHamiltonianSameOccurrenceAndNext : type_of% electronicSourceHamiltonianJointFactorization
  hamiltonianLawSameOccurrenceAndNext : type_of% electronicHamiltonianLawJointFactorization
  lawCurrentSameOccurrenceAndNext : type_of% electronicLawCurrentJointFactorization
  lawTargetSameOccurrenceAndNext : type_of% electronicLawTargetJointFactorization
  rootFactorization : installedElectronic.RootAnswerAndNextFactorizes
  rootConsumer : Nonempty (RenewalResponsibilityConsumerAt installedElectronic.operationalAuthority)
  literalNext : type_of% generatedElectronicNext_eq
  dispositionTarget : type_of% electronicDisposition_is_literalNext
  materialConsumer : type_of% electronicSource_keeps_materialPayload
  materialGeometry : type_of% electronicSourceGeometry_is_forceTarget
  currentCommuting : type_of% electronicCurrent_is_lawZero
  nativeTarget : type_of% electronicTarget_is_sourceGenerated
  targetRowSource : type_of% generatedTargetRow_keeps_sourceMatrices
  targetRowNativeTarget : type_of% generatedTargetRow_keeps_nativeTarget
  targetRowNativeNext : type_of% generatedTargetRow_keeps_nativeNext
  targetRowCommuting : type_of% generatedTargetRow_density_commutes
  claimPreserved : type_of% electronicClaim_preserved
  lineagePreserved : type_of% electronicLineage_preserved
  zeroBudgets : type_of% electronicBudgets_eq_zero
  budgetNotRefilled : type_of% electronicBudget_not_refilled
  notInitiallyActive : IsEmpty (SourceInstalledRenewalAt electronicRecognition visit0)
  notAtIncidence : IsEmpty (SourceInstalledRenewalAt electronicRecognition visit1)
  notAtEnergy : IsEmpty (SourceInstalledRenewalAt electronicRecognition visit2)
  notRepeated : IsEmpty (SourceInstalledRenewalAt electronicRecognition visit4)

theorem sourceInstalledLAlanine40KElectronicPropagation_rootCrown :
    SourceInstalledLAlanine40KElectronicPropagationRootCrown where
  forceCheckpoint := sourceInstalledLAlanine40KForceUpdate_rootCrown
  sourceCurrent := rfl
  targetCurrent := rfl
  electronicProducer := sourceGeneratedLAlanineElectronicPropagation_crown
  forceTargetBecomesSource := forceTarget_is_electronicSource
  sourceProjection := electronicSourceProjection_is_sourceMaterial
  hamiltonianProjection := electronicHamiltonianProjection_is_generated
  lawProjection := electronicDensityLawProjection_is_generated
  currentProjection := electronicCurrentDensityProjection_is_sourceMaterial
  targetProjection := electronicTargetProjection_is_nativeNext
  sourceHamiltonianSameOccurrenceAndNext := electronicSourceHamiltonianJointFactorization
  hamiltonianLawSameOccurrenceAndNext := electronicHamiltonianLawJointFactorization
  lawCurrentSameOccurrenceAndNext := electronicLawCurrentJointFactorization
  lawTargetSameOccurrenceAndNext := electronicLawTargetJointFactorization
  rootFactorization := installedElectronic.rootAnswerAndNext_factorizes
  rootConsumer := ⟨installedElectronic.rootResponsibilityConsumer⟩
  literalNext := generatedElectronicNext_eq
  dispositionTarget := electronicDisposition_is_literalNext
  materialConsumer := electronicSource_keeps_materialPayload
  materialGeometry := electronicSourceGeometry_is_forceTarget
  currentCommuting := electronicCurrent_is_lawZero
  nativeTarget := electronicTarget_is_sourceGenerated
  targetRowSource := generatedTargetRow_keeps_sourceMatrices
  targetRowNativeTarget := generatedTargetRow_keeps_nativeTarget
  targetRowNativeNext := generatedTargetRow_keeps_nativeNext
  targetRowCommuting := generatedTargetRow_density_commutes
  claimPreserved := electronicClaim_preserved
  lineagePreserved := electronicLineage_preserved
  zeroBudgets := electronicBudgets_eq_zero
  budgetNotRefilled := electronicBudget_not_refilled
  notInitiallyActive := noInitialElectronicActivation
  notAtIncidence := noIncidenceElectronicActivation
  notAtEnergy := noEnergyElectronicActivation
  notRepeated := noRepeatedElectronicActivation

end

end LAlanine40K2025.Propagation.Installation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
