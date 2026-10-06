import H0mework.Versions.AB.Chemistry.LAlaninePropagation.NativeElectronicRenewal

/-! # Source-installed L-alanine physical/chemical bond-density update -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Installation

noncomputable section

open _root_.SaturationMonoid.ProcessGame
open _root_.SaturationMonoid.ProcessGame.Society.Renewal
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Interface Source Calculation Producer Root

def renewalLaw : SourceNativeRenewalProjectionLaw
    baseAuthoritySource.restructuringSource.toLedgerSource game
    LAlanineRenewalSeed seedAt LAlanineRenewalConsumerAt
    LAlanineRenewalDispositionAt :=
  SourceNativeRenewalProjectionLaw.ofRootShell renewalRootShell sourceSeed
    renewalConsumer renewalDisposition

/-- Activation order is source-defined; projection installation precedes every visit. -/
def electronicAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection baseAuthoritySource Propagation.Root.electronicRenewalLaw

def forceAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection electronicAuthoritySource Force.Root.forceRenewalLaw

def incidenceAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection forceAuthoritySource renewalLaw

def authoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection incidenceAuthoritySource Energy.Root.energyRenewalLaw

def root : SourceNativeLivingRootClosure N V where
  source :=
    { base := authoritySource
      terminalHandoff := authoritySource.emptyFaithfulTerminalHandoff
        (fun _current => ⟨fun terminal => nomatch terminal⟩) }
  emitted := Root.emitted
  compiler_commutes := fun _current => rfl

def visit0 : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot :=
  .finite root.toAuthoritativeRoot.toRoot.initialVisit

def visit1 : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot :=
  visit0.next rfl

def renewalInstallation : SourceNativeProjectionLaw.InstallationAt
    renewalLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw :=
  (renewalComponent forceAuthoritySource renewalLaw).trans
    (inheritedByRenewal incidenceAuthoritySource Energy.Root.energyRenewalLaw)

def siblingInstallation : SourceNativeProjectionLaw.InstallationAt
    baseProjectionLaw root.toAuthoritativeRoot.source.projectionLaw :=
  (((inheritedByRenewal baseAuthoritySource Propagation.Root.electronicRenewalLaw).trans
    (inheritedByRenewal electronicAuthoritySource Force.Root.forceRenewalLaw)).trans
      (inheritedByRenewal forceAuthoritySource renewalLaw)).trans
        (inheritedByRenewal incidenceAuthoritySource Energy.Root.energyRenewalLaw)

def recognition : SourceNativeRenewalRecognitionAt root game
    LAlanineRenewalSeed seedAt LAlanineRenewalConsumerAt
      LAlanineRenewalDispositionAt where
  law := renewalLaw
  installation := renewalInstallation

def installed : SourceInstalledRenewalAt recognition visit0 :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

theorem generatedNext_eq :
    root.generatedNextCurrentAt visit0 =
      ⟨V, root.toAuthoritativeRoot, visit1⟩ := by
  rfl

theorem targetStage_inactive :
    IsEmpty (renewalLaw.ActiveAt (root.emitted visit1.current)) :=
  ⟨fun active => nomatch active⟩

theorem noRepeatedActivation :
    IsEmpty (SourceInstalledRenewalAt recognition visit1) :=
  ⟨fun later => targetStage_inactive.false later.active⟩

set_option linter.defProp false in
def physicalChemicalJointFactorization :=
  (root.canonicalCausalAnswerAndNext (ULift.up visit0))
    |>.installedJointSubsystemAuthority_factorizes
      siblingInstallation siblingInstallation
      LAlanineSiblingProjection.physicalDensity
      LAlanineSiblingProjection.chemicalIncidence

theorem physicalProjection_is_sourceProducer :
    baseProjectionLaw.outcomeAt .physicalDensity
        (root.emitted visit0.current) =
      (.inl ⟨PUnit.unit,
        ⟨sourceGeneratedTargetErasedLAlanine40KBondDensity_crown⟩⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .physicalDensity
          (root.emitted visit0.current)) := by
  rfl

theorem chemicalProjection_is_postFreezeConsumer :
    baseProjectionLaw.outcomeAt .chemicalIncidence
        (root.emitted visit0.current) =
      (.inl ⟨PUnit.unit,
        ⟨sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown⟩⟩ :
        SourceNativeProjectionFiberAt baseProjectionLaw .chemicalIncidence
          (root.emitted visit0.current)) := by
  rfl

theorem rootClaim_preserved :
    installed.payload.sourceEntry.claim =
      installed.operationalAuthority.operationalStanding.claim := by
  exact installed.operationalAuthority.debtLineage.claim_eq

theorem rootBudget_not_refilled :
    installed.operationalAuthority.operationalStanding.progressBudget ≤
      installed.payload.sourceEntry.progressBudget :=
  installed.operationalAuthority.progressBudget_not_refilled

structure SourceInstalledLAlanine40KBondDensityRootCrown : Prop where
  sourceCurrent : visit0.current = .targetErasedDensityBCPCensusFrozen
  targetCurrent : visit1.current = .physicalChemicalBondIncidenceCertified
  localProducer : SourceGeneratedLAlanine40KPhysicalChemicalBondIncidenceCrown
  physicalProjection : type_of% physicalProjection_is_sourceProducer
  chemicalProjection : type_of% chemicalProjection_is_postFreezeConsumer
  jointSameOccurrenceAndNext : type_of% physicalChemicalJointFactorization
  rootFactorization : installed.RootAnswerAndNextFactorizes
  rootConsumer : Nonempty (RenewalResponsibilityConsumerAt
    installed.operationalAuthority)
  literalNext : root.generatedNextCurrentAt visit0 =
    ⟨V, root.toAuthoritativeRoot, visit1⟩
  dispositionTarget : installed.payload.disposition.target = visit1.current
  claimPreserved : installed.payload.sourceEntry.claim =
    installed.operationalAuthority.operationalStanding.claim
  budgetNotRefilled :
    installed.operationalAuthority.operationalStanding.progressBudget ≤
      installed.payload.sourceEntry.progressBudget
  noSecondActivation : IsEmpty (SourceInstalledRenewalAt recognition visit1)

theorem sourceInstalledLAlanine40KBondDensity_rootCrown :
    SourceInstalledLAlanine40KBondDensityRootCrown where
  sourceCurrent := rfl
  targetCurrent := rfl
  localProducer := sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown
  physicalProjection := physicalProjection_is_sourceProducer
  chemicalProjection := chemicalProjection_is_postFreezeConsumer
  jointSameOccurrenceAndNext := physicalChemicalJointFactorization
  rootFactorization := installed.rootAnswerAndNext_factorizes
  rootConsumer := ⟨installed.rootResponsibilityConsumer⟩
  literalNext := generatedNext_eq
  dispositionTarget := rfl
  claimPreserved := rootClaim_preserved
  budgetNotRefilled := rootBudget_not_refilled
  noSecondActivation := noRepeatedActivation

end

end LAlanine40K2025.Installation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
