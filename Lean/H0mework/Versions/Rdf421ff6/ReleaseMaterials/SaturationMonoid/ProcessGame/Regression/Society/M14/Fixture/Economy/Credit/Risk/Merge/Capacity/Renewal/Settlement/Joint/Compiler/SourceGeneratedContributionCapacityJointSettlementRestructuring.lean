import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Compiler.SourceGeneratedContributionCapacityJointSettlementCompiler

/-!
# Lifecycle certification for the joint settlement compiler

This module keeps the high-arity lifecycle proof separate from the finite
write/terminal compiler.  It reuses the existing contribution-capacity
obligation vocabulary and introduces no second lifecycle or ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementRestructuring

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler

def contributionCapacityJointSettlementRestructuringLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeLedgerRestructuringLaw
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material) where
  vocabulary := contributionCapacityReopeningRestructuringVocabulary oldVisit
  sourceEventAt := fun _ =>
    ((contributionCapacitySettlementSurvivorSupport oldVisit).1,
      exactSourceGeneratedLossAllocationMaterialWitness)
  obligationAt := by
    intro current occurrence support entry
    cases support with
    | inl reopeningSupport =>
        exact contributionCapacityU8ObligationAt oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness
          (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
            (CapacityU8NAt oldVisit) reopeningSupport.1)
    | inr emptyUnit =>
        cases emptyUnit
        exact PEmpty.elim entry.2
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by
    intro current occurrence support entry
    cases support with
    | inl reopeningSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact PEmpty.elim entry.2
  anchor_commutes := by
    intro current occurrence support entry
    cases support with
    | inl reopeningSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact PEmpty.elim entry.2
  incidence_commutes := by
    intro current occurrence support entry
    cases support with
    | inl reopeningSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact PEmpty.elim entry.2
  lineage_commutes := by
    intro current occurrence support entry
    cases support with
    | inl reopeningSupport => rfl
    | inr emptyUnit => cases emptyUnit; exact PEmpty.elim entry.2
  obligationAt_injective := by
    intro current occurrence support left right equality
    cases support with
    | inl reopeningSupport =>
        exact contributionCapacityU8ObligationAt_injective oldVisit
          exactSourceGeneratedLossAllocationMaterialWitness equality
    | inr emptyUnit =>
        cases emptyUnit
        exact PEmpty.elim left.2

def contributionCapacityJointSettlementRestructuringCertification
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionCapacityJointSettlementRestructuringLaw oldVisit
        sourceIndex material)
      ((contributionCapacityJointSettlementLedgerCompiler oldVisit sourceIndex
        material).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  · exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun left right equality =>
        (contributionCapacityJointSettlementWriteEvolution_origin oldVisit
          sourceIndex material
          (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
            material false) left).symm.trans
          (equality.trans
            (contributionCapacityJointSettlementWriteEvolution_origin oldVisit
              sourceIndex material
              (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
                material false) right)))
      (fun left right equality =>
        (contributionCapacityJointSettlementWriteEvolution_destination oldVisit
          sourceIndex material
          (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
            material false) left).symm.trans
          (equality.trans
            (contributionCapacityJointSettlementWriteEvolution_destination
              oldVisit sourceIndex material
              (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
                material false) right)))
  · exact PUnit.unit

def contributionCapacityJointSettlementRestructuringCompiler
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeRestructuringLedgerCompiler
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material) where
  ledgerCompiler := contributionCapacityJointSettlementLedgerCompiler oldVisit
    sourceIndex material
  restructuringLaw := contributionCapacityJointSettlementRestructuringLaw
    oldVisit sourceIndex material
  certifyRestructuring :=
    contributionCapacityJointSettlementRestructuringCertification oldVisit
      sourceIndex material

def contributionCapacityJointSettlementRestructuringSource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeRestructuringLedgerSource (JointSettlementNAt oldVisit)
      (ContributionCapacityJointSettlementVAt oldVisit) where
  source := contributionCapacityJointSettlementSource oldVisit sourceIndex
    material
  compiler := contributionCapacityJointSettlementRestructuringCompiler oldVisit
    sourceIndex material

end
end M14SourceGeneratedContributionCapacityJointSettlementRestructuring
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementRestructuring.contributionCapacityJointSettlementRestructuringSource
