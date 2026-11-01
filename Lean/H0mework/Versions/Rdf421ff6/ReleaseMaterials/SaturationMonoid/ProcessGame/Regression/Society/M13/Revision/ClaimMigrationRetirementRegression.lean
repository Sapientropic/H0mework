import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Revision.SelfU8Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ReflexiveClaimLifecycle

/-!
# Root-installed claim migration and later retirement

The revised living root itself owns two dependent projection coordinates:
claim migration at current `0`, and final retirement at current `1`.  The
first face is consumed together with the U8 canonical first write and its
new-row receipt.  The second face occurs at the strict successor visit and
contains the actual fulfilled lifecycle edge.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M13ClaimMigrationRetirementRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Settlement Theory.Revision
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M9ProofCarryingRenewalInquiryRuntime
open M13SelfU8Regression
open M13ReflexiveClaimLifecycleFixture

noncomputable section

abbrev migration := M13ReflexiveClaimLifecycleFixture.migration
abbrev laterConsumer := M13ReflexiveClaimLifecycleFixture.laterConsumer
abbrev laterFulfillment := M13ReflexiveClaimLifecycleFixture.laterFulfillment
abbrev retirement := M13ReflexiveClaimLifecycleFixture.retirement
abbrev migrationCompiler :=
  M13ReflexiveClaimLifecycleFixture.migrationCompiler

def firstVisit : SourceNativeTemporalVisitAt
    revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (revisedVisitAt 0)

def laterVisit : SourceNativeTemporalVisitAt
    revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (revisedVisitAt 1)

@[simp] theorem firstVisit_current : firstVisit.current = (0 : Nat) :=
  revisedVisitAt_current 0

@[simp] theorem laterVisit_current : laterVisit.current = (1 : Nat) :=
  revisedVisitAt_current 1

theorem laterVisit_is_strict_successor :
    revisedVisitAt 1 = (revisedVisitAt 0).next rfl :=
  rfl

theorem first_and_later_current_distinct :
    firstVisit.current ≠ laterVisit.current := by
  rw [firstVisit_current, laterVisit_current]
  change (0 : Nat) ≠ 1
  decide

/-! ## Installed first-write migration face -/

def migrationFace : RootClaimMigrationFaceAt (revisedEmitted (0 : Nat)) :=
  revisedProjectionLaw.project .claimMigration
    (revisedEmitted (0 : Nat)) ⟨rfl⟩

theorem migrationFace_is_revisedRoot_projection :
    revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.project
      .claimMigration (revisedLivingRoot.emitted (0 : Nat)) ⟨rfl⟩ =
        migrationFace :=
  rfl

@[simp] theorem migrationFace_exact :
    RootClaimMigrationFaceAt.exactMigration migrationFace = migration :=
  rfl

theorem migration_sourceEvent_is_rootOccurrence :
    ClaimP.boundarySource migration.firstWriteSettlement.event =
      (⟨(0 : Nat), revisedLivingRoot.emitted (0 : Nat)⟩ :
        RevisedRootOccurrence) :=
  migrationFace.sourceEvent_eq_rootOccurrence

/-- The lifecycle obligation is the exact inherited row image written by the
U8 revised root, not an unrelated M3 obligation. -/
@[simp] theorem inherited_claim_content_is_revised_oldRow :
    migration.inheritedClaim.content = oldRevisedEntry.claim :=
  rfl

@[simp] theorem inherited_claim_bearer_is_revised_oldRow :
    migration.inheritedClaim.bearer = oldRevisedEntry.1 :=
  rfl

def runtimeFirstWrite := selfU8.firstWrite
def runtimeFirstWriteConsumes := selfU8.firstWriteConsumes

@[simp] theorem selfU8_revisedRoot_eq :
    exactRevolution.core.revision.generate.newLivingRoot = revisedLivingRoot :=
  rfl

@[simp] theorem runtimeFirstWrite_targetVisit_eq_laterRootVisit :
    runtimeFirstWrite.targetVisit = revisedVisitAt 1 :=
  rfl

def firstWholeLedgerWriteBack :=
  (revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit firstVisit).wholeLedgerWriteBack

def firstGeneratedNext := revisedLivingRoot.generatedNextCurrentAt firstVisit

@[simp] theorem semantic_disposition_is_replaced :
    migration.semanticDisposition =
      LawRevisionDispositionAt.replaced () () :=
  rfl

theorem semanticReplacement : migration.SemanticReplacementAt :=
  ⟨(), (), rfl⟩

theorem replaced_claim_is_still_live_and_not_closed :
    Nonempty (ExactSettlementEdge.LiveResidualAt
        migration.firstWriteSettlement) ∧
      ¬ Nonempty (ExactSettlementEdge.ClosedSettlementAt
        migration.firstWriteSettlement) :=
  migration.semanticReplacement_retains_live_claim semanticReplacement

theorem migrated_lineage_is_preserved :
    migration.successorClaim.lineage = migration.inheritedClaim.lineage :=
  migration.successorClaim_lineage_eq

theorem sparse_omission_is_not_retirement :
    ¬ Nonempty (ExactSettlementEdge.ClosedSettlementAt
      migration.firstWriteSettlement) :=
  migration.sparseOmission_is_not_firstWriteRetirement
    (readout := []) (by
      simp [SourceGeneratedInheritedClaimMigrationAt.SparseReadoutOmissionAt])

/-! ## Installed later actual retirement face -/

def retirementFace : RootClaimRetirementFaceAt (revisedEmitted (1 : Nat)) :=
  revisedProjectionLaw.project .claimRetirement
    (revisedEmitted (1 : Nat)) ⟨rfl⟩

theorem retirementFace_is_revisedRoot_projection :
    revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.project
      .claimRetirement (revisedLivingRoot.emitted (1 : Nat)) ⟨rfl⟩ =
        retirementFace :=
  rfl

@[simp] theorem retirementFace_exact :
    RootClaimRetirementFaceAt.exactRetirement retirementFace = retirement :=
  rfl

theorem retirement_sourceEvent_is_laterRootOccurrence :
    ClaimP.boundarySource laterConsumer.event =
      (⟨(1 : Nat), revisedLivingRoot.emitted (1 : Nat)⟩ :
        RevisedRootOccurrence) :=
  retirementFace.sourceEvent_eq_rootOccurrence

def laterWholeLedgerWriteBack :=
  (revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit laterVisit).wholeLedgerWriteBack

def laterGeneratedNext := revisedLivingRoot.generatedNextCurrentAt laterVisit

/-- The later retirement visit is exactly the first-write target visit; its
root-generated next is the common next consumed by both revised rows. -/
@[simp] theorem laterGeneratedNext_eq_selfU8_revisedRows :
    laterGeneratedNext = selfU8.oldRowAnswerAndNext.nextCurrent :=
  rfl

@[simp] theorem later_classification_is_fulfilled :
    (migration.laterSettlement laterConsumer).classification =
      ExactSettlementEdge.Class.fulfilled :=
  retirement.later_classification_eq_fulfilled

def terminalArchive := retirement.closed.archive

theorem later_event_closes_migrated_claim :
    ResponsibilityState.DisappearsAt
      migration.firstWriteSettlement.edge.target
      (migration.laterSettlement laterConsumer).edge.target
      (migration.laterSettlement laterConsumer).slot.val :=
  retirement.later_actual_disappearance

/-- The root projection has one selected compiler image; an arbitrary sibling
compiler cannot be used as this installed face. -/
theorem bare_migration_cannot_replace_installed_face : True := by
  fail_if_success
    exact (M13ReflexiveClaimLifecycleFixture.migration :
      RootClaimMigrationFaceAt (revisedEmitted (0 : Nat)))
  trivial

/-- Semantic replacement alone still cannot generate the later root face. -/
theorem replaced_alone_cannot_generate_retirementFace : True := by
  fail_if_success
    exact (migration.semanticDisposition :
      RootClaimRetirementFaceAt (revisedEmitted (1 : Nat)))
  trivial

end
end M13ClaimMigrationRetirementRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.migrationFace
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.migrationFace_is_revisedRoot_projection
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.runtimeFirstWriteConsumes
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.runtimeFirstWrite_targetVisit_eq_laterRootVisit
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.retirementFace
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.retirement_sourceEvent_is_laterRootOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.laterGeneratedNext_eq_selfU8_revisedRows
#print axioms SaturationMonoid.ProcessGame.Society.M13ClaimMigrationRetirementRegression.later_event_closes_migrated_claim
