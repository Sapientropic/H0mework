import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Revision
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Credit.PeriodicClearingCreditClaimLifecycle

/-!
# Periodic default-side loss allocation

At each finite depth this module reads the C6 credit and the richer M9
default-side split from the same old-root visit.  It creates no occurrence,
registry, ledger, root, core, action, or completed future.  In particular,
the C6 carried `2 → 2` row remains distinct from the revised first-write
`2 → 1 + 1` structural split.

This is the strongest same-visit source/action producer, not a runtime
resumption receipt.  For a noninitial visit, construction of `jointCoreAt`
does not by itself prove that the canonical inquiry runtime selected that
core; the later sequential-runtime consumer must generate that authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicDefaultSideLossAllocation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M9ProofCarryingRenewalU8Revision
open M14UBIPeriodicRootHistory
open M14PeriodicClearingBackstopRenewal
open M14PeriodicClearingCreditClaimLifecycle
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld

/-- Depth-only bridge between the existing C6 row and the richer revised
first write at that literal old-root visit. -/
structure SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt
    (depth : Nat) : Type 18 where
  private mk ::
  temporalVisitExact :
    Sigma.fst (periodicClearingBackstopOccurrenceAt depth) =
      (.finite (rootVisitAt depth) :
        SourceNativeTemporalVisitAt
          jointRoot.toAuthoritativeRoot.toLedgerRoot)
  rootOccurrenceExact :
    (sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
      ).backstop.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (.finite (rootVisitAt depth))
  sourceAndTargetRowsExact :
    (sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
      ).backstop.installed.payload.sourceEntry =
        (rootedAt (rootVisitAt depth)).rootEntry ∧
      (sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
        ).backstop.appliedReform.targetEntry =
          (rootedAt (rootVisitAt depth)).oldTargetEntry ∧
      (lossAllocationOldTargetOpenLedger (rootedAt (rootVisitAt depth))
        ).forward
          (sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
            ).backstop.appliedReform.targetEntry =
        oldRevisedEntryAt (rootVisitAt depth)
  coreAndActionGroundingExact :
    (jointCoreAt (rootVisitAt depth)).frontier.rooted =
        rootedAt (rootVisitAt depth) ∧
      (jointCoreAt (rootVisitAt depth)).revision =
        (generatedDefaultSideLossAllocationAt
          (rootVisitAt depth)).fieldGroundedRevision
  actionRowsExact :
    let action :=
      generatedDefaultSideLossAllocationAt (rootVisitAt depth)
    (action.successor.ledgerEvolution.origin action.left).1 =
        oldRevisedEntryAt (rootVisitAt depth) ∧
      (action.successor.ledgerEvolution.origin action.right).1 =
        oldRevisedEntryAt (rootVisitAt depth) ∧
      action.left = revisedLossChildAAt (rootVisitAt depth) ∧
      action.right = revisedLossChildBAt (rootVisitAt depth)
  compilerSelectsExactSplit :
    let revision := generatedTypedRevisionAt (rootVisitAt depth)
    let action :=
      generatedDefaultSideLossAllocationAt (rootVisitAt depth)
    (revision.exactInitialRestructuringCertification action.successor).split
        action.left action.right action.origin_eq =
      SourceNativeSplitClassificationAt.split action.split
  wholeMaterialExact :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    let material := sourceGeneratedLossAllocationMaterial
    credit.defaultOccurrence = material.defaultOccurrence ∧
      credit.backstop.installed.payload.sourceSeed =
        material.activationSeed ∧
      HEq credit.standing material.standing ∧
      credit.downsideBearer = material.parentBearer ∧
      material.defaultOccurrence =
        M14ClearingConsumerDeath.sourceGeneratedClearingConsumerDeath ∧
      material.activationSeed =
        M14SourceGeneratedClearingBackstopActivation.sourceGeneratedClearingBackstopExactSeed
  claimExact :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    let revision := generatedTypedRevisionAt (rootVisitAt depth)
    let action :=
      generatedDefaultSideLossAllocationAt (rootVisitAt depth)
    credit.sourceClaim = credit.futureClaim ∧
      revision.translation.claim.forward credit.sourceClaim =
        (oldRevisedEntryAt (rootVisitAt depth)).claim ∧
      revision.translation.claim.forward credit.sourceClaim =
        (action.left).claim ∧
      revision.translation.claim.forward credit.futureClaim =
        (action.right).claim
  bearerExact :
    let revision := generatedTypedRevisionAt (rootVisitAt depth)
    let action :=
      generatedDefaultSideLossAllocationAt (rootVisitAt depth)
    ((revision.sourceFixedRestructuringLaw).obligationAt
        revision.initialRestructuringGenerated.occurrence
        action.left).bearer =
        sourceGeneratedLossAllocationMaterial.childBearerAt .a ∧
      ((revision.sourceFixedRestructuringLaw).obligationAt
        revision.initialRestructuringGenerated.occurrence
        action.right).bearer =
        sourceGeneratedLossAllocationMaterial.childBearerAt .b ∧
      ((revision.sourceFixedRestructuringLaw).obligationAt
        revision.initialRestructuringGenerated.occurrence
        action.left).bearer ≠
        ((revision.sourceFixedRestructuringLaw).obligationAt
          revision.initialRestructuringGenerated.occurrence
          action.right).bearer
  carriedRowIsNotTheSplit :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.rowEvolution = LedgerEntryEvolutionAt.carried rfl HEq.rfl ∧
      ¬ (credit.backstop.appliedReform.targetEntry.progressBudget <
        credit.backstop.installed.payload.sourceEntry.progressBudget)
  splitBudgetsExact :
    let action :=
      generatedDefaultSideLossAllocationAt (rootVisitAt depth)
    (oldRevisedEntryAt (rootVisitAt depth)).progressBudget = 2 ∧
      action.left.progressBudget = 1 ∧
      action.right.progressBudget = 1 ∧
      action.left.progressBudget <
        (oldRevisedEntryAt (rootVisitAt depth)).progressBudget ∧
      action.right.progressBudget <
        (oldRevisedEntryAt (rootVisitAt depth)).progressBudget
  oldRootNextExact :
    let credit :=
      sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
    credit.generatedRootNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      credit.backstop.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1)

namespace SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt

variable {depth : Nat}

/-- C6 is read at the carrier's depth; it is not accepted by the producer. -/
def credit
    (_carrier :
      SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth) :=
  sourceGeneratedProofCarryingPeriodicClearingCreditAt depth

/-- Literal old-root visit underlying C6 and the U8 failure. -/
def visit
    (_carrier :
      SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth) :=
  rootVisitAt depth

/-- Same-visit rooted failure readout. -/
def rooted
    (_carrier :
      SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth) :=
  rootedAt (rootVisitAt depth)

/-- Same-visit unique U8 core readout. -/
def core
    (_carrier :
      SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth) :=
  jointCoreAt (rootVisitAt depth)

/-- Same-visit generated default-side action readout. -/
def action
    (_carrier :
      SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth) :=
  generatedDefaultSideLossAllocationAt (rootVisitAt depth)

end SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt

/-- Sole public producer.  Its only argument is temporal depth. -/
def sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt
    (depth : Nat) :
    SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth := by
  let credit :=
    sourceGeneratedProofCarryingPeriodicClearingCreditAt depth
  let action :=
    generatedDefaultSideLossAllocationAt (rootVisitAt depth)
  exact
    { temporalVisitExact := rfl
      rootOccurrenceExact := rfl
      sourceAndTargetRowsExact := ⟨rfl, rfl, rfl⟩
      coreAndActionGroundingExact := ⟨rfl, rfl⟩
      actionRowsExact := ⟨rfl, rfl, rfl, rfl⟩
      compilerSelectsExactSplit := action.compiler_selects_exact_split
      wholeMaterialExact := ⟨rfl, rfl, HEq.rfl, rfl, rfl, rfl⟩
      claimExact := ⟨credit.sameClaimFromDebtLineage, rfl, rfl, rfl⟩
      bearerExact := ⟨rfl, rfl, action.bearers_distinct⟩
      carriedRowIsNotTheSplit :=
        ⟨credit.fixedRowEvolutionCarried, credit.noStrictBudgetDebit⟩
      splitBudgetsExact :=
        ⟨rfl, rfl, rfl, action.left_budget_strictly_debited,
          action.right_budget_strictly_debited⟩
      oldRootNextExact :=
        ⟨credit.rootCompilerNextExact, credit.backstop.nextVisitExact⟩ }

theorem every_depth_generates_defaultSideLossAllocation (depth : Nat) :
    Nonempty
      (SourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth) :=
  ⟨sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth⟩

/-- Depth zero is definitionally the already installed fixed C6/M9 data. -/
theorem depthZero_restricts_to_fixed :
    let periodic :=
      sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt 0
    periodic.credit =
        sourceGeneratedProofCarryingPeriodicClearingCreditAt 0 ∧
      periodic.rooted = M9ProofCarryingRenewalU8Failure.rooted ∧
      periodic.core = M9ProofCarryingRenewalU8Revision.jointCore ∧
      periodic.action =
        M9ProofCarryingRenewalU8RevisedWorld.generatedDefaultSideLossAllocation :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem periodic_defaultSide_backstopOccurrence_injective :
    Function.Injective periodicClearingBackstopOccurrenceAt :=
  periodic_clearingCredit_backstopOccurrence_injective

theorem adjacent_defaultSide_backstopOccurrences_distinct (depth : Nat) :
    periodicClearingBackstopOccurrenceAt depth ≠
      periodicClearingBackstopOccurrenceAt (depth + 1) :=
  adjacent_clearingCredit_backstopOccurrences_distinct depth

theorem no_single_backstop_occurrence_carries_all_defaultSide_depths :
    ¬ ∃ occurrence : AnyPeriodicClearingBackstopOccurrence,
      ∀ depth : Nat,
        periodicClearingBackstopOccurrenceAt depth = occurrence :=
  no_single_backstop_occurrence_carries_all_clearingCredit_depths

/-- Explicit negative control: the depth-zero occurrence cannot be reused as
the occurrence of every periodic action. -/
theorem constant_depthZero_occurrence_cannot_serve_all_depths :
    ¬ ∀ depth : Nat,
      periodicClearingBackstopOccurrenceAt depth =
        periodicClearingBackstopOccurrenceAt 0 := by
  intro constantReuse
  exact no_single_backstop_occurrence_carries_all_defaultSide_depths
    ⟨periodicClearingBackstopOccurrenceAt 0, constantReuse⟩

theorem periodic_defaultSide_mouth_has_no_submitted_authority_or_future
    (depth : Nat) : True := by
  let periodic :=
    sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt depth
  fail_if_success exact periodic.submittedCredit
  fail_if_success exact periodic.submittedVisit
  fail_if_success exact periodic.submittedRooted
  fail_if_success exact periodic.submittedCore
  fail_if_success exact periodic.submittedAction
  fail_if_success exact periodic.secondOccurrence
  fail_if_success exact periodic.parallelLedger
  fail_if_success exact periodic.riskPool
  fail_if_success exact periodic.merge
  fail_if_success exact periodic.localContentToRootClaim
  fail_if_success exact periodic.completedFuture
  trivial

end
end M14PeriodicDefaultSideLossAllocation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicDefaultSideLossAllocation.sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicDefaultSideLossAllocation.depthZero_restricts_to_fixed
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicDefaultSideLossAllocation.constant_depthZero_occurrence_cannot_serve_all_depths
