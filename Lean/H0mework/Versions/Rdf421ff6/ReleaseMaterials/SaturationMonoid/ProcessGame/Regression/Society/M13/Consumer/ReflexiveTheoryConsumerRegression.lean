import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Adoption.ProofCarryingTheoryAdoptionRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Audit.MotherLawBreakingRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Revision.ClaimMigrationRetirementRegression

/-!
# M13 reflexive-theory direct consumer

One certificate keeps both authority stages exact:

* causal adoption, effect, observer kernel and old-root responsibility at the
  literal M9 joint occurrence;
* mother-law audit, rooted failure, minimal coface, runtime first write,
  inherited-claim migration at the revised initial occurrence, and a later
  actual fulfilled retirement.

The old-root renewal next and heterogeneous revised runtime next remain
separate authorities even though their source faces share the old occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M13ReflexiveTheoryConsumerRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Theory Effect Adoption Audit Revision Observer Settlement
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M6GoNaturalAuthorityReconstructionRegression
open M13ReflexiveClaimLifecycleFixture

noncomputable section

namespace Adopt
abbrev value := M13ProofCarryingTheoryAdoptionRegression.adoption
end Adopt

namespace Mother
abbrev value := M13MotherLawBreakingRegression.audit
abbrev gate := M13MotherLawBreakingRegression.u8Gate
end Mother

namespace Self
abbrev value := M13SelfU8Regression.selfU8
end Self

namespace Claim
abbrev migration := M13ClaimMigrationRetirementRegression.migration
abbrev retirement := M13ClaimMigrationRetirementRegression.retirement
end Claim

/-- The classified mother-law failure is the exact rooted failure consumed by
the self-U8 runtime branch. -/
@[simp] theorem motherLaw_gate_is_selfU8_rooted :
    Mother.gate.rooted = Self.value.rooted :=
  rfl

@[simp] theorem motherLaw_coface_is_selfU8_coface :
    Mother.gate.minimalCoface = Self.value.minimalCoface :=
  rfl

/-- Adoption and self-U8 consume one literal old-root whole-ledger write-back. -/
@[simp] theorem adoption_selfU8_same_wholeLedgerWriteBack :
    Adopt.value.wholeLedgerWriteBack = Self.value.wholeLedgerWriteBack :=
  rfl

/-- The mother-law contract audits the same theory which was causally
adopted, not a post-hoc theory text. -/
@[simp] theorem adopted_theory_is_audited_theory :
    Adopt.value.theoryState =
      RootInquiryU8CompletionRegression.oldTheory :=
  rfl

/-- The two lifecycle faces are installed in the literal revised root produced
by this exact self-U8. -/
@[simp] theorem claimLifecycle_root_is_selfU8_revisedRoot :
    M13SelfU8Regression.exactRevolution.core.revision.generate.newLivingRoot =
      revisedLivingRoot :=
  rfl

/-- Renewal-local next and revolutionary macro next deliberately do not mix:
the latter changes the world-network support type. -/
theorem oldRoot_next_ne_revisedNext :
    (⟨M9ProofCarryingRenewalInquiryRoot.N, Adopt.value.generatedNext⟩ :
      AnyAuthoritativeRootCurrent) ≠ Self.value.revisedNext := by
  intro equality
  have network_eq := congrArg AnyAuthoritativeRootCurrent.N equality
  have support_eq := congrArg WorldRelationNetwork.Support network_eq
  exact
    M14SourceGeneratedContributionMergeSupportSeparation.originalSupport_ne_revisedSupport
      support_eq

structure ReflexiveTheoryConsumerCertificate : Type 16 where
  adoption : SourceInstalledCausallyAdoptedTheoryAt
    (recognition := causalTheoryRecognition)
    installedRenewal jointRuntime 0 runtimeSplice
  adoptionConsumer : CausalTheoryAdoptionIndependentConsumerAt adoption
  motherLawAudit : SourceGeneratedMotherLawAuditAt
    M13MotherLawBreakingRegression.contract
    ()
    M13MotherLawBreakingRegression.active
    M13MotherLawBreakingRegression.classified failureFace rfl
  motherLawGate : SourceGeneratedMotherLawU8GateAt motherLawAudit
    authority.toAuthoritativeAuthority successor
  selfU8 : SourceGeneratedReflexiveSelfU8At
    M9ProofCarryingLegislationRegression.proofCarryingLegislation
    M13SelfU8Regression.exactRevolution
    M13SelfU8Regression.exactConsumption
  auditRooted_eq_selfU8Rooted : motherLawGate.rooted = selfU8.rooted
  auditCoface_eq_selfU8Coface : motherLawGate.minimalCoface = selfU8.minimalCoface
  adoptedTheory_eq_oldTheory :
    adoption.theoryState = RootInquiryU8CompletionRegression.oldTheory
  exactEffect : theoryFeedbackCompiler.EffectAt adoption.exactSourceSeed
  exactEffect_eq : exactEffect = adoption.actualEffect
  effectConsumer : theoryFeedbackCompiler.EffectConsumerAt
    adoption.exactSourceSeed exactEffect
  observerNoAuthorityRecovery :
    ¬ Nonempty (AuthorityFactorization (goAuthorityObserver 1))
  sameOldWholeLedger :
    adoption.wholeLedgerWriteBack = selfU8.wholeLedgerWriteBack
  oldRootFactorization : installedRenewal.RootAnswerAndNextFactorizes
  runtimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0
  revisedRowsShareNext :
    selfU8.oldRowAnswerAndNext.nextCurrent =
      selfU8.newRowAnswerAndNext.nextCurrent
  migrationFace : RootClaimMigrationFaceAt (revisedEmitted (0 : Nat))
  migrationFaceProjection :
    revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.project
      .claimMigration (revisedLivingRoot.emitted (0 : Nat)) ⟨rfl⟩ =
        migrationFace
  migrationFaceExact :
    RootClaimMigrationFaceAt.exactMigration migrationFace =
      M13ClaimMigrationRetirementRegression.migration
  migrationSourceEventIsRootOccurrence :
    ClaimP.boundarySource
      M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement.event =
      (⟨(0 : Nat), revisedLivingRoot.emitted (0 : Nat)⟩ :
        RevisedRootOccurrence)
  inheritedClaimStateGenerated :
    inheritedClaimState.current.history = inheritedClaimState.generated.events
  inheritedClaimContentIsRootRow :
    M13ClaimMigrationRetirementRegression.migration.inheritedClaim.content =
      oldRevisedEntry.claim
  inheritedClaimBearerIsRootRow :
    M13ClaimMigrationRetirementRegression.migration.inheritedClaim.bearer =
      oldRevisedEntry.1
  runtimeFirstWrite : CanonicalFirstRootWriteAt
    M13SelfU8Regression.exactRevolution.core.revision.generate.newRoot.toLedgerRoot
  runtimeFirstWrite_eq : runtimeFirstWrite = selfU8.firstWrite
  runtimeFirstWriteConsumes :
    (M13SelfU8Regression.exactRevolution.core.revision.generate.newRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite M13SelfU8Regression.exactRevolution.core.revision.generate.newRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        M13SelfU8Regression.exactRevolution.core.revision.generate.newOnlyEntry
  runtimeFirstWriteTargetIsLaterVisit :
    runtimeFirstWrite.targetVisit = revisedVisitAt 1
  laterVisitIsStrictSuccessor :
    revisedVisitAt 1 = (revisedVisitAt 0).next rfl
  firstWholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source
      (revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          M13ClaimMigrationRetirementRegression.firstVisit).occurrence
  firstGeneratedNext : SourceNativeAuthoritativeRootCurrentAt
    M9ProofCarryingRenewalU8RevisedWorld.NewN
  firstGeneratedNext_eq : firstGeneratedNext =
    revisedLivingRoot.generatedNextCurrentAt
      M13ClaimMigrationRetirementRegression.firstVisit
  semanticReplacement :
    M13ClaimMigrationRetirementRegression.migration.SemanticReplacementAt
  migratedClaimLive : Nonempty
    (ExactSettlementEdge.LiveResidualAt
      M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement)
  migratedClaimNotClosed : ¬ Nonempty
    (ExactSettlementEdge.ClosedSettlementAt
      M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement)
  retirementFace : RootClaimRetirementFaceAt (revisedEmitted (1 : Nat))
  retirementFaceProjection :
    revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.project
      .claimRetirement (revisedLivingRoot.emitted (1 : Nat)) ⟨rfl⟩ =
        retirementFace
  retirementFaceExact :
    RootClaimRetirementFaceAt.exactRetirement retirementFace =
      M13ClaimMigrationRetirementRegression.retirement
  retirementSourceEventIsLaterRootOccurrence :
    ClaimP.boundarySource
      M13ClaimMigrationRetirementRegression.laterConsumer.event =
      (⟨(1 : Nat), revisedLivingRoot.emitted (1 : Nat)⟩ :
        RevisedRootOccurrence)
  firstAndLaterCurrentDistinct :
    M13ClaimMigrationRetirementRegression.firstVisit.current ≠
      M13ClaimMigrationRetirementRegression.laterVisit.current
  laterWholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source
      (revisedLivingRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          M13ClaimMigrationRetirementRegression.laterVisit).occurrence
  laterGeneratedNext : SourceNativeAuthoritativeRootCurrentAt
    M9ProofCarryingRenewalU8RevisedWorld.NewN
  laterGeneratedNext_eq_revisedRows :
    laterGeneratedNext = selfU8.oldRowAnswerAndNext.nextCurrent
  laterActualDisappearance : ResponsibilityState.DisappearsAt
    M13ClaimMigrationRetirementRegression.migration.firstWriteSettlement.edge.target
    (M13ClaimMigrationRetirementRegression.migration.laterSettlement
      M13ClaimMigrationRetirementRegression.laterConsumer).edge.target
    (M13ClaimMigrationRetirementRegression.migration.laterSettlement
      M13ClaimMigrationRetirementRegression.laterConsumer).slot.val
  oldAndRevisedNextDoNotMix :
    (⟨M9ProofCarryingRenewalInquiryRoot.N, adoption.generatedNext⟩ :
      AnyAuthoritativeRootCurrent) ≠ selfU8.revisedNext

def reflexiveTheoryDirectConsumer : ReflexiveTheoryConsumerCertificate where
  adoption := Adopt.value
  adoptionConsumer := Adopt.value.independentConsumer
  motherLawAudit := Mother.value
  motherLawGate := Mother.gate
  selfU8 := Self.value
  auditRooted_eq_selfU8Rooted := motherLaw_gate_is_selfU8_rooted
  auditCoface_eq_selfU8Coface := motherLaw_coface_is_selfU8_coface
  adoptedTheory_eq_oldTheory := adopted_theory_is_audited_theory
  exactEffect := Adopt.value.actualEffect
  exactEffect_eq := rfl
  effectConsumer := Adopt.value.effectConsumer
  observerNoAuthorityRecovery :=
    M13ProofCarryingTheoryAdoptionRegression.visible_observer_cannot_recover_hidden_authority
  sameOldWholeLedger := adoption_selfU8_same_wholeLedgerWriteBack
  oldRootFactorization := Adopt.value.rootAnswerAndNext_factorizes
  runtimeConsumesCore := Self.value.runtime_consumes_core
  revisedRowsShareNext := Self.value.revised_rows_share_generatedNext
  migrationFace := M13ClaimMigrationRetirementRegression.migrationFace
  migrationFaceProjection :=
    M13ClaimMigrationRetirementRegression.migrationFace_is_revisedRoot_projection
  migrationFaceExact :=
    M13ClaimMigrationRetirementRegression.migrationFace_exact
  migrationSourceEventIsRootOccurrence :=
    M13ClaimMigrationRetirementRegression.migration_sourceEvent_is_rootOccurrence
  inheritedClaimStateGenerated :=
    M13ReflexiveClaimLifecycleFixture.inheritedClaimState_history_generated
  inheritedClaimContentIsRootRow :=
    M13ClaimMigrationRetirementRegression.inherited_claim_content_is_revised_oldRow
  inheritedClaimBearerIsRootRow :=
    M13ClaimMigrationRetirementRegression.inherited_claim_bearer_is_revised_oldRow
  runtimeFirstWrite := M13ClaimMigrationRetirementRegression.runtimeFirstWrite
  runtimeFirstWrite_eq := rfl
  runtimeFirstWriteConsumes :=
    M13ClaimMigrationRetirementRegression.runtimeFirstWriteConsumes
  runtimeFirstWriteTargetIsLaterVisit :=
    M13ClaimMigrationRetirementRegression.runtimeFirstWrite_targetVisit_eq_laterRootVisit
  laterVisitIsStrictSuccessor :=
    M13ClaimMigrationRetirementRegression.laterVisit_is_strict_successor
  firstWholeLedgerWriteBack :=
    M13ClaimMigrationRetirementRegression.firstWholeLedgerWriteBack
  firstGeneratedNext :=
    M13ClaimMigrationRetirementRegression.firstGeneratedNext
  firstGeneratedNext_eq := rfl
  semanticReplacement :=
    M13ClaimMigrationRetirementRegression.semanticReplacement
  migratedClaimLive :=
    M13ClaimMigrationRetirementRegression.replaced_claim_is_still_live_and_not_closed.1
  migratedClaimNotClosed :=
    M13ClaimMigrationRetirementRegression.replaced_claim_is_still_live_and_not_closed.2
  retirementFace := M13ClaimMigrationRetirementRegression.retirementFace
  retirementFaceProjection :=
    M13ClaimMigrationRetirementRegression.retirementFace_is_revisedRoot_projection
  retirementFaceExact :=
    M13ClaimMigrationRetirementRegression.retirementFace_exact
  retirementSourceEventIsLaterRootOccurrence :=
    M13ClaimMigrationRetirementRegression.retirement_sourceEvent_is_laterRootOccurrence
  firstAndLaterCurrentDistinct :=
    M13ClaimMigrationRetirementRegression.first_and_later_current_distinct
  laterWholeLedgerWriteBack :=
    M13ClaimMigrationRetirementRegression.laterWholeLedgerWriteBack
  laterGeneratedNext :=
    M13ClaimMigrationRetirementRegression.laterGeneratedNext
  laterGeneratedNext_eq_revisedRows :=
    M13ClaimMigrationRetirementRegression.laterGeneratedNext_eq_selfU8_revisedRows
  laterActualDisappearance :=
    M13ClaimMigrationRetirementRegression.later_event_closes_migrated_claim
  oldAndRevisedNextDoNotMix := oldRoot_next_ne_revisedNext

end
end M13ReflexiveTheoryConsumerRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M13ReflexiveTheoryConsumerRegression.motherLaw_gate_is_selfU8_rooted
#print axioms SaturationMonoid.ProcessGame.Society.M13ReflexiveTheoryConsumerRegression.claimLifecycle_root_is_selfU8_revisedRoot
#print axioms SaturationMonoid.ProcessGame.Society.M13ReflexiveTheoryConsumerRegression.oldRoot_next_ne_revisedNext
#print axioms SaturationMonoid.ProcessGame.Society.M13ReflexiveTheoryConsumerRegression.reflexiveTheoryDirectConsumer
