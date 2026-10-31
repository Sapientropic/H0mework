import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingLegislation

/-!
# Literal joint-occurrence proof-carrying legislation regression

The sole PCL in this regression consumes the depth-zero occurrence of the
joint renewal/inquiry runtime.  Its renewal restriction was installed before
emission; its revolutionary core, first write, two revised rows, and
heterogeneous next are all read from that same automatic runtime tick.

Every declaration below remains a restriction of that one literal joint
runtime occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingLegislationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open Lifecycle Universal Exchange Settlement Renewal Observer Legislation Revision
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3SettlementDispositionRegression
open M6GoNaturalAuthorityReconstructionRegression
open M8RelationshipMaintenanceRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingRenewalInquiryRuntime

/-! ## Sole literal-occurrence PCL -/

/-- The PCL producer accepts only the installed renewal, the named runtime,
depth zero, and their exact splice.  It receives no branch or U8 core. -/
def proofCarryingLegislation : ProofCarryingLegislationAt
    installedRenewal jointRuntime 0 runtimeSplice :=
  sourceGeneratedProofCarryingLegislation
    installedRenewal jointRuntime 0 runtimeSplice

/-- Independent downstream mouth of the exact PCL occurrence. -/
def proofCarryingLegislationConsumer :=
  proofCarryingLegislation.independentConsumer

/-! ## Exact pre-emitter renewal restriction -/

@[simp] theorem renewalRestriction_is_preEmitterRestriction :
    proofCarryingLegislation.renewalRestriction = proofCarryingRestriction :=
  rfl

@[simp] theorem localConsumer_preserves_relationshipConsumer :
    proofCarryingLegislation.localResponsibilityConsumer.existingLocalConsumer =
      relationshipConsumer :=
  rfl

@[simp] theorem localLifecycle_is_M1_wholeCompilation :
    proofCarryingLegislation.localLifecycle =
      Lifecycle.Universal.FixedAdapter.law.wholeCompilation :=
  rfl

@[simp] theorem existingResidual_is_M3_maintainedResidual :
    proofCarryingLegislation.existingResidual =
      M9ProofCarryingRenewalInquiryRoot.existingResidual :=
  rfl

@[simp] theorem residualBearer_is_M3_maintainedBearer :
    proofCarryingLegislation.residualBearer =
      (maintainOpen .a).residualBearer :=
  rfl

@[simp] theorem observerKernel_is_M6_canonicalKernel :
    proofCarryingLegislation.observerKernel =
      canonicalAuthorityKernelPair
        (goAuthorityChangingVerticalAutomorphism 1) :=
  rfl

/-! ## Literal root / visit / row / occurrence splice -/

theorem inquiryRoot_is_literalJointRoot : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
    jointRoot :=
  proofCarryingLegislation.inquiryRoot_heq_installedRoot

theorem inquiryVisit_is_literalJointVisit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit
    jointVisit :=
  proofCarryingLegislation.inquiryVisit_heq_installedVisit

theorem inquiryRow_is_literalInstalledRenewalRow : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.entryAt
      (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).2)
    installedRenewal.payload.sourceEntry :=
  proofCarryingLegislation.inquiryRow_heq_installedRenewalRow

theorem inquiryOccurrence_is_literalInstalledOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit) :=
  proofCarryingLegislation.inquiryOccurrence_heq_installedOccurrence

/-! ## Automatic revolutionary consumer -/

@[simp] theorem automatic_revisionKind_is_revolution :
    proofCarryingLegislation.revisionKind =
      SourceGeneratedInstitutionalRevisionKind.revolution :=
  rfl

/-- Exact revolutionary consumer automatically recovered from the PCL tick. -/
def exactRevolutionaryConsumption :
    Sigma fun revolution : SourceGeneratedRevolutionaryTickAt jointRuntime 0 =>
      ProofCarryingRevolutionaryConsumptionAt
        proofCarryingLegislation revolution :=
  (proofCarryingLegislation.revolutionaryConsumption?).get (by rfl)

@[simp] theorem revolutionaryConsumption_is_exact_some :
    proofCarryingLegislation.revolutionaryConsumption? =
      some exactRevolutionaryConsumption :=
  rfl

@[simp] theorem revolutionaryConsumption_core_is_jointCore :
    exactRevolutionaryConsumption.1.core = jointCore :=
  rfl

theorem revolutionaryConsumption_resumes_jointCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0 :=
  exactRevolutionaryConsumption.2.resumption

/-- Exact attached-coface realization containing the canonical first write
and its new-row consumption receipt. -/
def revolutionaryFirstWriteRealization :=
  exactRevolutionaryConsumption.2.firstWriteRealization

/-- Canonical revised-root first write consumed by the PCL revolution. -/
def revolutionaryFirstWrite :=
  exactRevolutionaryConsumption.2.firstWrite

/-- Exact new-only row written by that first write. -/
def revolutionaryFirstWriteConsumes :=
  exactRevolutionaryConsumption.2.firstWriteConsumes

/-- Complete initial factorization, first-write realization, and both revised
row answer-and-next consumers. -/
def revolutionaryTwoRowAnswerAndNext :=
  exactRevolutionaryConsumption.2.twoRowAnswerAndNext

theorem revolutionaryTwoRows_share_generatedNext :
    exactRevolutionaryConsumption.2.oldRowAnswerAndNext.nextCurrent =
      exactRevolutionaryConsumption.2.newRowAnswerAndNext.nextCurrent :=
  exactRevolutionaryConsumption.2.twoRows_share_generatedNext

/-! ## Heterogeneous macro next and whole-ledger factorization -/

@[simp] theorem pcl_generatedNext_is_revolutionaryRevisedNext :
    proofCarryingLegislation.generatedNext =
      exactRevolutionaryConsumption.2.revisedNext :=
  rfl

@[simp] theorem pcl_generatedNext_is_macroTickErasure :
    proofCarryingLegislation.generatedNext =
      (jointRuntime.tickAt 0).next.node.erase :=
  rfl

set_option linter.defProp false in
def pcl_macroNext_erases_to_generated :=
  proofCarryingLegislation.next_erases_to_generated

@[simp] theorem pcl_wholeLedgerWriteBack_is_literalJointWriteBack :
    proofCarryingLegislation.wholeLedgerWriteBack =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit jointVisit).wholeLedgerWriteBack :=
  rfl

theorem pcl_wholeLedgerAnswerAndNext_factorizes :
    installedRenewal.RootAnswerAndNextFactorizes :=
  proofCarryingLegislation.rootAnswerAndNext_factorizes

/-! ## Independent certificate -/

/-- End-to-end certificate for the sole literal joint occurrence.

The revolutionary dependent object is retained, so the first-write and
two-row readouts remain available without erasing their exact core index. -/
structure ProofCarryingLegislationCertificate : Type 14 where
  legislation : ProofCarryingLegislationAt
    installedRenewal jointRuntime 0 runtimeSplice
  consumer : ProofCarryingLegislationConsumerAt legislation
  restrictionExact : legislation.renewalRestriction = proofCarryingRestriction
  relationshipConsumerExact :
    legislation.localResponsibilityConsumer.existingLocalConsumer =
      relationshipConsumer
  lifecycleExact : legislation.localLifecycle =
    Lifecycle.Universal.FixedAdapter.law.wholeCompilation
  residualExact : legislation.existingResidual =
    M9ProofCarryingRenewalInquiryRoot.existingResidual
  kernelExact : legislation.observerKernel =
    canonicalAuthorityKernelPair
      (goAuthorityChangingVerticalAutomorphism 1)
  sameRoot : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
    jointRoot
  sameVisit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit
    jointVisit
  sameRow : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.entryAt
      (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).2)
    installedRenewal.payload.sourceEntry
  sameOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit)
  automaticRevolution : legislation.revisionKind =
    SourceGeneratedInstitutionalRevisionKind.revolution
  revolution : Sigma fun revolutionaryTick :
      SourceGeneratedRevolutionaryTickAt jointRuntime 0 =>
    ProofCarryingRevolutionaryConsumptionAt legislation revolutionaryTick
  revolutionSelected : legislation.revolutionaryConsumption? = some revolution
  coreExact : HEq revolution.1.core jointCore
  resumption : SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
    jointCore jointRuntime 0
  firstWriteRealization :
    SourceGeneratedAttachedCofaceRealizationAt
      revolution.1.core.revision.generate
  twoRowsShareNext :
    revolution.2.oldRowAnswerAndNext.nextCurrent =
      revolution.2.newRowAnswerAndNext.nextCurrent
  generatedNextIsRevised : legislation.generatedNext = revolution.2.revisedNext
  generatedNextIsMacroTick : legislation.generatedNext =
    (jointRuntime.tickAt 0).next.node.erase
  wholeLedgerWriteBackExact : legislation.wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit jointVisit).wholeLedgerWriteBack
  rootFactorization : installedRenewal.RootAnswerAndNextFactorizes

/-- Direct construction of the independent end-to-end certificate. -/
def proofCarryingLegislationDirectConsumer :
    ProofCarryingLegislationCertificate where
  legislation := proofCarryingLegislation
  consumer := proofCarryingLegislationConsumer
  restrictionExact := renewalRestriction_is_preEmitterRestriction
  relationshipConsumerExact := localConsumer_preserves_relationshipConsumer
  lifecycleExact := localLifecycle_is_M1_wholeCompilation
  residualExact := existingResidual_is_M3_maintainedResidual
  kernelExact := observerKernel_is_M6_canonicalKernel
  sameRoot := inquiryRoot_is_literalJointRoot
  sameVisit := inquiryVisit_is_literalJointVisit
  sameRow := inquiryRow_is_literalInstalledRenewalRow
  sameOccurrence := inquiryOccurrence_is_literalInstalledOccurrence
  automaticRevolution := automatic_revisionKind_is_revolution
  revolution := exactRevolutionaryConsumption
  revolutionSelected := revolutionaryConsumption_is_exact_some
  coreExact := heq_of_eq revolutionaryConsumption_core_is_jointCore
  resumption := revolutionaryConsumption_resumes_jointCore
  firstWriteRealization := revolutionaryFirstWriteRealization
  twoRowsShareNext := revolutionaryTwoRows_share_generatedNext
  generatedNextIsRevised := pcl_generatedNext_is_revolutionaryRevisedNext
  generatedNextIsMacroTick := pcl_generatedNext_is_macroTickErasure
  wholeLedgerWriteBackExact := pcl_wholeLedgerWriteBack_is_literalJointWriteBack
  rootFactorization := pcl_wholeLedgerAnswerAndNext_factorizes

end
end M9ProofCarryingLegislationRegression
end Society
end ProcessGame
end SaturationMonoid
