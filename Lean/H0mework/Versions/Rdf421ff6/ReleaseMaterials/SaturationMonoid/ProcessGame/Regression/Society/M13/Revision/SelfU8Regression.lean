import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Revision.SourceGeneratedReflexiveSelfU8
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.Legislation.ProofCarryingLegislationRegression

/-!
# M13 reflexive self-U8 regression

The existing M9 proof-carrying joint root is consumed directly.  No second
theory root or revision candidate is rebuilt here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M13SelfU8Regression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Theory.Revision Legislation
open Society.Revision
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingLegislationRegression

noncomputable section

abbrev exactRevolution := exactRevolutionaryConsumption.1
abbrev exactConsumption := exactRevolutionaryConsumption.2

/-- The M13 seal consumes the exact revolutionary occurrence already selected
by the M9 canonical runtime. -/
def selfU8 : SourceGeneratedReflexiveSelfU8At
    proofCarryingLegislation exactRevolution exactConsumption :=
  SourceGeneratedReflexiveSelfU8At.generate exactConsumption

@[simp] theorem failure_is_runtime_failure :
    selfU8.failure = RootInquiryU8CompletionRegression.failure :=
  rfl

@[simp] theorem minimalCoface_is_joint_coface :
    selfU8.minimalCoface =
      M9ProofCarryingRenewalU8Failure.coface :=
  rfl

theorem runtime_consumes_exact_joint_core :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      jointCore jointRuntime 0 :=
  selfU8.runtime_consumes_core

@[simp] theorem firstWrite_is_runtime_firstWrite :
    selfU8.firstWrite = exactConsumption.firstWrite :=
  rfl

theorem revised_rows_share_one_next :
    selfU8.oldRowAnswerAndNext.nextCurrent =
      selfU8.newRowAnswerAndNext.nextCurrent :=
  selfU8.revised_rows_share_generatedNext

theorem same_root : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
    jointRoot :=
  selfU8.sameRoot

theorem same_visit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit
    jointVisit :=
  selfU8.sameVisit

theorem same_row : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.entryAt
      (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).2)
    installedRenewal.payload.sourceEntry :=
  selfU8.sameRow

theorem same_occurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit) :=
  selfU8.sameOccurrence

def wholeLedgerWriteBack := selfU8.wholeLedgerWriteBack

theorem root_factorization : installedRenewal.RootAnswerAndNextFactorizes :=
  selfU8.rootAnswerAndNext_factorizes

/-- One exact runtime occurrence has a unique self-U8 seal. -/
theorem selfU8_unique
    (candidate : SourceGeneratedReflexiveSelfU8At
      proofCarryingLegislation exactRevolution exactConsumption) :
    candidate = selfU8 :=
  Subsingleton.elim _ _

/-- A bare failure is not accepted by the self-U8 producer. -/
theorem bare_failure_cannot_generate_selfU8 : True := by
  fail_if_success
    exact SourceGeneratedReflexiveSelfU8At.generate
      RootInquiryU8CompletionRegression.failure
  trivial

/-- A coface frontier is not accepted by the self-U8 producer. -/
theorem frontier_cannot_generate_selfU8 : True := by
  fail_if_success
    exact SourceGeneratedReflexiveSelfU8At.generate
      M9ProofCarryingRenewalU8Revision.frontier
  trivial

end
end M13SelfU8Regression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M13SelfU8Regression.selfU8
#print axioms SaturationMonoid.ProcessGame.Society.M13SelfU8Regression.same_occurrence
#print axioms SaturationMonoid.ProcessGame.Society.M13SelfU8Regression.revised_rows_share_one_next
#print axioms SaturationMonoid.ProcessGame.Society.M13SelfU8Regression.selfU8_unique
