import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Adoption.SourceInstalledCausalTheoryAdoption
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# M13 proof-carrying causal theory adoption

The theory-feedback restriction is installed inside the existing M9 joint
root before emission.  It preserves the relationship consumer, shares the
literal inquiry root/visit/row/occurrence, and consumes the existing root
responsibility and generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M13ProofCarryingTheoryAdoptionRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Theory Effect Adoption Observer Renewal Legislation
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M8RelationshipMaintenanceRenewalRegression
open M6GoNaturalAuthorityReconstructionRegression

noncomputable section

/-- Sole installed adoption on the literal M9 renewal/runtime splice. -/
def adoption : SourceInstalledCausallyAdoptedTheoryAt
    (recognition := causalTheoryRecognition)
    installedRenewal jointRuntime 0 runtimeSplice :=
  sourceInstalledCausalTheoryAdoption
    (recognition := causalTheoryRecognition)
    installedRenewal jointRuntime 0 runtimeSplice

def adoptionConsumer := adoption.independentConsumer

@[simp] theorem compiler_theory_is_final_root_theory :
    adoption.compilerTheoryState = adoption.theoryState :=
  adoption.compilerTheoryState_eq_adoptedTheory

@[simp] theorem adopted_theory_is_old_law_surface :
    adoption.theoryState = RootInquiryU8CompletionRegression.oldTheory :=
  rfl

theorem adoption_seed_retains_trace_provenance :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
        Lifecycle.actualEventGame.source state adoption.exactSourceSeed.1 :=
  adoption.feedbackTrace.sourceSeed_incidence

@[simp] theorem exact_seed_is_relationship_seed :
    adoption.exactSourceSeed = relationshipRenewalSeed :=
  rfl

/-- M9's existing relationship consumer survives inside the pre-emitter
adoption composite. -/
@[simp] theorem existing_relationship_consumer_is_preserved :
    adoption.existingLocalConsumer = relationshipConsumer :=
  rfl

@[simp] theorem exact_classification_is_focal :
    adoption.classificationReadout.read adoption.exactSourceSeed = true :=
  rfl

@[simp] theorem exact_policy_is_maintain :
    adoption.policyReadout.read adoption.exactSourceSeed = true :=
  rfl

/-- The actual causal effect is the exact M1 lifecycle compilation already
consumed by the same renewal payload. -/
@[simp] theorem actual_effect_is_local_lifecycle :
    adoption.actualEffect = adoption.localLifecycle :=
  rfl

def exactEffectConsumer := adoption.effectConsumer

theorem effect_has_dependent_consumer :
    Nonempty (theoryFeedbackCompiler.EffectConsumerAt
      adoption.exactSourceSeed adoption.actualEffect) :=
  adoption.actualEffect_has_consumer

@[simp] theorem observer_kernel_is_existing_Go_kernel :
    adoption.observerKernel = canonicalAuthorityKernelPair
      (goAuthorityChangingVerticalAutomorphism 1) :=
  rfl

theorem visible_observer_cannot_recover_hidden_authority :
    ¬ Nonempty (AuthorityFactorization (goAuthorityObserver 1)) :=
  go_has_no_authority_factorization 1

theorem same_root : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
    jointRoot :=
  adoption.sameRoot

theorem same_visit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit
    jointVisit :=
  adoption.sameVisit

theorem same_row : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.entryAt
      (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).2)
    installedRenewal.payload.sourceEntry :=
  adoption.sameRow

theorem same_occurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit) :=
  adoption.sameOccurrence

def wholeLedgerWriteBack := adoption.wholeLedgerWriteBack
def rootResponsibilityConsumer := adoption.rootConsumer

theorem root_factorization : installedRenewal.RootAnswerAndNextFactorizes :=
  adoption.rootAnswerAndNext_factorizes

@[simp] theorem generated_next_is_root_next :
    adoption.generatedNext = jointRoot.generatedNextCurrentAt jointVisit :=
  rfl

/-- The ordinary renewal next cannot silently revise the adopted theory.  A
theory change requires the separately generated U8 macro transition. -/
theorem fixedLaw_next_preserves_adoptedTheory :
    adoption.generatedNext.root.source.lawSurface = adoption.theoryState := by
  rw [generated_next_is_root_next]
  exact jointRoot.generatedNextCurrentAt_lawSurface_eq jointVisit

/-- The independent consumer carries no caller-selected result or numeric
field; classification and policy remain derived readouts. -/
theorem independent_consumer_has_no_result_fields : True := by
  fail_if_success exact adoptionConsumer.classification
  fail_if_success exact adoptionConsumer.policyDecision
  fail_if_success exact adoptionConsumer.probability
  trivial

/-- A bare effect cannot be passed to the installed-adoption producer. -/
theorem bare_effect_cannot_replace_installed_adoption : True := by
  let bare : BareTheoryEffectAt theoryFeedbackCompiler
      installedRenewal.payload.sourceSeed :=
    ⟨adoption.actualEffect⟩
  fail_if_success
    exact sourceInstalledCausalTheoryAdoption bare jointRuntime 0 runtimeSplice
  trivial

end
end M13ProofCarryingTheoryAdoptionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M13ProofCarryingTheoryAdoptionRegression.adoption
#print axioms SaturationMonoid.ProcessGame.Society.M13ProofCarryingTheoryAdoptionRegression.actual_effect_is_local_lifecycle
#print axioms SaturationMonoid.ProcessGame.Society.M13ProofCarryingTheoryAdoptionRegression.same_occurrence
#print axioms SaturationMonoid.ProcessGame.Society.M13ProofCarryingTheoryAdoptionRegression.generated_next_is_root_next
#print axioms SaturationMonoid.ProcessGame.Society.M13ProofCarryingTheoryAdoptionRegression.fixedLaw_next_preserves_adoptedTheory
#print axioms SaturationMonoid.ProcessGame.Society.M13ProofCarryingTheoryAdoptionRegression.visible_observer_cannot_recover_hidden_authority
