import H0mework.Foundation.Runtime.Inquiry
import H0mework.Checks.Runtime.U8Completion

/-!
# Regression: canonical inquiry runtime crosses U8

The runtime reuses the existing inquiry process. Its first activation belongs
to the source; each subsequent activation is generated from the preceding
exact transition. The first tick is the existing U8 occurrence and later
ticks run in the generated revised living root. A one-shot local inquiry
cannot masquerade as an autonomous world runtime after its query fibre closes.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalInquiryRuntimeRegression

open RootInquiryCompletion
open RootInquiryU8CompletionRegression

universe u

def runtimeInitialQuery : (process.stateAt process.initial).Query := ()

theorem runtimeInitialQuery_unique
    (candidate : (process.stateAt process.initial).Query) :
    candidate = runtimeInitialQuery := by
  cases candidate
  rfl

def runtimeNextQueryAt
    (state : ProcessState)
    (query : (process.stateAt state).Query) :
    (process.stateAt (process.successorAt state query).1).Query := by
  cases state with
  | original => exact ()
  | revised _index => exact ()

theorem runtimeNextQuery_unique
    (state : ProcessState)
    (query : (process.stateAt state).Query)
    (candidate :
      (process.stateAt (process.successorAt state query).1).Query) :
    candidate = runtimeNextQueryAt state query := by
  cases state with
  | original => cases candidate; rfl
  | revised _index => cases candidate; rfl

def runtime : SourceNativeInquiryRuntime process where
  activationLaw :=
    Engine.SourceNativeInquiryActivationLaw.ofUnique
      runtimeInitialQuery runtimeInitialQuery_unique
      runtimeNextQueryAt runtimeNextQuery_unique

def firstTick := runtime.tickAt 0

theorem firstTick_eq_existing : firstTick.rawReadout = first :=
  firstTick.rawReadout.eq_of_same_inquiry first

/-- The runtime's first macro tick is the existing U7-first U8 resolution. -/
theorem firstTick_resolution_is_revised :
    firstTick.resolution =
      .revised obstruction u7Gate failure generatedCompletion := by
  change first.resolution =
    .revised obstruction u7Gate failure generatedCompletion
  exact first_resolution_is_revised

/-- The candidate certified at the build frontier is the exact revised core
consumed by this named runtime's first tick. -/
theorem cofaceRealizationRuntimeResumption :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      generatedRevisionCore runtime 0 where
  contains_core := by
    rw [firstTick_resolution_is_revised]
    exact HEq.rfl

/-- The runner-facing certificate is now one proposition.  Core, candidate
certification and generated runtime next remain sealed inside it. -/
theorem cofaceRealizationInstalled :
    SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
      cofaceFrontier cofaceRealizationCandidate runtime 0 := by
  exact ⟨generatedRevisionCore,
    cofaceRealizationCertification,
    cofaceRealizationRuntimeResumption⟩

/-- Any other core claiming authority for this exact problem occurrence is
definitionally the core already consumed by the named runtime. -/
theorem cofaceRealizationRuntimeCore_unique
    {Core : Type 11} {core : Core}
    (candidate : SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      core runtime 0) :
    HEq core generatedRevisionCore :=
  candidate.core_heq cofaceRealizationRuntimeResumption

/-- The reporter reads the U8 branch already selected by the fixed inquiry
compiler; it does not submit a branch token. -/
theorem firstTick_resolutionKind_is_revised :
    firstTick.resolutionKind = .revised := by
  have resolution_eq := congrArg RootInquiryProcessNode.resolutionKind
    firstTick_resolution_is_revised
  exact resolution_eq

/-- Runtime continuation after the U8 macro uses the generated revised living
root, not the old fixed-law micro-successor. -/
theorem firstTick_next_uses_exact_revised_living_root :
    HEq
      (processPresentation (.revised 2)).state.base.root
      generatedCompletion.revisionReceipt.revision.generate.newLivingRoot := by
  exact first_next_uses_exact_revised_living_root

/-- The U8 macro successor cannot be replaced by the old-root micro
successor: their registered network supports are different. -/
theorem firstTick_next_is_not_old_micro_successor :
    (process.stateAt (.revised 2)).erase ≠
      (⟨N, (presentation.state.base.oldAnswerAndNext ()).nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) := by
  intro equality
  have network_eq := congrArg AnyAuthoritativeRootCurrent.N equality
  have support_eq := congrArg WorldRelationNetwork.Support network_eq
  exact bool_ne_newSupport support_eq.symm

/-- The second runtime tick is already executed inside the revised root. -/
theorem secondTick_eq_existing : (runtime.tickAt 1).rawReadout = second :=
  (runtime.tickAt 1).rawReadout.eq_of_same_inquiry second

theorem secondTick_is_revised_root_answer :
    (runtime.tickAt 1).resolution =
      .directlyAnswered (revisedAnswerFaceAt 2)
        (revisedAnswerConsumerAt 2) := by
  change second.resolution =
    .directlyAnswered (revisedAnswerFaceAt 2)
      (revisedAnswerConsumerAt 2)
  exact second_resolution_is_direct

theorem secondTick_resolutionKind_is_direct :
    (runtime.tickAt 1).resolutionKind = .directlyAnswered := by
  have resolution_eq := congrArg RootInquiryProcessNode.resolutionKind
    secondTick_is_revised_root_answer
  exact resolution_eq

/-- Three ticks are a recursively generated finite observation, not a
completed future table. -/
def threeTickHistory := runtime.run 3

/- The previous completed activation table and arbitrary runtime-state
constructor remain absent from the public surface. -/
/-- error: Unknown constant `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.Engine.SourceNativeInquiryActivationLaw.activationAt` -/
#guard_msgs (substring := true) in
#check Engine.SourceNativeInquiryActivationLaw.activationAt

/-- error: Unknown constant `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.State.mk` -/
#guard_msgs (substring := true) in
#check SourceNativeInquiryRuntime.State.mk

/- The authority-occurrence constructor is private; raw `Engine.ask` results
cannot be wrapped into a fixed runtime. -/
/-- error: Unknown constant `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.mk` -/
#guard_msgs in
#check SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.mk

def rawOccurrenceCannotBecomeRuntimeAuthority : PUnit := by
  fail_if_success
    exact (first :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt
        runtime.initialState)
  exact PUnit.unit

/-- A raw sealed engine is not itself a reachable inquiry-runtime state. -/
def rawEngineCannotTick : PUnit := by
  fail_if_success
    exact SourceNativeInquiryRuntime.State.tick engine
  exact PUnit.unit

/-- The activation generated for a later sibling state cannot be replayed at
the preceding state. -/
def siblingActivationCannotReplay : PUnit := by
  let preceding := runtime.stateAt 1
  let sibling := runtime.stateAt 2
  fail_if_success
    exact (show Engine.SourceNativeInquiryActivationAt preceding.engine from
      sibling.activation)
  exact PUnit.unit

/-- A local one-shot inquiry is not an autonomous world runtime. After its
single answer, the next query fibre is empty and the recursive activation law
cannot be installed. -/
theorem oneShot_has_no_autonomous_runtime
    (state : RootInquiryStatePresentation.{u}) :
    IsEmpty (SourceNativeInquiryRuntime state.oneShotProcess) := by
  constructor
  intro candidate
  let initialActivation := candidate.activationLaw.initial
  have impossible :=
    candidate.activationLaw.nextAt none initialActivation
  let impossibleQuery : PEmpty := impossible.query
  exact nomatch impossibleQuery

#print axioms SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.eq_tick
#print axioms Engine.SourceNativeInquiryActivationLaw.ofUnique
#print axioms Engine.SourceNativeInquiryActivationLaw.nextAfter
#print axioms SourceNativeInquiryRuntime.stateAt_succ
#print axioms SourceNativeInquiryRuntime.stateAt_succ_engine
#print axioms SourceNativeInquiryRuntime.stateAt_succ_activation
#print axioms SourceNativeInquiryRuntime.run_zero
#print axioms SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.resolutionKind
#print axioms firstTick_resolution_is_revised
#print axioms cofaceRealizationRuntimeResumption
#print axioms SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
#print axioms cofaceRealizationInstalled
#print axioms SourceNativeInquiryRuntime.CofaceRealizationResumptionAt.core_heq
#print axioms cofaceRealizationRuntimeCore_unique
#print axioms firstTick_resolutionKind_is_revised
#print axioms firstTick_next_uses_exact_revised_living_root
#print axioms firstTick_next_is_not_old_micro_successor
#print axioms secondTick_is_revised_root_answer
#print axioms secondTick_resolutionKind_is_direct
#print axioms oneShot_has_no_autonomous_runtime
#print axioms rawEngineCannotTick
#print axioms rawOccurrenceCannotBecomeRuntimeAuthority
#print axioms siblingActivationCannotReplay

end CanonicalInquiryRuntimeRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
