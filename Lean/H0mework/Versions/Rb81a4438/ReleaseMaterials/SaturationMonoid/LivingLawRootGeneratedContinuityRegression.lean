import H0mework.Foundation.Runtime.GeneratedContinuity
import H0mework.Arithmetic.PrimeShadow.LivingLawRootAnswerNextHistoryRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace GeneratedContinuityDirectSpliceRegression

open ConstructiveRoot
open ConstructiveRoot.RootAnswerNextHistoryRegression

structure ExactStageAt (state : Nat) : Type where
  value : Nat
  value_eq : value = state

def exactStageLaw :
    SourceNativeGeneratedInvariantLaw cofinalProcess :=
  .create ExactStageAt ⟨0, rfl⟩ fun state prior =>
    ⟨prior.value + 1, by rw [prior.value_eq]; rfl⟩

def exactStageHistory :
    SourceNativeGeneratedInvariantHistoryAt exactStageLaw :=
  exactStageLaw.generateHistory

@[simp] theorem cofinalProcess_stateAfter_eq (index : Nat) :
    cofinalProcess.stateAfter index = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change cofinalProcess.successor (cofinalProcess.stateAfter index) = index + 1
      rw [inductionHypothesis]
      rfl

theorem exactStageHistory_value (index : Nat) :
    (exactStageHistory.at index).value = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change (exactStageHistory.at index).value + 1 = index + 1
      rw [inductionHypothesis]

theorem exactStageHistory_uses_exact_root_successor (depth : Nat) :
    (exactStageHistory.currentAt depth).IsGeneratedSuccessor
      (exactStageHistory.currentAt (depth + 1)) :=
  exactStageHistory.current_succ_is_generated depth

def generatedCounterLaw :
    SourceNativeGeneratedContinuityLaw cofinalProcess :=
  SourceNativeGeneratedContinuityLaw.create
    (process := cofinalProcess)
    (PatchAt := fun _state : cofinalProcess.State => Nat)
    (initialAt := 0)
    (advanceAt := fun _state prior => prior + 1)
    (restrictAt := fun _state next => next.pred)
    (advance_restricts := by intro _state prior; simp)

def generatedCounterContinuum :
    SourceNativeGeneratedContinuumAt generatedCounterLaw :=
  generatedCounterLaw.generate

theorem generatedCounter_value (depth : Nat) :
    (show Nat from generatedCounterContinuum.patchAt depth) = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change (show Nat from generatedCounterContinuum.patchAt depth) + 1 =
        depth + 1
      exact congrArg (fun value : Nat => value + 1) inductionHypothesis

theorem generatedCounter_restricts (depth : Nat) :
    generatedCounterLaw.restrictAt (cofinalProcess.stateAfter depth)
        (generatedCounterContinuum.patchAt (depth + 1)) =
      generatedCounterContinuum.patchAt depth :=
  generatedCounterContinuum.restrict_succ_eq depth

theorem generatedCounter_uses_exact_root_successor (depth : Nat) :
    (generatedCounterContinuum.currentAt depth).IsGeneratedSuccessor
      (generatedCounterContinuum.currentAt (depth + 1)) :=
  generatedCounterContinuum.current_succ_is_generated depth

/-- A completed invariant future cannot be supplied in place of the private
canonical history token. -/
theorem caller_cannot_install_completed_invariant_history : True := by
  fail_if_success
    exact (⟨⟩ : SourceNativeGeneratedInvariantHistoryAt exactStageLaw)
  trivial

/-- Nor can a caller install an arbitrary completed compatible family. -/
theorem caller_cannot_install_completed_continuum : True := by
  fail_if_success
    exact (⟨⟩ : SourceNativeGeneratedContinuumAt generatedCounterLaw)
  trivial

#print axioms SourceNativeGeneratedInvariantLaw.generatedAt_succ
#print axioms SourceNativeGeneratedContinuityLaw.generatedAt_unique
#print axioms SourceNativeGeneratedInvariantHistoryAt.current_succ_is_generated
#print axioms SourceNativeGeneratedContinuumAt.restrict_succ_eq
#print axioms SourceNativeGeneratedContinuumAt.current_succ_is_generated
#print axioms SourceNativeGeneratedContinuumAt.patchAt_eq_of_local_generation
#print axioms exactStageHistory_value
#print axioms exactStageHistory_uses_exact_root_successor
#print axioms generatedCounter_value
#print axioms generatedCounter_restricts
#print axioms generatedCounter_uses_exact_root_successor

end GeneratedContinuityDirectSpliceRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
