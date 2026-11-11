import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticCompletionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticIncidenceRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticCompletionRegression

open ArithmeticFreeClosure
open ArithmeticFreeClosure.DerivedArithmeticOccurrence
open RootArithmeticIncidence
open RootArithmeticIncidenceRegression
open RootArithmeticCompletion

def jointDirection : GeneratedArithmeticClosureDirectionAt step :=
  .joint generatedJointResidual

theorem exact_parallel_has_no_completion_direction :
    IsEmpty (GeneratedParallelResidualAt step step.material) :=
  ⟨fun residual => residual.mismatch rfl⟩

def completion : RootArithmeticCompletionReceiptAt step jointDirection :=
  sourceGeneratedMinimalClosure jointDirection

def derivedFace : RootDerivedArithmeticOccurrenceAt completion :=
  completion.derivedOccurrence

theorem residual_generates_actual_extension :
    completion.completionNode =
      FreeClosureAt.extend jointDirection
        (.base (step.material.left.joint step.material.right)) :=
  rfl

theorem generated_completion_cannot_stall_at_old_carrier
    (history : ArithmeticGeneration.UnitHistory) :
    completion.completionNode ≠ FreeClosureAt.base history :=
  completion.completionNode_ne_base history

/-- The joint defect is read stably as actual minus expected: `5 - 6`. -/
theorem joint_defect_has_derived_cofiber_shadow :
    derivedFace.occurrence.eulerShadow = -1 := by
  decide

theorem joint_defect_fiber_has_opposite_shadow :
    (DerivedArithmeticOccurrence.fiber
      (.joint (.atom step.material.left) (.atom step.material.right))
      (.atom step.material.whole)).eulerShadow = 1 := by
  decide

theorem dual_preserves_euler_shadow :
    (DerivedArithmeticOccurrence.dual
      derivedFace.occurrence).eulerShadow = -1 := by
  decide

theorem derived_face_preserves_receipt_ledger_and_next :
    HEq derivedFace.wholeLedgerWriteBack completion.wholeLedgerWriteBack ∧
      derivedFace.nextCurrent = completion.nextCurrent :=
  ⟨HEq.rfl, rfl⟩

theorem completion_reuses_obstructed_whole_ledger :
    HEq completion.wholeLedgerWriteBack step.wholeLedgerWriteBack :=
  HEq.rfl

theorem completion_reuses_obstructed_next :
    completion.nextCurrent =
      materialRoot.generatedNextCurrentAt materialVisit :=
  rfl

/-- No domain realization can reinterpret the free node after agreeing on
the base and local extension action. -/
theorem completion_realization_is_initial
    {Carrier : Type}
    (baseAt : ArithmeticGeneration.UnitHistory → Carrier)
    (extendAt : GeneratedArithmeticClosureDirectionAt step →
      Carrier → Carrier)
    (candidate : FreeArithmeticCompletionAt step → Carrier)
    (base_commutes : (history : ArithmeticGeneration.UnitHistory) →
      candidate (.base history) = baseAt history)
    (extend_commutes :
      (direction : GeneratedArithmeticClosureDirectionAt step) →
      (prior : FreeArithmeticCompletionAt step) →
      candidate (.extend direction prior) =
        extendAt direction (candidate prior)) :
    candidate completion.completionNode =
      completion.realize baseAt extendAt :=
  completion.realize_unique baseAt extendAt candidate
    base_commutes extend_commutes

theorem caller_cannot_construct_completion_receipt : True := by
  fail_if_success
    exact (⟨⟩ : RootArithmeticCompletionReceiptAt step jointDirection)
  trivial

theorem sibling_visit_completion_cannot_replay : True := by
  fail_if_success
    exact (completion : RootArithmeticCompletionReceiptAt nextStep jointDirection)
  trivial

#print axioms ArithmeticFreeClosure.FreeClosureAt.fold_unique
#print axioms DerivedArithmeticOccurrence.fold_unique
#print axioms DerivedArithmeticOccurrence.eulerShadow_cofiber
#print axioms DerivedArithmeticOccurrence.eulerShadow_fiber
#print axioms DerivedArithmeticOccurrence.eulerShadow_dual
#print axioms DerivedArithmeticOccurrence.determinantShadow_cofiber
#print axioms DerivedArithmeticOccurrence.determinantShadow_fiber
#print axioms DerivedArithmeticOccurrence.determinantShadow_dual
#print axioms RootArithmeticCompletionReceiptAt.realize_unique
#print axioms RootDerivedArithmeticOccurrenceAt.unique
#print axioms exact_parallel_has_no_completion_direction
#print axioms joint_defect_has_derived_cofiber_shadow
#print axioms derived_face_preserves_receipt_ledger_and_next
#print axioms completion_reuses_obstructed_whole_ledger
#print axioms completion_reuses_obstructed_next
#print axioms sibling_visit_completion_cannot_replay

end RootArithmeticCompletionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
