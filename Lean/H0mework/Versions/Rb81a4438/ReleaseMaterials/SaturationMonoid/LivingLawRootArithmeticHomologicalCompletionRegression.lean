import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticHomologicalCompletionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticProcessRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticHomologicalCompletionRegression

open ArithmeticFreeClosure
open ArithmeticGeneration
open ArithmeticHomologicalCompletion
open RootArithmeticCompletion
open RootArithmeticCompletionRegression
open RootArithmeticHomologicalCompletion
open RootArithmeticIncidenceRegression
open RootArithmeticProcess
open RootArithmeticProcessRegression

def homological : RootGeneratedArithmeticHomologicalCompletionAt process :=
  sourceGeneratedRootArithmeticHomologicalCompletion process

def boundaryComplex := homological.boundaryComplex

def cofinalObservation := homological.cofinalObservation

def relationProfile := homological.relationProfile

def depthOne : UnitHistory := .next .empty
def depthTwo : UnitHistory := .next depthOne
def depthThree : UnitHistory := .next depthTwo

theorem boundary_complex_is_same_generated_cofiber :
    boundaryComplex.residualOccurrence = derivedFace.occurrence :=
  homological.residualOccurrence_eq

theorem long_exact_starts_at_expected_occurrence :
    (cofinalObservation.observationAt .empty).object =
      generatedExpectedOccurrence jointDirection :=
  rfl

theorem long_exact_reaches_actual_occurrence :
    (cofinalObservation.observationAt depthOne).object =
      generatedActualOccurrence step :=
  rfl

theorem long_exact_reaches_generated_residual :
    (cofinalObservation.observationAt depthTwo).object =
      derivedFace.occurrence :=
  rfl

theorem long_exact_rotates_to_shifted_source :
    (cofinalObservation.observationAt depthThree).object =
      .shift (generatedExpectedOccurrence jointDirection) :=
  rfl

def firstBoundarySquare :=
  boundaryComplex.boundarySquareAt boundaryComplex.initialState

theorem consecutive_boundaries_are_composable :
    firstBoundarySquare.first.targetOccurrence =
      firstBoundarySquare.second.sourceOccurrence :=
  firstBoundarySquare.boundaries_compose

theorem residual_boundary_squared_is_zero :
    firstBoundarySquare.normalForm = .zero :=
  firstBoundarySquare.boundary_squared_zero

theorem generated_long_sequence_rotates_every_three_boundaries
    (depth : UnitHistory) :
    (boundaryComplex.objectAt
        (boundaryComplex.stateAfter depth).successor.successor.successor) =
      .shift (boundaryComplex.objectAt
        (boundaryComplex.stateAfter depth)) :=
  boundaryComplex.objectAt_successor_three
    (boundaryComplex.stateAfter depth)

theorem every_generated_view_is_formally_exact (depth : UnitHistory) :
    Nonempty (SourceGeneratedResidualExactAt boundaryComplex
      (cofinalObservation.observationAt depth).state) :=
  ⟨(cofinalObservation.observationAt depth).exact⟩

theorem cofinal_observation_restricts (depth : UnitHistory) :
    (cofinalObservation.observationAt (.next depth)).restrict =
      cofinalObservation.observationAt depth :=
  cofinalObservation.restricts depth

theorem distinct_relation_anchors_cannot_replay : True := by
  fail_if_success
    exact (boundaryComplex.relationProfileAt boundaryComplex.initialState :
      SourceGeneratedRootedRelationProfileAt boundaryComplex
        boundaryComplex.initialState.successor)
  trivial

theorem relation_profile_normal_form_recovers_anchor :
    relationProfile.normalForm.anchor = boundaryComplex.initialState :=
  rfl

theorem rooted_relation_realization_is_forced
    {Carrier : Type}
    (identityAt : Carrier)
    (advance : ResidualBoundaryKind → Carrier → Carrier)
    (candidate : UnitHistory → Carrier)
    (identity_commutes : candidate .empty = identityAt)
    (naturality : (length : UnitHistory) →
      candidate (.next length) =
        advance
          (boundaryComplex.boundaryKindAt
            (relationProfile.anchor.advance length))
          (candidate length))
    (length : UnitHistory) :
    candidate length = rootedRelationFold boundaryComplex
      relationProfile.anchor identityAt advance length :=
  rootedRelationFold_unique boundaryComplex relationProfile.anchor
    identityAt advance candidate identity_commutes naturality length

theorem homological_face_preserves_whole_ledger_and_next :
    HEq homological.wholeLedgerWriteBack
        completion.wholeLedgerWriteBack ∧
      homological.nextCurrent = completion.nextCurrent :=
  ⟨HEq.rfl, rfl⟩

theorem caller_cannot_construct_boundary_complex : True := by
  fail_if_success
    exact (⟨⟩ : SourceGeneratedResidualBoundaryComplexAt
      (generatedExpectedOccurrence jointDirection)
      (generatedActualOccurrence step))
  trivial

theorem caller_cannot_construct_cofinal_observation : True := by
  fail_if_success
    exact (⟨⟩ : SourceGeneratedCofinalResidualObservationAt boundaryComplex)
  trivial

theorem caller_cannot_construct_root_homological_face : True := by
  fail_if_success
    exact (⟨⟩ : RootGeneratedArithmeticHomologicalCompletionAt process)
  trivial

theorem sibling_visit_homological_face_cannot_replay : True := by
  fail_if_success
    exact (homological :
      RootGeneratedArithmeticHomologicalCompletionAt nextProcess)
  trivial

#print axioms SourceGeneratedResidualBoundarySquareAt.boundaries_compose
#print axioms SourceGeneratedResidualBoundarySquareAt.boundary_squared_zero
#print axioms ResidualTriangleState.successor_three
#print axioms SourceGeneratedResidualBoundaryComplexAt.objectAt_successor_three
#print axioms SourceGeneratedResidualBoundaryComplexAt.boundaryKindAt_successor_three
#print axioms SourceGeneratedCofinalResidualObservationAt.restricts
#print axioms residualObservationFold_unique
#print axioms relationProfileNormalForm_reflects_anchor
#print axioms rootedRelationFold_unique
#print axioms RootGeneratedArithmeticHomologicalCompletionAt.residualOccurrence_eq
#print axioms RootGeneratedArithmeticHomologicalCompletionAt.nextCurrent_eq
#print axioms RootGeneratedArithmeticHomologicalCompletionAt.unique
#print axioms boundary_complex_is_same_generated_cofiber
#print axioms residual_boundary_squared_is_zero
#print axioms generated_long_sequence_rotates_every_three_boundaries
#print axioms distinct_relation_anchors_cannot_replay
#print axioms homological_face_preserves_whole_ledger_and_next
#print axioms sibling_visit_homological_face_cannot_replay

end RootArithmeticHomologicalCompletionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
