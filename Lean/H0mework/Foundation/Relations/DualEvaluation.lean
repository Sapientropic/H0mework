import Mathlib.LinearAlgebra.BilinearMap
import H0mework.Foundation.Arithmetic.IncidenceFace

/-!
# Axiom-free root face for dual evaluation

This file contains only the source/root incidence carrier for a two-sided
integral pairing.  It records the exact root, left/right occurrence families,
and pairing occurrence together with their identity seals.  No linear
algebraic classification, inverse, finite presentation, perfectness, or
determinant machinery is imported here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedDualEvaluation

universe u v w

structure RootGeneratedDualEvaluationPairingAt
    {Root : Type w} {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (leftOccurrences : Left → RootedAccountedUnfolding Left)
    (rightOccurrences : Right → RootedAccountedUnfolding Right)
    (pairingOccurrence : RootedAccountedUnfolding
      (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)) : Type (max u v w + 1) where
  private mk ::
  core : DerivedArithmeticAxiomFreeCore.RootGeneratedDualIncidenceAt
    rootOccurrence leftOccurrences rightOccurrences pairingOccurrence
  left_occurrences_exact : ∀ left, (leftOccurrences left).root = left
  right_occurrences_exact : ∀ right, (rightOccurrences right).root = right

namespace RootGeneratedDualEvaluationPairingAt

variable {Root : Type w} {Left : Type u} {Right : Type v}
variable [AddCommGroup Left] [AddCommGroup Right]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence : RootedAccountedUnfolding
  (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ)}

def generate
    (left_exact : ∀ left, (leftOccurrences left).root = left)
    (right_exact : ∀ right, (rightOccurrences right).root = right) :
    RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence :=
  ⟨DerivedArithmeticAxiomFreeCore.RootGeneratedDualIncidenceAt.generate,
    left_exact, right_exact⟩

def root
    (_face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def left
    (_face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Left → RootedAccountedUnfolding Left :=
  leftOccurrences

def right
    (_face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Right → RootedAccountedUnfolding Right :=
  rightOccurrences

def actualPairing
    (_face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] ℤ) :=
  pairingOccurrence

theorem preserves_occurrences
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    face.root = rootOccurrence ∧
      face.left = leftOccurrences ∧
      face.right = rightOccurrences ∧
      face.actualPairing = pairingOccurrence :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem left_occurrence_root
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence)
    (left : Left) :
    (face.left left).root = left :=
  face.left_occurrences_exact left

theorem right_occurrence_root
    (face : RootGeneratedDualEvaluationPairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence)
    (right : Right) :
    (face.right right).root = right :=
  face.right_occurrences_exact right

end RootGeneratedDualEvaluationPairingAt

end SourceGeneratedDualEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
