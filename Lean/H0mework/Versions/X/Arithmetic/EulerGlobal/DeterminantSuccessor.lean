import H0mework.Versions.X.Arithmetic.EulerGlobal.DerivedDeterminant
import H0mework.Realization.Determinant.RestrictionAction

/-!
# Full-Euler determinant successor

The actual runtime successor expands the generated prime/exponent support.
Restriction of integral Euler solutions is surjective and intertwines both
the prime action and reversal.  The frozen determinant-factorization kernel
therefore generates the relative kernel factor between consecutive full-Euler
sections.  No local zero fibre or completed cofinal table is formed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerDeterminantSuccessor

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open SurjectiveRestrictionActionDeterminant
open SurjectiveRestrictionActionDeterminant.RootGeneratedSurjectiveRestrictionActionDeterminantAt

noncomputable section

variable (seed : FactorizationPayload) (stage : Nat)

abbrev SourceCarrier := Carrier seed (stage + 1)
abbrev TargetCarrier := Carrier seed stage

def successorRow : SurjectiveRestrictionActionAt
    ℤ (SourceCarrier seed stage) (TargetCarrier seed stage) where
  sourceAction := carrierEulerAction seed (stage + 1)
  targetAction := carrierEulerAction seed stage
  restriction := carrierRestriction seed stage
  restriction_surjective := carrierRestriction_surjective seed stage
  action_square := carrierRestriction_euler_square seed stage

def dependentSuccessorRowOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × SurjectiveRestrictionActionAt
      ℤ (SourceCarrier seed stage) (TargetCarrier seed stage)) :=
  (stageOccurrenceFrom seed (stage + 1)).map fun owner =>
    (owner, successorRow seed stage)

theorem dependentSuccessorRowOccurrence_projects :
    (dependentSuccessorRowOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed (stage + 1) := by
  unfold dependentSuccessorRowOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed (stage + 1)).map id = _
  exact RootedAccountedUnfolding.map_id _

def successorFace : RootGeneratedSurjectiveRestrictionActionDeterminantAt
    (stageOccurrenceFrom seed (stage + 1))
    (dependentSuccessorRowOccurrence seed stage)
    (dependentSuccessorRowOccurrence_projects seed stage) :=
  RootGeneratedSurjectiveRestrictionActionDeterminantAt.generate

@[simp] theorem successorFace_sourceDeterminantPolynomial :
    (successorFace seed stage).sourceDeterminantPolynomial =
      determinantPolynomial seed (stage + 1) := by
  rfl

@[simp] theorem successorFace_targetDeterminantPolynomial :
    (successorFace seed stage).targetDeterminantPolynomial =
      determinantPolynomial seed stage := by
  rfl

noncomputable def relativeKernelDeterminantPolynomial : Polynomial ℤ :=
  (successorFace seed stage).relativeKernelDeterminantPolynomial

/-- Frozen exact factorization of consecutive generated sections. -/
theorem determinantPolynomial_successor_factorization :
    determinantPolynomial seed (stage + 1) =
      relativeKernelDeterminantPolynomial seed stage *
        determinantPolynomial seed stage := by
  simpa [relativeKernelDeterminantPolynomial] using
    (successorFace seed stage).sourceDeterminantPolynomial_factorization

theorem successor_preserves_reversal :
    (carrierRestriction seed stage).comp
        (carrierReversal seed (stage + 1)) =
      (carrierReversal seed stage).comp
        (carrierRestriction seed stage) :=
  carrierRestriction_reversal_square seed stage

theorem preserves_exact_support_expanding_successor :
    (successorFace seed stage).root =
        stageOccurrenceFrom seed (stage + 1) ∧
      (successorFace seed stage).actualRow.sourceAction =
        carrierEulerAction seed (stage + 1) ∧
      (successorFace seed stage).actualRow.targetAction =
        carrierEulerAction seed stage ∧
      (successorFace seed stage).actualRow.restriction =
        carrierRestriction seed stage ∧
      (carrierRestriction seed stage).comp
          (carrierReversal seed (stage + 1)) =
        (carrierReversal seed stage).comp
          (carrierRestriction seed stage) := by
  refine ⟨dependentSuccessorRowOccurrence_projects seed stage,
    rfl, rfl, rfl, successor_preserves_reversal seed stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerDeterminantSuccessor
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
