import H0mework.Realization.Graph.CokernelDuality
import H0mework.Realization.Graph.CokernelNaturality
import H0mework.Realization.Graph.RealizationNaturality

/-!
# Riesz state in the actual functional-graph target

The canonical quotient Riesz vector has an orthogonal representative in the
generated graph completion and therefore an actual state in the complete
graph target.  Its measurement coordinate is its squared quotient norm.
Every generated graph/relation self-morphism that preserves the functional
makes this realized state stationary.  No isometry, nondegeneracy, finite
dimension, determinant, or domain equation is assumed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphCokernel

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedHilbertCokernel

open scoped InnerProductSpace

noncomputable section

universe c r h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {Rel : Type r} [AddCommGroup Rel] [Module ℂ Rel]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The descended functional evaluates an arbitrary quotient class through
the same graph functional; this is not restricted to the dense source. -/
theorem descendedFunctional_quotientClass_readback
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0)
    (point : GraphHilbertAmbient feature functional) :
    descendedFunctional feature functional relation annihilates
        (quotientClass (relationGraphMap feature functional relation) point) =
      graphHilbertFunctional feature functional point := by
  unfold descendedFunctional quotientClass
  rw [Submodule.liftQL_apply, Submodule.mkQL_apply]
  change (closedRange
      (relationGraphMap feature functional relation)).toSubmodule.liftQ
        (graphHilbertFunctional feature functional).toLinearMap
        (relationClosedRange_le_functional_ker
          feature functional relation annihilates)
        (Submodule.Quotient.mk point) = _
  rw [Submodule.liftQ_apply]
  rfl

variable [CompleteSpace H]

omit [CompleteSpace H] in
private theorem descendedRieszVector_eq_quotientClass_orthogonal
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0) :
    let T := relationGraphMap feature functional relation
    let quotientState :=
      descendedRieszVector feature functional relation annihilates
    let orthogonalState := quotientOrthogonalEquiv T quotientState
    quotientState = quotientClass T
      (orthogonalState : GraphHilbertAmbient feature functional) := by
  dsimp only
  let T := relationGraphMap feature functional relation
  let quotientState :=
    descendedRieszVector feature functional relation annihilates
  let orthogonalState := quotientOrthogonalEquiv T quotientState
  calc
    quotientState = (quotientOrthogonalEquiv T).symm orthogonalState :=
      ((quotientOrthogonalEquiv T).symm_apply_apply quotientState).symm
    _ = quotientClass T (orthogonalState :
        GraphHilbertAmbient feature functional) := by
      change
        ((closedRange T).toSubmodule.quotientEquivOrthogonal).symm
            orthogonalState =
          Submodule.Quotient.mk orthogonalState.1
      exact (closedRange T).toSubmodule.quotientEquivOrthogonal_symm_eq_mk
        orthogonalState.1 orthogonalState.2

/-- The measurement coordinate of the actual realized Riesz state is its
squared quotient norm. -/
theorem realizedRieszState_snd_eq_norm_sq
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0) :
    let quotientState :=
      descendedRieszVector feature functional relation annihilates
    let orthogonalState :=
      quotientOrthogonalEquiv (relationGraphMap feature functional relation)
        quotientState
    (graphHilbertAmbientRealization feature functional orthogonalState).snd =
      ((‖quotientState‖ : ℂ) ^ 2) := by
  dsimp only
  let T := relationGraphMap feature functional relation
  let quotientState :=
    descendedRieszVector feature functional relation annihilates
  let orthogonalState := quotientOrthogonalEquiv T quotientState
  have quotientState_eq :
      quotientState = quotientClass T (orthogonalState :
        GraphHilbertAmbient feature functional) := by
    simpa [T, quotientState, orthogonalState] using
      (descendedRieszVector_eq_quotientClass_orthogonal
        feature functional relation annihilates)
  calc
    (graphHilbertAmbientRealization feature functional orthogonalState).snd =
        graphHilbertFunctional feature functional orthogonalState :=
      graphHilbertAmbientRealization_snd feature functional orthogonalState
    _ = descendedFunctional feature functional relation annihilates
        (quotientClass T orthogonalState) :=
      (descendedFunctional_quotientClass_readback
        feature functional relation annihilates orthogonalState).symm
    _ = descendedFunctional feature functional relation annihilates
        quotientState := by rw [quotientState_eq]
    _ = inner ℂ quotientState quotientState := by
      exact (descendedRieszVector_inner
        feature functional relation annihilates quotientState).symm
    _ = ((‖quotientState‖ : ℂ) ^ 2) :=
      inner_self_eq_norm_sq_to_K quotientState

/-- A generated graph/relation self-morphism preserving the functional makes
the canonical Riesz state stationary after actual-target realization. -/
theorem realizedRieszState_graphMorphism_stationary
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0)
    (morphism : RelationGraphSourceMorphism
      feature functional relation feature functional relation) :
    let quotientState :=
      descendedRieszVector feature functional relation annihilates
    let orthogonalState :=
      quotientOrthogonalEquiv (relationGraphMap feature functional relation)
        quotientState
    let targetState :=
      graphHilbertAmbientRealization feature functional orthogonalState
    inner ℂ targetState (graphTargetMap morphism.graphMorphism targetState) =
      inner ℂ targetState targetState := by
  dsimp only
  let T := relationGraphMap feature functional relation
  let quotientState :=
    descendedRieszVector feature functional relation annihilates
  let orthogonalState := quotientOrthogonalEquiv T quotientState
  have quotientState_eq :
      quotientState = quotientClass T (orthogonalState :
        GraphHilbertAmbient feature functional) := by
    simpa [T, quotientState, orthogonalState] using
      (descendedRieszVector_eq_quotientClass_orthogonal
        feature functional relation annihilates)
  have quotientStationary :
      inner ℂ quotientState (morphism.quotientMap quotientState) =
        inner ℂ quotientState quotientState := by
    rw [descendedRieszVector_inner, descendedRieszVector_inner]
    exact morphism.descendedFunctional_quotientMap
      annihilates annihilates quotientState
  have mappedOrthogonal :
      quotientOrthogonalEquiv T (morphism.quotientMap quotientState) =
        residual T
          (graphCompletionMap morphism.graphMorphism orthogonalState) := by
    rw [quotientState_eq, morphism.quotientMap_quotientClass,
      quotientOrthogonalEquiv_quotientClass]
  have projectedStationary :
      inner ℂ orthogonalState
          (residual T
            (graphCompletionMap morphism.graphMorphism orthogonalState)) =
        inner ℂ orthogonalState orthogonalState := by
    change inner ℂ (quotientOrthogonalEquiv T quotientState)
        (residual T
          (graphCompletionMap morphism.graphMorphism orthogonalState)) =
      inner ℂ (quotientOrthogonalEquiv T quotientState)
        (quotientOrthogonalEquiv T quotientState)
    rw [← mappedOrthogonal]
    exact quotientStationary
  have projectionInvisible :
      inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
          (graphCompletionMap morphism.graphMorphism orthogonalState) =
        inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
          (residual T
            (graphCompletionMap morphism.graphMorphism orthogonalState) :
              GraphHilbertAmbient feature functional) := by
    have closedDifference := sub_residual_mem_closedRange T
      (graphCompletionMap morphism.graphMorphism orthogonalState)
    have orthogonalZero :
        inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
          (graphCompletionMap morphism.graphMorphism orthogonalState -
            (residual T
              (graphCompletionMap morphism.graphMorphism orthogonalState) :
                GraphHilbertAmbient feature functional)) = 0 :=
      Submodule.inner_left_of_mem_orthogonal
        closedDifference orthogonalState.2
    rw [inner_sub_right, sub_eq_zero] at orthogonalZero
    exact orthogonalZero
  have projectedStationaryAmbient :
      inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
          (residual T
            (graphCompletionMap morphism.graphMorphism orthogonalState) :
              GraphHilbertAmbient feature functional) =
        inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
          (orthogonalState : GraphHilbertAmbient feature functional) := by
    exact projectedStationary
  let realization := graphHilbertAmbientRealization feature functional
  calc
    inner ℂ (realization orthogonalState)
        (graphTargetMap morphism.graphMorphism
          (realization orthogonalState)) =
      inner ℂ (realization orthogonalState)
        (realization
          (graphCompletionMap morphism.graphMorphism orthogonalState)) := by
            rw [graphHilbertAmbientRealization_graphCompletionMap]
    _ = inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
        (graphCompletionMap morphism.graphMorphism orthogonalState) := by
          exact LinearIsometry.inner_map_map _ _ _
    _ = inner ℂ (orthogonalState : GraphHilbertAmbient feature functional)
        (orthogonalState : GraphHilbertAmbient feature functional) :=
      projectionInvisible.trans projectedStationaryAmbient
    _ = inner ℂ (realization orthogonalState)
        (realization orthogonalState) := by
          exact (LinearIsometry.inner_map_map realization
            (orthogonalState : GraphHilbertAmbient feature functional)
            (orthogonalState : GraphHilbertAmbient feature functional)).symm

end

end SourceGeneratedFunctionalGraphCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
