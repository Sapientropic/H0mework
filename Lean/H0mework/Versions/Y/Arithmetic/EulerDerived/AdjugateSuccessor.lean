import H0mework.Realization.MappingCone.AdjugateShearNaturality
import H0mework.Versions.Y.Arithmetic.EulerDerived.AdjugateTotalFiber

/-!
# Actual successor of the whole adjugate total fibre

The block determinant and adjugate both acquire the same relative factor at
the next exact runtime stage.  These actual identities instantiate the
generic shear successor, whose second coordinate remains the literal whole-
complex restriction.  No relative factor is inverted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberSuccessor

open CategoryTheory
open CategoryTheory.Limits
open CochainMappingCoconeDeterminantAdjugateInclusion
open CochainMappingCoconeDeterminantAdjugateTotalFiber
open CochainMappingCoconeDeterminantAdjugateTotalFiberShearNaturality
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugate
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier

noncomputable section

def zeroBlockEvaluation : BlockCoordinateRing →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) fun _index ↦ 0

@[simp] theorem zeroBlockEvaluation_blockA (prime : Nat.Primes) :
    zeroBlockEvaluation (blockA prime) = 0 := by
  simp [zeroBlockEvaluation, blockA]

@[simp] theorem zeroBlockEvaluation_blockB (prime : Nat.Primes) :
    zeroBlockEvaluation (blockB prime) = 0 := by
  simp [zeroBlockEvaluation, blockB]

@[simp] theorem zeroBlockEvaluation_localFactor
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    zeroBlockEvaluation
        (blockLocalFactor seedOccurrence.root stage primeIndex) = 1 := by
  simp [blockLocalFactor]

theorem blockLocalFactor_ne_zero
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    blockLocalFactor seedOccurrence.root stage primeIndex ≠ 0 := by
  intro equality
  have evaluated := congrArg zeroBlockEvaluation equality
  simp at evaluated

theorem blockAdjugateOtherFactorProduct_lift
    (stage : Nat) (primeIndex : StagePrime seedOccurrence.root stage) :
    blockAdjugateOtherFactorProduct (stage + 1)
        (liftBlockPrime seedOccurrence.root stage primeIndex) =
      relativeBlockDeterminantSection seedOccurrence.root stage *
        blockAdjugateOtherFactorProduct stage primeIndex := by
  apply mul_left_cancel₀ (blockLocalFactor_ne_zero stage primeIndex)
  calc
    blockLocalFactor seedOccurrence.root stage primeIndex *
        blockAdjugateOtherFactorProduct (stage + 1)
          (liftBlockPrime seedOccurrence.root stage primeIndex) =
      blockLocalFactor seedOccurrence.root (stage + 1)
          (liftBlockPrime seedOccurrence.root stage primeIndex) *
        blockAdjugateOtherFactorProduct (stage + 1)
          (liftBlockPrime seedOccurrence.root stage primeIndex) := by
            rw [blockLocalFactor_lift]
    _ = blockDeterminantSection seedOccurrence.root (stage + 1) :=
      blockLocalFactor_mul_adjugateOtherFactorProduct _ _
    _ = relativeBlockDeterminantSection seedOccurrence.root stage *
        blockDeterminantSection seedOccurrence.root stage :=
      blockDeterminantSection_successor_factorization _ _
    _ = relativeBlockDeterminantSection seedOccurrence.root stage *
        (blockLocalFactor seedOccurrence.root stage primeIndex *
          blockAdjugateOtherFactorProduct stage primeIndex) := by
            rw [blockLocalFactor_mul_adjugateOtherFactorProduct]
    _ = blockLocalFactor seedOccurrence.root stage primeIndex *
        (relativeBlockDeterminantSection seedOccurrence.root stage *
          blockAdjugateOtherFactorProduct stage primeIndex) := by
            ring

theorem blockInnerAdjugate_restriction_twisted (stage : Nat) :
    (blockInnerRestriction seedOccurrence.root stage).comp
        (blockInnerAdjugate (stage + 1)) =
      relativeBlockDeterminantSection seedOccurrence.root stage •
        ((blockInnerAdjugate stage).comp
          (blockInnerRestriction seedOccurrence.root stage)) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  have productLift :
      blockAdjugateOtherFactorProduct (stage + 1)
          (liftPrime seedOccurrence.root stage primeIndex) =
        relativeBlockDeterminantSection seedOccurrence.root stage *
          blockAdjugateOtherFactorProduct stage primeIndex := by
    exact blockAdjugateOtherFactorProduct_lift stage primeIndex
  fin_cases dualIndex <;>
    simp [blockInnerRestriction, blockInnerAdjugate,
      liftPrime_actualPrime] <;>
    rw [productLift] <;>
    ring

theorem blockWholeVertexAdjugate_restriction_twisted (stage : Nat) :
    (blockWholeVertexRestriction seedOccurrence.root stage).comp
        (blockWholeVertexAdjugate (stage + 1)) =
      relativeBlockDeterminantSection seedOccurrence.root stage •
        ((blockWholeVertexAdjugate stage).comp
          (blockWholeVertexRestriction seedOccurrence.root stage)) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (blockInnerAdjugate_restriction_twisted stage) (value none)
  | some row =>
      exact LinearMap.congr_fun
        (blockInnerAdjugate_restriction_twisted stage)
          (value (some (liftFactorRow seedOccurrence.root stage row)))

theorem blockWholeRelationAdjugate_restriction_twisted (stage : Nat) :
    (blockWholeRelationRestriction seedOccurrence.root stage).comp
        (blockWholeRelationAdjugate (stage + 1)) =
      relativeBlockDeterminantSection seedOccurrence.root stage •
        ((blockWholeRelationAdjugate stage).comp
          (blockWholeRelationRestriction seedOccurrence.root stage)) := by
  apply LinearMap.ext
  intro value
  funext row
  exact LinearMap.congr_fun
    (blockInnerAdjugate_restriction_twisted stage)
      (value (liftFactorRow seedOccurrence.root stage row))

noncomputable def blockDirectRelativeMultiplication (stage : Nat) :
    LocalWholeComplex stage ⟶ LocalWholeComplex stage :=
  relativeBlockDeterminantSection seedOccurrence.root stage •
    𝟙 (LocalWholeComplex stage)

theorem blockDirectRelativeMultiplication_commutes_operator (stage : Nat) :
    blockDirectRelativeMultiplication stage ≫ blockDirectEulerOperator stage =
      blockDirectEulerOperator stage ≫
        blockDirectRelativeMultiplication stage := by
  simp [blockDirectRelativeMultiplication]

theorem blockDirectAdjugate_restriction_twisted (stage : Nat) :
    blockDirectAdjugate (stage + 1) ≫
        blockDirectRestriction seedOccurrence.root stage =
      blockDirectRestriction seedOccurrence.root stage ≫
        blockDirectAdjugate stage ≫
          blockDirectRelativeMultiplication stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeVertexRestriction seedOccurrence.root stage
        (blockWholeVertexAdjugate (stage + 1) value) =
      relativeBlockDeterminantSection seedOccurrence.root stage •
        blockWholeVertexAdjugate stage
          (blockWholeVertexRestriction seedOccurrence.root stage value)
    have twisted := LinearMap.congr_fun
      (blockWholeVertexAdjugate_restriction_twisted stage) value
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using twisted
  · by_cases degreeOne : degree = 1
    · subst degree
      change blockWholeRelationRestriction seedOccurrence.root stage
          (blockWholeRelationAdjugate (stage + 1) value) =
        relativeBlockDeterminantSection seedOccurrence.root stage •
          blockWholeRelationAdjugate stage
            (blockWholeRelationRestriction seedOccurrence.root stage value)
      have twisted := LinearMap.congr_fun
        (blockWholeRelationAdjugate_restriction_twisted stage) value
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using twisted
    · let targetSubsingleton : Subsingleton
          ((LocalWholeComplex stage).X degree) := by
        change Subsingleton (BlockDirectObject seedOccurrence.root stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact Subsingleton.elim _ _

theorem blockDirectEulerOperator_restriction (stage : Nat) :
    blockDirectEulerOperator (stage + 1) ≫
        blockDirectRestriction seedOccurrence.root stage =
      blockDirectRestriction seedOccurrence.root stage ≫
        blockDirectEulerOperator stage := by
  unfold blockDirectEulerOperator
  rw [Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id,
    blockDirectRestriction_action_square]

theorem blockDirectDeterminant_restriction_twisted (stage : Nat) :
    blockDirectDeterminantMultiplication (stage + 1) ≫
        blockDirectRestriction seedOccurrence.root stage =
      blockDirectRestriction seedOccurrence.root stage ≫
        blockDirectDeterminantMultiplication stage ≫
          blockDirectRelativeMultiplication stage := by
  ext degree value
  by_cases degreeZero : degree = 0
  · subst degree
    change blockWholeVertexRestriction seedOccurrence.root stage
        (blockDeterminantSection seedOccurrence.root (stage + 1) • value) = _
    rw [map_smul, blockDeterminantSection_successor_factorization]
    change
      (relativeBlockDeterminantSection seedOccurrence.root stage *
          blockDeterminantSection seedOccurrence.root stage) •
            blockWholeVertexRestriction seedOccurrence.root stage value =
        relativeBlockDeterminantSection seedOccurrence.root stage •
          (blockDeterminantSection seedOccurrence.root stage •
            blockWholeVertexRestriction seedOccurrence.root stage value)
    exact mul_smul _ _ _
  · by_cases degreeOne : degree = 1
    · subst degree
      change blockWholeRelationRestriction seedOccurrence.root stage
          (blockDeterminantSection seedOccurrence.root (stage + 1) • value) = _
      rw [map_smul, blockDeterminantSection_successor_factorization]
      change
        (relativeBlockDeterminantSection seedOccurrence.root stage *
            blockDeterminantSection seedOccurrence.root stage) •
              blockWholeRelationRestriction seedOccurrence.root stage value =
          relativeBlockDeterminantSection seedOccurrence.root stage •
            (blockDeterminantSection seedOccurrence.root stage •
              blockWholeRelationRestriction seedOccurrence.root stage value)
      exact mul_smul _ _ _
    · let targetSubsingleton : Subsingleton
          ((LocalWholeComplex stage).X degree) := by
        change Subsingleton (BlockDirectObject seedOccurrence.root stage degree)
        simp [BlockDirectObject, degreeZero, degreeOne]
        exact ⟨fun left right => funext fun index => Fin.elim0 index⟩
      exact Subsingleton.elim _ _

theorem localTotalFiberShearSuccessor (stage : Nat) :
    TotalFiberShearSuccessorAt
      (localAdjugateSquare (stage + 1)) (localAdjugateSquare stage)
      (blockDirectRestriction seedOccurrence.root stage)
      (blockDirectRelativeMultiplication stage) where
  operatorSquare := blockDirectEulerOperator_restriction stage
  determinantSquare := blockDirectDeterminant_restriction_twisted stage
  adjugateSquare := blockDirectAdjugate_restriction_twisted stage
  relativeOperatorCommutes :=
    blockDirectRelativeMultiplication_commutes_operator stage

noncomputable def localTotalFiberRestriction (stage : Nat) :
    LocalTotalFiber (stage + 1) ⟶ LocalTotalFiber stage :=
  (localTotalFiberShearSuccessor stage).totalTransition

theorem localTotalInclusion_successor (stage : Nat) :
    localTotalInclusion (stage + 1) ≫ localTotalFiberRestriction stage =
      blockDirectRestriction seedOccurrence.root stage ≫
        localTotalInclusion stage :=
  (localTotalFiberShearSuccessor stage).totalInclusion_naturality

theorem localTotalFiberRestriction_preserves_raw_endpoint (stage : Nat) :
    (localTotalFiberShearSuccessor stage).pairTransition ≫
        (biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
          LocalWholeComplex stage) =
      (biprod.snd : LocalWholeComplex (stage + 1) ⊞
          LocalWholeComplex (stage + 1) ⟶ LocalWholeComplex (stage + 1)) ≫
        blockDirectRestriction seedOccurrence.root stage :=
  (localTotalFiberShearSuccessor stage).pairTransition_second

theorem preserves_actual_shear_successor_and_raw_endpoint (stage : Nat) :
    localTotalInclusion (stage + 1) ≫ localTotalFiberRestriction stage =
        blockDirectRestriction seedOccurrence.root stage ≫
          localTotalInclusion stage ∧
      (localTotalFiberShearSuccessor stage).pairTransition ≫
          (biprod.snd : LocalWholeComplex stage ⊞ LocalWholeComplex stage ⟶
            LocalWholeComplex stage) =
        (biprod.snd : LocalWholeComplex (stage + 1) ⊞
            LocalWholeComplex (stage + 1) ⟶ LocalWholeComplex (stage + 1)) ≫
          blockDirectRestriction seedOccurrence.root stage :=
  ⟨localTotalInclusion_successor stage,
    localTotalFiberRestriction_preserves_raw_endpoint stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberSuccessor
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
