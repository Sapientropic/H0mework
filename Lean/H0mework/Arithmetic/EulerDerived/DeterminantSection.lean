import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import H0mework.Arithmetic.EulerDualBlock.Frame
import H0mework.Arithmetic.EulerGlobal.WholeGlobalSection

/-!
# Determinant section of the full prime-dual block frame

The canonical determinant is taken from the actual block action already
installed on the complete whole/relation complex.  Its source successor is
preserved before collapse, and the canonical collapse `A_p ↦ pX`, `B_p ↦ 0`
reads the existing whole-action section `D`.  An independent coordinate pair
evaluates the same common frame into its two local Euler eigenfactors.

No zero, fixedness, endpoint law, or analytic continuation enters this
producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerDeterminantSuccessor
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalDeterminantSection
open Polynomial

noncomputable section

variable (seed : FactorizationPayload) (stage : Nat)

def blockEulerOperator :
    BlockInner seed stage →ₗ[BlockCoordinateRing] BlockInner seed stage :=
  LinearMap.id - blockInnerAction seed stage

def primeBlockOperatorMatrix (primeIndex : StagePrime seed stage) :
    Matrix (Fin 2) (Fin 2) BlockCoordinateRing :=
  fun row column =>
    if row = column then
      1 - blockA ((stageFactorization seed stage).actualPrime primeIndex)
    else
      -blockB ((stageFactorization seed stage).actualPrime primeIndex)

def blockIndexEquiv :
    (Fin 2 × StagePrime seed stage) ≃ BaseIndex seed stage :=
  Equiv.prodComm (Fin 2) (StagePrime seed stage)

def blockOperatorMatrix :
    Matrix (BaseIndex seed stage) (BaseIndex seed stage) BlockCoordinateRing :=
  Matrix.reindex (blockIndexEquiv seed stage) (blockIndexEquiv seed stage)
    (Matrix.blockDiagonal (primeBlockOperatorMatrix seed stage))

theorem blockEulerOperator_toMatrix :
    LinearMap.toMatrix
        (Pi.basisFun BlockCoordinateRing (BaseIndex seed stage))
        (Pi.basisFun BlockCoordinateRing (BaseIndex seed stage))
        (blockEulerOperator seed stage) =
      blockOperatorMatrix seed stage := by
  apply Matrix.ext
  intro row column
  rcases row with ⟨rowPrime, rowDual⟩
  rcases column with ⟨columnPrime, columnDual⟩
  by_cases samePrime : rowPrime = columnPrime
  · subst columnPrime
    by_cases sameDual : rowDual = columnDual
    · subst columnDual
      have reversedNe : rowDual.rev ≠ rowDual := by
        fin_cases rowDual <;> decide
      simp [blockEulerOperator, blockInnerAction, blockOperatorMatrix,
        blockIndexEquiv, primeBlockOperatorMatrix, reversedNe]
    · have reversed : rowDual.rev = columnDual := by
        fin_cases rowDual <;> fin_cases columnDual <;> simp_all
      simp [blockEulerOperator, blockInnerAction, blockOperatorMatrix,
        blockIndexEquiv, primeBlockOperatorMatrix, sameDual, reversed]
  · have rowNeColumn :
        (rowPrime, rowDual) ≠ (columnPrime, columnDual) := by
      intro equality
      exact samePrime (congrArg Prod.fst equality)
    have reversedNe :
        (rowPrime, rowDual.rev) ≠ (columnPrime, columnDual) := by
      intro equality
      exact samePrime (congrArg Prod.fst equality)
    simp [blockEulerOperator, blockInnerAction, blockOperatorMatrix,
      blockIndexEquiv, Matrix.blockDiagonal_apply, rowNeColumn, reversedNe,
      samePrime]

theorem primeBlockOperatorMatrix_det
    (primeIndex : StagePrime seed stage) :
    (primeBlockOperatorMatrix seed stage primeIndex).det =
      (1 - blockA
          ((stageFactorization seed stage).actualPrime primeIndex)) ^ 2 -
        blockB ((stageFactorization seed stage).actualPrime primeIndex) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [primeBlockOperatorMatrix]
  ring

noncomputable def blockDeterminantSection : BlockCoordinateRing :=
  LinearMap.det (blockEulerOperator seed stage)

theorem blockDeterminantSection_eq_actual_product :
    blockDeterminantSection seed stage =
      ∏ primeIndex : StagePrime seed stage,
        ((1 - blockA
            ((stageFactorization seed stage).actualPrime primeIndex)) ^ 2 -
          blockB
            ((stageFactorization seed stage).actualPrime primeIndex) ^ 2) := by
  rw [blockDeterminantSection,
    ← LinearMap.det_toMatrix
      (Pi.basisFun BlockCoordinateRing (BaseIndex seed stage)),
    blockEulerOperator_toMatrix, blockOperatorMatrix,
    Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  apply Finset.prod_congr rfl
  intro primeIndex _membership
  exact primeBlockOperatorMatrix_det seed stage primeIndex

def collapseBlockCoordinate : BlockCoordinateRing →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C fun index =>
    if index.2 = 0 then
      Polynomial.C (index.1 : ℤ) * Polynomial.X
    else 0

@[simp] theorem collapseBlockCoordinate_A (prime : Nat.Primes) :
    collapseBlockCoordinate (blockA prime) =
      Polynomial.C (prime : ℤ) * Polynomial.X := by
  simp [collapseBlockCoordinate, blockA]

@[simp] theorem collapseBlockCoordinate_B (prime : Nat.Primes) :
    collapseBlockCoordinate (blockB prime) = 0 := by
  simp [collapseBlockCoordinate, blockB]

theorem collapse_primeBlockFactor
    (primeIndex : StagePrime seed stage) :
    collapseBlockCoordinate
        ((1 - blockA
            ((stageFactorization seed stage).actualPrime primeIndex)) ^ 2 -
          blockB
            ((stageFactorization seed stage).actualPrime primeIndex) ^ 2) =
      (1 - Polynomial.C (actualPrimeScalar seed stage primeIndex) *
          Polynomial.X) ^ 2 := by
  rw [map_sub, map_pow, map_sub, map_one,
    collapseBlockCoordinate_A, map_pow, collapseBlockCoordinate_B]
  simp [actualPrimeScalar]

theorem collapse_blockDeterminantSection_eq_existing_D :
    collapseBlockCoordinate (blockDeterminantSection seed stage) =
      determinantPolynomial seed stage := by
  rw [blockDeterminantSection_eq_actual_product, map_prod,
    determinantPolynomial_eq_actual_product, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro primeIndex _membership
  rw [collapse_primeBlockFactor, Fin.prod_univ_two]
  change
    (1 - Polynomial.C (actualPrimeScalar seed stage primeIndex) *
        Polynomial.X) ^ 2 =
      localEulerDeterminantFactor seed stage (primeIndex, 0) *
        localEulerDeterminantFactor seed stage (primeIndex, 1)
  unfold localEulerDeterminantFactor
  ring

theorem collapse_blockDeterminantSection_reads_whole_D :
    collapseBlockCoordinate (blockDeterminantSection seed stage) =
      innerEulerDeterminantPolynomial seed stage := by
  rw [collapse_blockDeterminantSection_eq_existing_D,
    innerDeterminantPolynomial_eq_existing]

/-! ## Source successor in the common block frame -/

def blockLocalFactor (primeIndex : StagePrime seed stage) :
    BlockCoordinateRing :=
  (1 - blockA ((stageFactorization seed stage).actualPrime primeIndex)) ^ 2 -
    blockB ((stageFactorization seed stage).actualPrime primeIndex) ^ 2

def liftBlockPrime : StagePrime seed stage → StagePrime seed (stage + 1) :=
  liftPrime seed stage

theorem liftBlockPrime_injective :
    Function.Injective (liftBlockPrime seed stage) :=
  liftPrime_injective seed stage

def inheritedBlockPrimeSupport : Finset (StagePrime seed (stage + 1)) :=
  (Finset.univ : Finset (StagePrime seed stage)).image
    (liftBlockPrime seed stage)

def relativeBlockDeterminantSection : BlockCoordinateRing :=
  ∏ primeIndex ∈
      (Finset.univ : Finset (StagePrime seed (stage + 1))) \
        inheritedBlockPrimeSupport seed stage,
    blockLocalFactor seed (stage + 1) primeIndex

theorem blockLocalFactor_lift (primeIndex : StagePrime seed stage) :
    blockLocalFactor seed (stage + 1) (liftBlockPrime seed stage primeIndex) =
      blockLocalFactor seed stage primeIndex := by
  unfold blockLocalFactor liftBlockPrime
  rw [liftPrime_actualPrime]

theorem inheritedBlockPrimeSupport_product :
    (∏ primeIndex ∈ inheritedBlockPrimeSupport seed stage,
      blockLocalFactor seed (stage + 1) primeIndex) =
        ∏ primeIndex : StagePrime seed stage,
          blockLocalFactor seed stage primeIndex := by
  classical
  rw [inheritedBlockPrimeSupport,
    Finset.prod_image (liftBlockPrime_injective seed stage).injOn]
  apply Finset.prod_congr rfl
  intro primeIndex _membership
  exact blockLocalFactor_lift seed stage primeIndex

theorem blockDeterminantSection_successor_factorization :
    blockDeterminantSection seed (stage + 1) =
      relativeBlockDeterminantSection seed stage *
        blockDeterminantSection seed stage := by
  rw [blockDeterminantSection_eq_actual_product,
    blockDeterminantSection_eq_actual_product]
  have subset : inheritedBlockPrimeSupport seed stage ⊆
      (Finset.univ : Finset (StagePrime seed (stage + 1))) := by
    intro primeIndex _membership
    exact Finset.mem_univ primeIndex
  have split := Finset.prod_sdiff
    (f := blockLocalFactor seed (stage + 1)) subset
  change relativeBlockDeterminantSection seed stage *
      (∏ primeIndex ∈ inheritedBlockPrimeSupport seed stage,
        blockLocalFactor seed (stage + 1) primeIndex) =
    ∏ primeIndex : StagePrime seed (stage + 1),
      blockLocalFactor seed (stage + 1) primeIndex at split
  rw [inheritedBlockPrimeSupport_product] at split
  exact split.symm

theorem collapse_blockDeterminantSection_successor_factorization :
    collapseBlockCoordinate (blockDeterminantSection seed (stage + 1)) =
      relativeKernelDeterminantPolynomial seed stage *
        collapseBlockCoordinate (blockDeterminantSection seed stage) := by
  rw [collapse_blockDeterminantSection_eq_existing_D,
    collapse_blockDeterminantSection_eq_existing_D]
  exact determinantPolynomial_successor_factorization seed stage

/-! ## One independent two-coordinate installed frame -/

abbrev CoordinatePair := ℂ × ℂ
abbrev InstalledPairFunctionRing := CoordinatePair → ℂ

def intToPairFunctions : ℤ →+* InstalledPairFunctionRing :=
  RingHom.pi fun _pair => Int.castRingHom ℂ

def installedPrimeEigenvalue (prime : Nat.Primes) (coordinate : ℂ) : ℂ :=
  ((prime : Nat) : ℂ) ^ (-coordinate)

def installedPairAverage (prime : Nat.Primes) (pair : CoordinatePair) : ℂ :=
  (installedPrimeEigenvalue prime pair.1 +
      installedPrimeEigenvalue prime pair.2) / 2

def installedPairDifference (prime : Nat.Primes) (pair : CoordinatePair) : ℂ :=
  (installedPrimeEigenvalue prime pair.1 -
      installedPrimeEigenvalue prime pair.2) / 2

def installedBlockVariable (index : BlockVariable) :
    InstalledPairFunctionRing := fun pair =>
  match index.2 with
  | 0 => installedPairAverage index.1 pair
  | 1 => installedPairDifference index.1 pair

def installedBlockEvaluation :
    BlockCoordinateRing →+* InstalledPairFunctionRing :=
  MvPolynomial.eval₂Hom intToPairFunctions installedBlockVariable

@[simp] theorem installedBlockEvaluation_A
    (prime : Nat.Primes) (pair : CoordinatePair) :
    installedBlockEvaluation (blockA prime) pair =
      installedPairAverage prime pair := by
  simp [installedBlockEvaluation, blockA, installedBlockVariable]

@[simp] theorem installedBlockEvaluation_B
    (prime : Nat.Primes) (pair : CoordinatePair) :
    installedBlockEvaluation (blockB prime) pair =
      installedPairDifference prime pair := by
  simp [installedBlockEvaluation, blockB, installedBlockVariable]

theorem installedBlockEvaluation_localFactor
    (primeIndex : StagePrime seed stage) (pair : CoordinatePair) :
    installedBlockEvaluation (blockLocalFactor seed stage primeIndex) pair =
      (1 - installedPrimeEigenvalue
          ((stageFactorization seed stage).actualPrime primeIndex) pair.1) *
        (1 - installedPrimeEigenvalue
          ((stageFactorization seed stage).actualPrime primeIndex) pair.2) := by
  unfold blockLocalFactor
  rw [map_sub, map_pow, map_sub, map_one, map_pow]
  change
    (1 - installedBlockEvaluation
        (blockA ((stageFactorization seed stage).actualPrime primeIndex)) pair) ^ 2 -
      installedBlockEvaluation
        (blockB ((stageFactorization seed stage).actualPrime primeIndex)) pair ^ 2 = _
  rw [installedBlockEvaluation_A, installedBlockEvaluation_B]
  unfold installedPairAverage installedPairDifference
  ring

theorem installedBlockEvaluation_section (pair : CoordinatePair) :
    installedBlockEvaluation (blockDeterminantSection seed stage) pair =
      ∏ primeIndex : StagePrime seed stage,
        ((1 - installedPrimeEigenvalue
            ((stageFactorization seed stage).actualPrime primeIndex) pair.1) *
          (1 - installedPrimeEigenvalue
            ((stageFactorization seed stage).actualPrime primeIndex) pair.2)) := by
  rw [blockDeterminantSection_eq_actual_product, map_prod]
  simp only [Fintype.prod_apply]
  apply Finset.prod_congr rfl
  intro primeIndex _membership
  exact installedBlockEvaluation_localFactor seed stage primeIndex pair

def coordinatePairSwap (pair : CoordinatePair) : CoordinatePair :=
  (pair.2, pair.1)

@[simp] theorem coordinatePairSwap_involutive (pair : CoordinatePair) :
    coordinatePairSwap (coordinatePairSwap pair) = pair :=
  rfl

@[simp] theorem installedPairAverage_swap
    (prime : Nat.Primes) (pair : CoordinatePair) :
    installedPairAverage prime (coordinatePairSwap pair) =
      installedPairAverage prime pair := by
  unfold installedPairAverage coordinatePairSwap
  ring

@[simp] theorem installedPairDifference_swap
    (prime : Nat.Primes) (pair : CoordinatePair) :
    installedPairDifference prime (coordinatePairSwap pair) =
      -installedPairDifference prime pair := by
  unfold installedPairDifference coordinatePairSwap
  ring

def installedBlockEvaluationAt (pair : CoordinatePair) :
    BlockCoordinateRing →+* ℂ :=
  (Pi.evalRingHom (fun _ : CoordinatePair => ℂ) pair).comp
    installedBlockEvaluation

theorem installedBlockEvaluation_section_swap (pair : CoordinatePair) :
    installedBlockEvaluation (blockDeterminantSection seed stage)
        (coordinatePairSwap pair) =
      installedBlockEvaluation (blockDeterminantSection seed stage) pair := by
  rw [installedBlockEvaluation_section, installedBlockEvaluation_section]
  apply Finset.prod_congr rfl
  intro primeIndex _membership
  simp only [coordinatePairSwap]
  ring

/-! ## Exact dependent occurrence and readback -/

def blockDeterminantOccurrence :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        ((BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
            BlockWholeVertex seed stage) × BlockCoordinateRing)) :=
  (blockWholeActionOccurrence seed stage).map fun readout =>
    (readout.1, (readout.2, blockDeterminantSection seed stage))

theorem blockDeterminantOccurrence_projects_action :
    (blockDeterminantOccurrence seed stage).map
        (fun readout => (readout.1, readout.2.1)) =
      blockWholeActionOccurrence seed stage := by
  unfold blockDeterminantOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (blockWholeActionOccurrence seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem blockDeterminantOccurrence_reads_action :
    (blockDeterminantOccurrence seed stage).root.2.1 =
      blockWholeVertexAction seed stage := by
  simp [blockDeterminantOccurrence, blockWholeActionOccurrence,
    stageOccurrenceFrom]

theorem blockDeterminantOccurrence_reads_section :
    (blockDeterminantOccurrence seed stage).root.2.2 =
      blockDeterminantSection seed stage := by
  simp [blockDeterminantOccurrence, blockWholeActionOccurrence,
    stageOccurrenceFrom]

theorem blockDeterminantOccurrence_projects_source :
    (blockDeterminantOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold blockDeterminantOccurrence blockWholeActionOccurrence
  rw [RootedAccountedUnfolding.map_map,
    RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem generated_block_determinant_summary :
    (blockDeterminantOccurrence seed stage).map Prod.fst =
        stageOccurrenceFrom seed stage ∧
      (blockDeterminantOccurrence seed stage).root.2.1 =
        blockWholeVertexAction seed stage ∧
      (blockDeterminantOccurrence seed stage).root.2.2 =
        blockDeterminantSection seed stage ∧
      collapseBlockCoordinate (blockDeterminantSection seed stage) =
        innerEulerDeterminantPolynomial seed stage ∧
      blockDeterminantSection seed (stage + 1) =
        relativeBlockDeterminantSection seed stage *
          blockDeterminantSection seed stage := by
  exact ⟨blockDeterminantOccurrence_projects_source seed stage,
    blockDeterminantOccurrence_reads_action seed stage,
    blockDeterminantOccurrence_reads_section seed stage,
    collapse_blockDeterminantSection_reads_whole_D seed stage,
    blockDeterminantSection_successor_factorization seed stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
