import H0mework.Arithmetic.EulerDerived.DeterminantSection
import H0mework.Arithmetic.EulerDualBlock.WholeRelationDeterminant
import H0mework.Realization.Completion.PolynomialSection

/-!
# Framework-generated global prime-dual block determinant section

One source-owned block determinant seed and its actual successor
factorization are submitted to the frozen cofinal polynomial-section engine.
The engine generates the whole history and global pro-section.  The local
readback remains the determinant carried by the same full-complex action
occurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeRelationDeterminant
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalDeterminantSection
open CofinalPolynomialSection
open CofinalPolynomialSection.RootGeneratedCofinalPolynomialSectionAt

noncomputable section

def blockDeterminantSectionProcess (seed : FactorizationPayload) :
    PolynomialSectionSuccessorProcessAt BlockCoordinateRing where
  State := Nat
  seed := 0
  next := Nat.succ
  polynomialAt stage := Polynomial.C (blockDeterminantSection seed stage)
  relativeFactor stage :=
    Polynomial.C (relativeBlockDeterminantSection seed stage)
  factorization stage := by
    rw [blockDeterminantSection_successor_factorization, map_mul]

def dependentBlockProcessOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      PolynomialSectionSuccessorProcessAt BlockCoordinateRing) :=
  seedOccurrence.map fun seed => (seed, blockDeterminantSectionProcess seed)

theorem dependentBlockProcessOccurrence_projects :
    dependentBlockProcessOccurrence.map Prod.fst = seedOccurrence := by
  unfold dependentBlockProcessOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

def globalBlockSectionFace : RootGeneratedCofinalPolynomialSectionAt
    seedOccurrence dependentBlockProcessOccurrence
      dependentBlockProcessOccurrence_projects :=
  RootGeneratedCofinalPolynomialSectionAt.generate

abbrev GlobalBlockDeterminantSectionDiagram :=
  globalBlockSectionFace.globalSectionDiagram

@[simp] theorem globalBlockSectionFace_stateAt (stage : Nat) :
    globalBlockSectionFace.stateAt stage = stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      change Nat.succ (globalBlockSectionFace.stateAt stage) = Nat.succ stage
      rw [inductionHypothesis]

theorem generated_stage_mem_block_section_history (stage : Nat) :
    globalBlockSectionFace.stateAt stage ∈
      (globalBlockSectionFace.cofinalFace.observation stage).trace :=
  globalBlockSectionFace.stateAt_mem_observation_trace stage

theorem globalBlockSection_local_restriction (stage : Nat) :
    (GlobalBlockDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial =
        Polynomial.C (blockDeterminantSection seedOccurrence.root stage) := by
  change Polynomial.C (blockDeterminantSection seedOccurrence.root
      (globalBlockSectionFace.stateAt stage)) = _
  rw [globalBlockSectionFace_stateAt]

theorem globalBlockSection_reads_same_action_occurrence (stage : Nat) :
    (GlobalBlockDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial =
        Polynomial.C
          (blockDeterminantOccurrence seedOccurrence.root stage).root.2.2 := by
  rw [globalBlockSection_local_restriction,
    blockDeterminantOccurrence_reads_section]

/-- The global section is the literal cancelled factor of the canonical
whole vertex/relation alternating determinant on the same stage occurrence. -/
theorem globalBlockSection_reads_whole_determinant_occurrence (stage : Nat) :
    (GlobalBlockDeterminantSectionDiagram.obj
        (Opposite.op stage)).polynomial =
        Polynomial.C (blockDeterminantSection seedOccurrence.root stage) ∧
      (blockWholeDeterminantOccurrence
          seedOccurrence.root stage).map Prod.fst =
        stageOccurrenceFrom seedOccurrence.root stage ∧
      (blockWholeDeterminantOccurrence
          seedOccurrence.root stage).root.2.2.numerator =
        blockDeterminantSection seedOccurrence.root stage *
          (blockWholeDeterminantOccurrence
            seedOccurrence.root stage).root.2.2.denominator := by
  exact ⟨globalBlockSection_local_restriction stage,
    blockWholeDeterminantOccurrence_projects_source _ _,
    blockWholeDeterminantOccurrence_cancels_to_inner _ _⟩

theorem collapse_globalBlockSection_reads_existing_whole_D (stage : Nat) :
    Polynomial.map collapseBlockCoordinate
        (GlobalBlockDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial =
      Polynomial.C
        (CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection.GlobalDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial := by
  rw [globalBlockSection_local_restriction, Polynomial.map_C,
    collapse_blockDeterminantSection_eq_existing_D,
    globalD_local_restriction_reads_relation_action,
    innerDeterminantPolynomial_eq_existing]

theorem generated_block_successor_factorization (stage : Nat) :
    blockDeterminantSection seedOccurrence.root (stage + 1) =
      relativeBlockDeterminantSection seedOccurrence.root stage *
        blockDeterminantSection seedOccurrence.root stage :=
  blockDeterminantSection_successor_factorization seedOccurrence.root stage

theorem preserves_exact_seed_block_action_successor_and_global_section :
    globalBlockSectionFace.cofinalFace.root = seedOccurrence ∧
      globalBlockSectionFace.actualProcess =
        blockDeterminantSectionProcess seedOccurrence.root ∧
      GlobalBlockDeterminantSectionDiagram =
        (blockDeterminantSectionProcess
          seedOccurrence.root).toCofinalProcess.diagram := by
  refine ⟨
    globalBlockSectionFace.preserves_root_local_successor_and_global_section.1,
    ?_,
    globalBlockSectionFace.preserves_root_local_successor_and_global_section.2.2⟩
  rfl

theorem preserves_exact_seed_whole_action_cancellation_and_global_section :
    globalBlockSectionFace.cofinalFace.root = seedOccurrence ∧
      (∀ stage : Nat,
        (blockWholeDeterminantOccurrence
            seedOccurrence.root stage).map Prod.fst =
          stageOccurrenceFrom seedOccurrence.root stage) ∧
      (∀ stage : Nat,
        (blockWholeDeterminantOccurrence
            seedOccurrence.root stage).root.2.2.numerator =
          blockDeterminantSection seedOccurrence.root stage *
            (blockWholeDeterminantOccurrence
              seedOccurrence.root stage).root.2.2.denominator) ∧
      (∀ stage : Nat,
        (GlobalBlockDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial =
            Polynomial.C
              (blockDeterminantSection seedOccurrence.root stage)) := by
  exact ⟨globalBlockSectionFace
      |>.preserves_root_local_successor_and_global_section |>.1,
    fun stage => blockWholeDeterminantOccurrence_projects_source _ _,
    fun stage => blockWholeDeterminantOccurrence_cancels_to_inner _ _,
    globalBlockSection_local_restriction⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
