import H0mework.Versions.X.Arithmetic.EulerGlobal.DeterminantSuccessor
import H0mework.Realization.Completion.PolynomialSection

/-!
# Framework-generated global full-Euler determinant section

One exact factorization seed supplies the local full-Euler action and one
support-expanding successor factorization.  The generic cofinal polynomial
section kernel generates the rooted history and the global pro-section `D`.
Zero-fibre formation is intentionally absent from this file and can only
consume this generated section diagram downstream.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerDeterminantSuccessor
open CofinalPolynomialSection
open CofinalPolynomialSection.RootGeneratedCofinalPolynomialSectionAt

noncomputable section

def determinantSectionProcess (seed : FactorizationPayload) :
    PolynomialSectionSuccessorProcessAt ℤ where
  State := Nat
  seed := 0
  next := Nat.succ
  polynomialAt stage := determinantPolynomial seed stage
  relativeFactor stage := relativeKernelDeterminantPolynomial seed stage
  factorization stage :=
    determinantPolynomial_successor_factorization seed stage

def dependentProcessOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × PolynomialSectionSuccessorProcessAt ℤ) :=
  seedOccurrence.map fun seed => (seed, determinantSectionProcess seed)

theorem dependentProcessOccurrence_projects :
    dependentProcessOccurrence.map Prod.fst = seedOccurrence := by
  unfold dependentProcessOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

def globalSectionFace : RootGeneratedCofinalPolynomialSectionAt
    seedOccurrence dependentProcessOccurrence
      dependentProcessOccurrence_projects :=
  RootGeneratedCofinalPolynomialSectionAt.generate

/-- The global determinant section authority.  It is generated before any
zero-fibre coordinate ring. -/
abbrev GlobalDeterminantSectionDiagram :=
  globalSectionFace.globalSectionDiagram

@[simp] theorem globalSectionFace_stateAt (stage : Nat) :
    globalSectionFace.stateAt stage = stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      change Nat.succ (globalSectionFace.stateAt stage) = Nat.succ stage
      rw [inductionHypothesis]

theorem generated_stage_mem_section_history (stage : Nat) :
    globalSectionFace.stateAt stage ∈
      (globalSectionFace.cofinalFace.observation stage).trace :=
  globalSectionFace.stateAt_mem_observation_trace stage

theorem globalSection_local_restriction (stage : Nat) :
    (GlobalDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial =
        determinantPolynomial seedOccurrence.root stage := by
  change determinantPolynomial seedOccurrence.root
      (globalSectionFace.stateAt stage) = _
  rw [globalSectionFace_stateAt]

theorem generated_successor_factorization (stage : Nat) :
    determinantPolynomial seedOccurrence.root (stage + 1) =
      relativeKernelDeterminantPolynomial seedOccurrence.root stage *
        determinantPolynomial seedOccurrence.root stage :=
  determinantPolynomial_successor_factorization seedOccurrence.root stage

theorem preserves_exact_seed_action_successor_and_global_D :
    globalSectionFace.cofinalFace.root = seedOccurrence ∧
      globalSectionFace.actualProcess =
        determinantSectionProcess seedOccurrence.root ∧
      GlobalDeterminantSectionDiagram =
        (determinantSectionProcess seedOccurrence.root).toCofinalProcess.diagram := by
  refine ⟨globalSectionFace.preserves_root_local_successor_and_global_section.1,
    ?_, globalSectionFace.preserves_root_local_successor_and_global_section.2.2⟩
  rfl

end
end CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
