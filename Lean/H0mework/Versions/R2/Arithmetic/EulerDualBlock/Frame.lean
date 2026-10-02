import Mathlib.Algebra.MvPolynomial.Basic
import H0mework.Versions.R2.Arithmetic.EulerGlobal.WholeRelationAction

/-!
# Prime-dual block frame on the full Euler whole-relation complex

For each actual prime, the two dual coordinates carry the single block

`[[A_p, B_p], [B_p, A_p]]`.

The block commutes with the source dual swap.  Hence it acts on the complete
whole/relation carrier, preserves the actual anti-invariant factorization
differential, commutes with the sign reversal on quotient and relation roles,
and is preserved by the runtime successor.  No zero, fixedness, coordinate,
or analytic datum enters this producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier

noncomputable section

abbrev BlockVariable := Nat.Primes × Fin 2
abbrev BlockCoordinateRing := MvPolynomial BlockVariable ℤ

def blockA (prime : Nat.Primes) : BlockCoordinateRing :=
  MvPolynomial.X (prime, 0)

def blockB (prime : Nat.Primes) : BlockCoordinateRing :=
  MvPolynomial.X (prime, 1)

abbrev BlockInner (seed : FactorizationPayload) (stage : Nat) :=
  BaseIndex seed stage → BlockCoordinateRing

def blockInnerAction (seed : FactorizationPayload) (stage : Nat) :
    BlockInner seed stage →ₗ[BlockCoordinateRing] BlockInner seed stage where
  toFun value index :=
    blockA ((stageFactorization seed stage).actualPrime index.1) * value index +
      blockB ((stageFactorization seed stage).actualPrime index.1) *
        value (index.1, index.2.rev)
  map_add' left right := by
    funext index
    simp only [Pi.add_apply]
    ring
  map_smul' scalar value := by
    funext index
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

def blockInnerReversal (seed : FactorizationPayload) (stage : Nat) :
    BlockInner seed stage →ₗ[BlockCoordinateRing] BlockInner seed stage where
  toFun value index := value (index.1, index.2.rev)
  map_add' _left _right := rfl
  map_smul' _scalar _value := rfl

def blockInnerRestriction (seed : FactorizationPayload) (stage : Nat) :
    BlockInner seed (stage + 1) →ₗ[BlockCoordinateRing]
      BlockInner seed stage where
  toFun value index := value (liftPrime seed stage index.1, index.2)
  map_add' _left _right := rfl
  map_smul' _scalar _value := rfl

theorem blockInnerReversal_involutive
    (seed : FactorizationPayload) (stage : Nat) :
    Function.Involutive (blockInnerReversal seed stage) := by
  intro value
  funext index
  simp [blockInnerReversal]

theorem blockInnerAction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerReversal seed stage).comp (blockInnerAction seed stage) =
      (blockInnerAction seed stage).comp (blockInnerReversal seed stage) := by
  apply LinearMap.ext
  intro value
  funext index
  simp [blockInnerReversal, blockInnerAction]

theorem blockInnerRestriction_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerRestriction seed stage).comp
        (blockInnerAction seed (stage + 1)) =
      (blockInnerAction seed stage).comp
        (blockInnerRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext index
  change
    blockA ((stageFactorization seed (stage + 1)).actualPrime
          (liftPrime seed stage index.1)) *
          value (liftPrime seed stage index.1, index.2) +
        blockB ((stageFactorization seed (stage + 1)).actualPrime
          (liftPrime seed stage index.1)) *
          value (liftPrime seed stage index.1, index.2.rev) =
      blockA ((stageFactorization seed stage).actualPrime index.1) *
          value (liftPrime seed stage index.1, index.2) +
        blockB ((stageFactorization seed stage).actualPrime index.1) *
          value (liftPrime seed stage index.1, index.2.rev)
  rw [liftPrime_actualPrime]

theorem blockInnerRestriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerRestriction seed stage).comp
        (blockInnerReversal seed (stage + 1)) =
      (blockInnerReversal seed stage).comp
        (blockInnerRestriction seed stage) := by
  rfl

abbrev BlockWholeVertex (seed : FactorizationPayload) (stage : Nat) :=
  WholeRole seed stage → BlockInner seed stage

abbrev BlockWholeRelation (seed : FactorizationPayload) (stage : Nat) :=
  FactorRow seed stage → BlockInner seed stage

def blockInnerAntiInvariant (seed : FactorizationPayload) (stage : Nat) :
    BlockInner seed stage →ₗ[BlockCoordinateRing] BlockInner seed stage :=
  LinearMap.id - blockInnerReversal seed stage

def blockFactorizationDifferential
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seed stage where
  toFun value row :=
    blockInnerAntiInvariant seed stage (value none) -
      (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) •
        blockInnerAntiInvariant seed stage (value (some row))
  map_add' left right := by
    funext row
    simp only [Pi.add_apply, map_add]
    module
  map_smul' scalar value := by
    funext row
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    module

def blockWholeVertexAction
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
      BlockWholeVertex seed stage where
  toFun value role := blockInnerAction seed stage (value role)
  map_add' left right := by
    funext role
    exact (blockInnerAction seed stage).map_add (left role) (right role)
  map_smul' scalar value := by
    funext role
    change blockInnerAction seed stage (scalar • value role) =
      scalar • blockInnerAction seed stage (value role)
    exact (blockInnerAction seed stage).map_smul scalar (value role)

def blockWholeRelationAction
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeRelation seed stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seed stage where
  toFun value row := blockInnerAction seed stage (value row)
  map_add' left right := by
    funext row
    exact (blockInnerAction seed stage).map_add (left row) (right row)
  map_smul' scalar value := by
    funext row
    change blockInnerAction seed stage (scalar • value row) =
      scalar • blockInnerAction seed stage (value row)
    exact (blockInnerAction seed stage).map_smul scalar (value row)

def blockWholeVertexReversal
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
      BlockWholeVertex seed stage where
  toFun value role :=
    match role with
    | none => blockInnerReversal seed stage (value none)
    | some row => -value (some row)
  map_add' left right := by
    funext role
    cases role with
    | none =>
        exact (blockInnerReversal seed stage).map_add (left none) (right none)
    | some row =>
        change -(left (some row) + right (some row)) =
          -left (some row) + -right (some row)
        module
  map_smul' scalar value := by
    funext role
    cases role with
    | none =>
        change blockInnerReversal seed stage (scalar • value none) =
          scalar • blockInnerReversal seed stage (value none)
        exact (blockInnerReversal seed stage).map_smul scalar (value none)
    | some row =>
        change -(scalar • value (some row)) = scalar • (-value (some row))
        module

def blockWholeRelationReversal
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeRelation seed stage →ₗ[BlockCoordinateRing]
      BlockWholeRelation seed stage where
  toFun value row := -value row
  map_add' left right := by
    funext row
    change -(left row + right row) = -left row + -right row
    module
  map_smul' scalar value := by
    funext row
    change -(scalar • value row) = scalar • (-value row)
    module

theorem blockInnerAntiInvariant_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerAntiInvariant seed stage).comp (blockInnerAction seed stage) =
      (blockInnerAction seed stage).comp
        (blockInnerAntiInvariant seed stage) := by
  unfold blockInnerAntiInvariant
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id,
    blockInnerAction_reversal_square]

theorem blockFactorizationDifferential_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockFactorizationDifferential seed stage).comp
        (blockWholeVertexAction seed stage) =
      (blockWholeRelationAction seed stage).comp
        (blockFactorizationDifferential seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  have wholeSquare :
      blockInnerAntiInvariant seed stage
          (blockInnerAction seed stage (value none)) =
        blockInnerAction seed stage
          (blockInnerAntiInvariant seed stage (value none)) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun
      (blockInnerAntiInvariant_action_square seed stage) (value none)
  have quotientSquare :
      blockInnerAntiInvariant seed stage
          (blockInnerAction seed stage (value (some row))) =
        blockInnerAction seed stage
          (blockInnerAntiInvariant seed stage (value (some row))) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun
      (blockInnerAntiInvariant_action_square seed stage) (value (some row))
  change
    blockInnerAntiInvariant seed stage
          (blockInnerAction seed stage (value none)) -
        _ • blockInnerAntiInvariant seed stage
          (blockInnerAction seed stage (value (some row))) =
      blockInnerAction seed stage
        (blockInnerAntiInvariant seed stage (value none) -
          _ • blockInnerAntiInvariant seed stage (value (some row)))
  rw [wholeSquare, quotientSquare, map_sub, map_smul]

theorem blockInnerAntiInvariant_reversal
    (seed : FactorizationPayload) (stage : Nat)
    (value : BlockInner seed stage) :
    blockInnerAntiInvariant seed stage (blockInnerReversal seed stage value) =
      -blockInnerAntiInvariant seed stage value := by
  unfold blockInnerAntiInvariant
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  rw [blockInnerReversal_involutive]
  module

theorem blockFactorizationDifferential_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockFactorizationDifferential seed stage).comp
        (blockWholeVertexReversal seed stage) =
      (blockWholeRelationReversal seed stage).comp
        (blockFactorizationDifferential seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change
    blockInnerAntiInvariant seed stage
          (blockInnerReversal seed stage (value none)) -
        _ • blockInnerAntiInvariant seed stage (-value (some row)) =
      -(blockInnerAntiInvariant seed stage (value none) -
        _ • blockInnerAntiInvariant seed stage (value (some row)))
  rw [blockInnerAntiInvariant_reversal, map_neg]
  module

theorem blockWholeVertexAction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeVertexAction seed stage).comp
        (blockWholeVertexReversal seed stage) =
      (blockWholeVertexReversal seed stage).comp
        (blockWholeVertexAction seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (blockInnerAction_reversal_square seed stage).symm (value none)
  | some row =>
      change blockInnerAction seed stage (-value (some row)) =
        -blockInnerAction seed stage (value (some row))
      rw [map_neg]

theorem blockWholeRelationAction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationAction seed stage).comp
        (blockWholeRelationReversal seed stage) =
      (blockWholeRelationReversal seed stage).comp
        (blockWholeRelationAction seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change blockInnerAction seed stage (-value row) =
    -blockInnerAction seed stage (value row)
  rw [map_neg]

def blockWholeVertexRestriction
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeVertex seed (stage + 1) →ₗ[BlockCoordinateRing]
      BlockWholeVertex seed stage where
  toFun value role :=
    match role with
    | none => blockInnerRestriction seed stage (value none)
    | some row => blockInnerRestriction seed stage
        (value (some (liftFactorRow seed stage row)))
  map_add' left right := by
    funext role
    cases role with
    | none =>
        exact (blockInnerRestriction seed stage).map_add
          (left none) (right none)
    | some row =>
        exact (blockInnerRestriction seed stage).map_add
          (left (some (liftFactorRow seed stage row)))
          (right (some (liftFactorRow seed stage row)))
  map_smul' scalar value := by
    funext role
    cases role with
    | none =>
        change blockInnerRestriction seed stage (scalar • value none) =
          scalar • blockInnerRestriction seed stage (value none)
        exact (blockInnerRestriction seed stage).map_smul scalar (value none)
    | some row =>
        change blockInnerRestriction seed stage
            (scalar • value (some (liftFactorRow seed stage row))) =
          scalar • blockInnerRestriction seed stage
            (value (some (liftFactorRow seed stage row)))
        exact (blockInnerRestriction seed stage).map_smul scalar
          (value (some (liftFactorRow seed stage row)))

def blockWholeRelationRestriction
    (seed : FactorizationPayload) (stage : Nat) :
    BlockWholeRelation seed (stage + 1) →ₗ[BlockCoordinateRing]
      BlockWholeRelation seed stage where
  toFun value row := blockInnerRestriction seed stage
    (value (liftFactorRow seed stage row))
  map_add' left right := by
    funext row
    exact (blockInnerRestriction seed stage).map_add
      (left (liftFactorRow seed stage row))
      (right (liftFactorRow seed stage row))
  map_smul' scalar value := by
    funext row
    change blockInnerRestriction seed stage
        (scalar • value (liftFactorRow seed stage row)) =
      scalar • blockInnerRestriction seed stage
        (value (liftFactorRow seed stage row))
    exact (blockInnerRestriction seed stage).map_smul scalar
      (value (liftFactorRow seed stage row))

theorem blockInnerAntiInvariant_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerRestriction seed stage).comp
        (blockInnerAntiInvariant seed (stage + 1)) =
      (blockInnerAntiInvariant seed stage).comp
        (blockInnerRestriction seed stage) := by
  unfold blockInnerAntiInvariant
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    blockInnerRestriction_reversal_square]

theorem blockFactorizationDifferential_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockFactorizationDifferential seed stage).comp
        (blockWholeVertexRestriction seed stage) =
      (blockWholeRelationRestriction seed stage).comp
        (blockFactorizationDifferential seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  funext row
  have wholeSquare :
      blockInnerAntiInvariant seed stage
          (blockInnerRestriction seed stage (value none)) =
        blockInnerRestriction seed stage
          (blockInnerAntiInvariant seed (stage + 1) (value none)) := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun
        (blockInnerAntiInvariant_restriction_square seed stage) (value none)).symm
  have quotientSquare :
      blockInnerAntiInvariant seed stage
          (blockInnerRestriction seed stage
            (value (some (liftFactorRow seed stage row)))) =
        blockInnerRestriction seed stage
          (blockInnerAntiInvariant seed (stage + 1)
            (value (some (liftFactorRow seed stage row)))) := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun
        (blockInnerAntiInvariant_restriction_square seed stage)
          (value (some (liftFactorRow seed stage row)))).symm
  change
    blockInnerAntiInvariant seed stage
          (blockInnerRestriction seed stage (value none)) -
        (((rowPrime row : Nat) : BlockCoordinateRing) ^ rowExponent row) •
          blockInnerAntiInvariant seed stage
            (blockInnerRestriction seed stage
              (value (some (liftFactorRow seed stage row)))) =
      blockInnerRestriction seed stage
        (blockInnerAntiInvariant seed (stage + 1) (value none) -
          (((rowPrime (liftFactorRow seed stage row) : Nat) :
              BlockCoordinateRing) ^
              rowExponent (liftFactorRow seed stage row)) •
            blockInnerAntiInvariant seed (stage + 1)
              (value (some (liftFactorRow seed stage row))))
  rw [wholeSquare, quotientSquare,
    liftFactorRow_prime, liftFactorRow_exponent, map_sub, map_smul]

theorem blockWholeVertexRestriction_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeVertexRestriction seed stage).comp
        (blockWholeVertexAction seed (stage + 1)) =
      (blockWholeVertexAction seed stage).comp
        (blockWholeVertexRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (blockInnerRestriction_action_square seed stage) (value none)
  | some row =>
      exact LinearMap.congr_fun
        (blockInnerRestriction_action_square seed stage)
          (value (some (liftFactorRow seed stage row)))

theorem blockWholeRelationRestriction_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationRestriction seed stage).comp
        (blockWholeRelationAction seed (stage + 1)) =
      (blockWholeRelationAction seed stage).comp
        (blockWholeRelationRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  exact LinearMap.congr_fun
    (blockInnerRestriction_action_square seed stage)
      (value (liftFactorRow seed stage row))

theorem blockWholeVertexRestriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeVertexRestriction seed stage).comp
        (blockWholeVertexReversal seed (stage + 1)) =
      (blockWholeVertexReversal seed stage).comp
        (blockWholeVertexRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext role
  cases role with
  | none =>
      exact LinearMap.congr_fun
        (blockInnerRestriction_reversal_square seed stage) (value none)
  | some row =>
      change blockInnerRestriction seed stage
          (-value (some (liftFactorRow seed stage row))) =
        -blockInnerRestriction seed stage
          (value (some (liftFactorRow seed stage row)))
      rw [map_neg]

theorem blockWholeRelationRestriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeRelationRestriction seed stage).comp
        (blockWholeRelationReversal seed (stage + 1)) =
      (blockWholeRelationReversal seed stage).comp
        (blockWholeRelationRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change blockInnerRestriction seed stage
      (-value (liftFactorRow seed stage row)) =
    -blockInnerRestriction seed stage (value (liftFactorRow seed stage row))
  rw [map_neg]

/-! ## Exact rooted occurrence and complete producer readout -/

def blockWholeActionOccurrence
    (seed : FactorizationPayload) (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (BlockWholeVertex seed stage →ₗ[BlockCoordinateRing]
          BlockWholeVertex seed stage)) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, blockWholeVertexAction seed stage)

theorem blockWholeActionOccurrence_projects
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeActionOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold blockWholeActionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem blockWholeActionOccurrence_reads_action
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeActionOccurrence seed stage).root.2 =
      blockWholeVertexAction seed stage := by
  simp [blockWholeActionOccurrence, stageOccurrenceFrom]

theorem blockWholeFrame_generated_summary
    (seed : FactorizationPayload) (stage : Nat) :
    (blockWholeActionOccurrence seed stage).map Prod.fst =
        stageOccurrenceFrom seed stage ∧
      (blockFactorizationDifferential seed stage).comp
          (blockWholeVertexAction seed stage) =
        (blockWholeRelationAction seed stage).comp
          (blockFactorizationDifferential seed stage) ∧
      (blockFactorizationDifferential seed stage).comp
          (blockWholeVertexReversal seed stage) =
        (blockWholeRelationReversal seed stage).comp
          (blockFactorizationDifferential seed stage) ∧
      (blockWholeVertexAction seed stage).comp
          (blockWholeVertexReversal seed stage) =
        (blockWholeVertexReversal seed stage).comp
          (blockWholeVertexAction seed stage) ∧
      (blockFactorizationDifferential seed stage).comp
          (blockWholeVertexRestriction seed stage) =
        (blockWholeRelationRestriction seed stage).comp
          (blockFactorizationDifferential seed (stage + 1)) ∧
      (blockWholeVertexRestriction seed stage).comp
          (blockWholeVertexAction seed (stage + 1)) =
        (blockWholeVertexAction seed stage).comp
          (blockWholeVertexRestriction seed stage) ∧
      (blockWholeVertexRestriction seed stage).comp
          (blockWholeVertexReversal seed (stage + 1)) =
        (blockWholeVertexReversal seed stage).comp
          (blockWholeVertexRestriction seed stage) := by
  exact ⟨blockWholeActionOccurrence_projects seed stage,
    blockFactorizationDifferential_action_square seed stage,
    blockFactorizationDifferential_reversal_square seed stage,
    blockWholeVertexAction_reversal_square seed stage,
    blockFactorizationDifferential_restriction_square seed stage,
    blockWholeVertexRestriction_action_square seed stage,
    blockWholeVertexRestriction_reversal_square seed stage⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
