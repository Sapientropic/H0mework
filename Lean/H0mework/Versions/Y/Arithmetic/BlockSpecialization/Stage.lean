import H0mework.Versions.X.Arithmetic.EulerGlobal.DerivedDeterminant
import H0mework.Versions.Y.Arithmetic.EulerDerived.DeterminantSection

/-!
# Arithmetic specialization of the prime-dual block frame

The existing block variables are evaluated at the actual arithmetic point

`A_p = p`, `B_p = 0`.

Coefficientwise evaluation followed by the existing initial-value solution
maps the block inner carrier to the integral full-Euler carrier.  The map
commutes with the actual Euler action, dual reversal, and source successor.
No zero-fibre point or inverse-limit base-change assertion enters this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace BlockArithmeticSpecializationStage

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection

noncomputable section

/-- The arithmetic point of the universal block-coordinate ring.  It is the
existing polynomial collapse followed by evaluation at `X = 1`. -/
def actualBlockSpecialization : BlockCoordinateRing →+* ℤ :=
  (Polynomial.evalRingHom 1).comp collapseBlockCoordinate

@[simp] theorem actualBlockSpecialization_blockA (prime : Nat.Primes) :
    actualBlockSpecialization (blockA prime) = (prime : ℤ) := by
  simp [actualBlockSpecialization]

@[simp] theorem actualBlockSpecialization_blockB (prime : Nat.Primes) :
    actualBlockSpecialization (blockB prime) = 0 := by
  simp [actualBlockSpecialization]

@[simp] theorem actualBlockSpecialization_intCast (value : ℤ) :
    actualBlockSpecialization (value : BlockCoordinateRing) = value := by
  simp [actualBlockSpecialization]

/-- Coefficientwise arithmetic evaluation on the exponent-zero block face. -/
def blockInnerBaseRead (seed : FactorizationPayload) (stage : Nat) :
    BlockInner seed stage →ₗ[ℤ] BaseLattice seed stage where
  toFun := fun value index => actualBlockSpecialization (value index)
  map_add' := by
    intro left right
    funext index
    exact map_add actualBlockSpecialization _ _
  map_smul' := by
    intro scalar value
    funext index
    simp [actualBlockSpecialization]

/-- The block value read into the existing full-Euler recurrence solution. -/
def blockInnerCarrierRead (seed : FactorizationPayload) (stage : Nat) :
    BlockInner seed stage →ₗ[ℤ] Carrier seed stage :=
  (solutionOfBase seed stage).comp (blockInnerBaseRead seed stage)

theorem blockInnerBaseRead_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerBaseRead seed stage).comp
        ((blockInnerAction seed stage).restrictScalars ℤ) =
      (baseEulerAction seed stage).comp (blockInnerBaseRead seed stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  simp [blockInnerBaseRead, blockInnerAction, baseEulerAction,
    actualPrimeScalar]

theorem solutionOfBase_baseEulerAction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (solutionOfBase seed stage).comp (baseEulerAction seed stage) =
      (carrierEulerAction seed stage).comp (solutionOfBase seed stage) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext index
  simp [solutionOfBase, extendFromBase, baseEulerAction,
    carrierEulerAction, vertexEulerAction]
  ring

/-- At the actual arithmetic point the universal block action is exactly the
existing integral carrier Euler action. -/
theorem blockInnerCarrierRead_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerCarrierRead seed stage).comp
        ((blockInnerAction seed stage).restrictScalars ℤ) =
      (carrierEulerAction seed stage).comp
        (blockInnerCarrierRead seed stage) := by
  unfold blockInnerCarrierRead
  rw [LinearMap.comp_assoc, blockInnerBaseRead_action_square,
    ← LinearMap.comp_assoc, solutionOfBase_baseEulerAction_square]
  rw [LinearMap.comp_assoc]

def blockBaseReversal (seed : FactorizationPayload) (stage : Nat) :
    BaseLattice seed stage →ₗ[ℤ] BaseLattice seed stage where
  toFun := fun value index => value (index.1, index.2.rev)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem blockInnerBaseRead_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerBaseRead seed stage).comp
        ((blockInnerReversal seed stage).restrictScalars ℤ) =
      (blockBaseReversal seed stage).comp
        (blockInnerBaseRead seed stage) := by
  rfl

theorem solutionOfBase_blockBaseReversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (solutionOfBase seed stage).comp (blockBaseReversal seed stage) =
      (carrierReversal seed stage).comp (solutionOfBase seed stage) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext index
  rfl

theorem blockInnerCarrierRead_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerCarrierRead seed stage).comp
        ((blockInnerReversal seed stage).restrictScalars ℤ) =
      (carrierReversal seed stage).comp
        (blockInnerCarrierRead seed stage) := by
  unfold blockInnerCarrierRead
  rw [LinearMap.comp_assoc, blockInnerBaseRead_reversal_square,
    ← LinearMap.comp_assoc, solutionOfBase_blockBaseReversal_square]
  rw [LinearMap.comp_assoc]

theorem blockInnerBaseRead_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerBaseRead seed stage).comp
        ((blockInnerRestriction seed stage).restrictScalars ℤ) =
      (baseRestriction seed stage).comp
        (blockInnerBaseRead seed (stage + 1)) := by
  rfl

theorem solutionOfBase_baseRestriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (solutionOfBase seed stage).comp (baseRestriction seed stage) =
      (carrierRestriction seed stage).comp
        (solutionOfBase seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  apply (carrierEquivBase seed stage).injective
  change baseRead seed stage
      (solutionOfBase seed stage (baseRestriction seed stage value)) =
    baseRead seed stage
      (carrierRestriction seed stage
        (solutionOfBase seed (stage + 1) value))
  rw [baseRead_solutionOfBase, baseRead_carrierRestriction,
    baseRead_solutionOfBase]

theorem blockInnerCarrierRead_restriction_square
    (seed : FactorizationPayload) (stage : Nat) :
    (blockInnerCarrierRead seed stage).comp
        ((blockInnerRestriction seed stage).restrictScalars ℤ) =
      (carrierRestriction seed stage).comp
        (blockInnerCarrierRead seed (stage + 1)) := by
  unfold blockInnerCarrierRead
  rw [LinearMap.comp_assoc, blockInnerBaseRead_restriction_square,
    ← LinearMap.comp_assoc, solutionOfBase_baseRestriction_square]
  rw [LinearMap.comp_assoc]

/-- Semilinearity needed by the whole/relation differential: evaluation of a
block coefficient becomes multiplication by its arithmetic value. -/
theorem blockInnerCarrierRead_block_smul
    (seed : FactorizationPayload) (stage : Nat)
    (coefficient : BlockCoordinateRing) (value : BlockInner seed stage) :
    blockInnerCarrierRead seed stage (coefficient • value) =
      actualBlockSpecialization coefficient •
        blockInnerCarrierRead seed stage value := by
  apply Subtype.ext
  funext index
  simp [blockInnerCarrierRead, blockInnerBaseRead, solutionOfBase,
    extendFromBase, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

abbrev ActualBlockStageReadPayload (stage : Nat) :=
  FactorizationPayload ×
    (BlockInner seedOccurrence.root stage →ₗ[ℤ]
      Carrier seedOccurrence.root stage)

/-- Exact-stage occurrence lock for the arithmetic specialization. -/
def actualBlockStageReadOccurrence (stage : Nat) :
    RootedAccountedUnfolding (ActualBlockStageReadPayload stage) :=
  (stageOccurrenceFrom seedOccurrence.root stage).map fun owner =>
    (owner, blockInnerCarrierRead seedOccurrence.root stage)

theorem actualBlockStageReadOccurrence_projects (stage : Nat) :
    (actualBlockStageReadOccurrence stage).map Prod.fst =
      stageOccurrenceFrom seedOccurrence.root stage := by
  unfold actualBlockStageReadOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seedOccurrence.root stage).map id = _
  exact RootedAccountedUnfolding.map_id _

end
end BlockArithmeticSpecializationStage
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
