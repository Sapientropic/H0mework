import Mathlib.LinearAlgebra.FreeModule.PID
import H0mework.Versions.R2.Arithmetic.EulerLocal.DependentDiagram

/-!
# Integral full-Euler solution action

At one exact runtime factorization stage, a vertex is indexed by an actual
prime, one of its generated exponent occurrences, and the dual bit.  An edge
joins consecutive exponent occurrences.  The Euler relation is the integral
recurrence

`v (e + 1) = p * v e`.

The carrier is the kernel of this actual recurrence map.  Multiplication by
the same actual prime and dual-bit reversal preserve that kernel and commute.
The successor restriction forgets only newly generated prime/exponent
coordinates and preserves the recurrence.  No quotient root, determinant
polynomial, zero point, coordinate evaluator, completed prime table, or
fixedness enters this domain producer.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerSolutionAction

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationOccurrence
open ArithmeticGeneration

noncomputable section

abbrev VertexIndex (seed : FactorizationPayload) (stage : Nat) :=
  EulerIndex seed stage

abbrev VertexLattice (seed : FactorizationPayload) (stage : Nat) :=
  VertexIndex seed stage → ℤ

abbrev EdgeExponent (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) :=
  Fin (multiplicity (StageHistory seed stage) primeIndex)

abbrev EdgeIndex (seed : FactorizationPayload) (stage : Nat) :=
  Σ primeIndex : StagePrime seed stage,
    EdgeExponent seed stage primeIndex × Fin 2

abbrev EdgeLattice (seed : FactorizationPayload) (stage : Nat) :=
  EdgeIndex seed stage → ℤ

def edgeLowExponent
    {seed : FactorizationPayload} {stage : Nat}
    {primeIndex : StagePrime seed stage}
    (edgeExponent : EdgeExponent seed stage primeIndex) :
    StageExponent seed stage primeIndex :=
  ⟨edgeExponent, edgeExponent.isLt.trans (Nat.lt_succ_self _)⟩

def edgeHighExponent
    {seed : FactorizationPayload} {stage : Nat}
    {primeIndex : StagePrime seed stage}
    (edgeExponent : EdgeExponent seed stage primeIndex) :
    StageExponent seed stage primeIndex :=
  ⟨edgeExponent + 1, Nat.succ_lt_succ edgeExponent.isLt⟩

def actualPrimeScalar (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) : ℤ :=
  ((stageFactorization seed stage).actualPrime primeIndex : Nat)

/-- The actual local Euler relation on the generated exponent path. -/
def eulerRecurrence (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed stage →ₗ[ℤ] EdgeLattice seed stage where
  toFun := fun value edge =>
    value ⟨edge.1, edgeHighExponent edge.2.1, edge.2.2⟩ -
      actualPrimeScalar seed stage edge.1 *
        value ⟨edge.1, edgeLowExponent edge.2.1, edge.2.2⟩
  map_add' := by
    intro left right
    funext edge
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro scalar value
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Integral Euler states satisfying every actual exponent-successor row. -/
abbrev Carrier (seed : FactorizationPayload) (stage : Nat) :=
  LinearMap.ker (eulerRecurrence seed stage)

noncomputable def carrierBasis
    (seed : FactorizationPayload) (stage : Nat) :
    Σ rank : Nat, Module.Basis (Fin rank) ℤ (Carrier seed stage) :=
  Submodule.basisOfPid
    (Module.finBasis ℤ (VertexLattice seed stage))
    (Carrier seed stage)

noncomputable instance carrierFree
    (seed : FactorizationPayload) (stage : Nat) :
    Module.Free ℤ (Carrier seed stage) :=
  Module.Free.of_basis (carrierBasis seed stage).2

noncomputable instance carrierFinite
    (seed : FactorizationPayload) (stage : Nat) :
    Module.Finite ℤ (Carrier seed stage) :=
  Module.Finite.of_basis (carrierBasis seed stage).2

abbrev BaseIndex (seed : FactorizationPayload) (stage : Nat) :=
  StagePrime seed stage × Fin 2

abbrev BaseLattice (seed : FactorizationPayload) (stage : Nat) :=
  BaseIndex seed stage → ℤ

def exponentZero (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) :
    StageExponent seed stage primeIndex :=
  ⟨0, Nat.zero_lt_succ _⟩

def baseRead (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage →ₗ[ℤ] BaseLattice seed stage where
  toFun := fun value index =>
    value.1 ⟨index.1, exponentZero seed stage index.1, index.2⟩
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def extendFromBase (seed : FactorizationPayload) (stage : Nat) :
    BaseLattice seed stage →ₗ[ℤ] VertexLattice seed stage where
  toFun := fun value index =>
    (actualPrimeScalar seed stage index.1) ^ index.2.1.1 *
      value (index.1, index.2.2)
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem eulerRecurrence_extendFromBase_eq_zero
    (seed : FactorizationPayload) (stage : Nat)
    (value : BaseLattice seed stage) :
    eulerRecurrence seed stage (extendFromBase seed stage value) = 0 := by
  funext edge
  rcases edge with ⟨primeIndex, edgeExponent, dualIndex⟩
  simp only [eulerRecurrence, extendFromBase, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.zero_apply]
  change
    actualPrimeScalar seed stage primeIndex ^ (edgeExponent.1 + 1) *
          value (primeIndex, dualIndex) -
        actualPrimeScalar seed stage primeIndex *
          (actualPrimeScalar seed stage primeIndex ^ edgeExponent.1 *
            value (primeIndex, dualIndex)) = 0
  rw [pow_succ]
  ring

def solutionOfBase (seed : FactorizationPayload) (stage : Nat) :
    BaseLattice seed stage →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage) (extendFromBase seed stage)
    (fun value => by
      rw [LinearMap.mem_ker]
      exact eulerRecurrence_extendFromBase_eq_zero seed stage value)

theorem carrier_value_at_nat
    (seed : FactorizationPayload) (stage : Nat)
    (value : Carrier seed stage)
    (primeIndex : StagePrime seed stage) (dualIndex : Fin 2) :
    ∀ (exponent : Nat)
      (bound : exponent <
        multiplicity (StageHistory seed stage) primeIndex + 1),
      value.1 ⟨primeIndex, ⟨exponent, bound⟩, dualIndex⟩ =
        actualPrimeScalar seed stage primeIndex ^ exponent *
          value.1 ⟨primeIndex,
            exponentZero seed stage primeIndex, dualIndex⟩ := by
  intro exponent
  induction exponent with
  | zero =>
      intro bound
      have exponentEq :
          (⟨0, bound⟩ : StageExponent seed stage primeIndex) =
            exponentZero seed stage primeIndex := by
        apply Fin.ext
        rfl
      rw [exponentEq]
      simp
  | succ exponent inductionHypothesis =>
      intro bound
      have edgeBound : exponent <
          multiplicity (StageHistory seed stage) primeIndex := by
        omega
      let edgeExponent : EdgeExponent seed stage primeIndex :=
        ⟨exponent, edgeBound⟩
      have relationZero := congrFun (LinearMap.mem_ker.mp value.2)
        (⟨primeIndex, edgeExponent, dualIndex⟩ : EdgeIndex seed stage)
      have previous := inductionHypothesis (Nat.lt_succ_of_lt edgeBound)
      change
        value.1 ⟨primeIndex,
            edgeHighExponent edgeExponent, dualIndex⟩ -
          actualPrimeScalar seed stage primeIndex *
            value.1 ⟨primeIndex,
              edgeLowExponent edgeExponent, dualIndex⟩ = 0 at relationZero
      have highEq : edgeHighExponent edgeExponent =
          (⟨exponent + 1, bound⟩ :
            StageExponent seed stage primeIndex) := by
        apply Fin.ext
        rfl
      have lowEq : edgeLowExponent edgeExponent =
          (⟨exponent, Nat.lt_succ_of_lt edgeBound⟩ :
            StageExponent seed stage primeIndex) := by
        apply Fin.ext
        rfl
      rw [highEq, lowEq, previous] at relationZero
      rw [pow_succ]
      linarith

theorem solutionOfBase_baseRead
    (seed : FactorizationPayload) (stage : Nat)
    (value : Carrier seed stage) :
    solutionOfBase seed stage (baseRead seed stage value) = value := by
  apply Subtype.ext
  funext index
  rcases index with ⟨primeIndex, localExponent, dualIndex⟩
  change actualPrimeScalar seed stage primeIndex ^ localExponent.1 *
      value.1 ⟨primeIndex,
        exponentZero seed stage primeIndex, dualIndex⟩ =
    value.1 ⟨primeIndex, localExponent, dualIndex⟩
  exact (carrier_value_at_nat seed stage value primeIndex dualIndex
    localExponent.1 localExponent.2).symm

theorem baseRead_solutionOfBase
    (seed : FactorizationPayload) (stage : Nat)
    (value : BaseLattice seed stage) :
    baseRead seed stage (solutionOfBase seed stage value) = value := by
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  simp [baseRead, solutionOfBase, extendFromBase, exponentZero]

noncomputable def carrierEquivBase
    (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage ≃ₗ[ℤ] BaseLattice seed stage where
  toLinearMap := baseRead seed stage
  invFun := solutionOfBase seed stage
  left_inv := solutionOfBase_baseRead seed stage
  right_inv := baseRead_solutionOfBase seed stage

def vertexEulerAction (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed stage →ₗ[ℤ] VertexLattice seed stage where
  toFun := fun value index =>
    actualPrimeScalar seed stage index.1 * value index
  map_add' := by
    intro left right
    funext index
    exact mul_add _ _ _
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def edgeEulerAction (seed : FactorizationPayload) (stage : Nat) :
    EdgeLattice seed stage →ₗ[ℤ] EdgeLattice seed stage where
  toFun := fun value index =>
    actualPrimeScalar seed stage index.1 * value index
  map_add' := by
    intro left right
    funext index
    exact mul_add _ _ _
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem eulerRecurrence_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (eulerRecurrence seed stage).comp (vertexEulerAction seed stage) =
      (edgeEulerAction seed stage).comp (eulerRecurrence seed stage) := by
  apply LinearMap.ext
  intro value
  funext edge
  simp [eulerRecurrence, vertexEulerAction, edgeEulerAction]
  ring

def carrierEulerAction (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage)
    ((vertexEulerAction seed stage).comp (Carrier seed stage).subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun
        (eulerRecurrence_action_square seed stage) value.1
      change eulerRecurrence seed stage
          (vertexEulerAction seed stage value.1) = 0
      change eulerRecurrence seed stage
          (vertexEulerAction seed stage value.1) =
        edgeEulerAction seed stage
          (eulerRecurrence seed stage value.1) at square
      rw [LinearMap.mem_ker.mp value.2, map_zero] at square
      exact square)

def vertexReversal (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed stage →ₗ[ℤ] VertexLattice seed stage where
  toFun := fun value index =>
    value ⟨index.1, index.2.1, index.2.2.rev⟩
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def edgeReversal (seed : FactorizationPayload) (stage : Nat) :
    EdgeLattice seed stage →ₗ[ℤ] EdgeLattice seed stage where
  toFun := fun value index =>
    value ⟨index.1, index.2.1, index.2.2.rev⟩
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem eulerRecurrence_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (eulerRecurrence seed stage).comp (vertexReversal seed stage) =
      (edgeReversal seed stage).comp (eulerRecurrence seed stage) := by
  rfl

def carrierReversal (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage)
    ((vertexReversal seed stage).comp (Carrier seed stage).subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun
        (eulerRecurrence_reversal_square seed stage) value.1
      change eulerRecurrence seed stage
          (vertexReversal seed stage value.1) = 0
      change eulerRecurrence seed stage
          (vertexReversal seed stage value.1) =
        edgeReversal seed stage
          (eulerRecurrence seed stage value.1) at square
      rw [LinearMap.mem_ker.mp value.2, map_zero] at square
      exact square)

theorem vertexReversal_involutive
    (seed : FactorizationPayload) (stage : Nat) :
    Function.Involutive (vertexReversal seed stage) := by
  intro value
  funext index
  simp [vertexReversal]

theorem carrierReversal_involutive
    (seed : FactorizationPayload) (stage : Nat) :
    Function.Involutive (carrierReversal seed stage) := by
  intro value
  apply Subtype.ext
  exact vertexReversal_involutive seed stage value.1

theorem carrierEuler_reversal_commutes
    (seed : FactorizationPayload) (stage : Nat) :
    (carrierEulerAction seed stage).comp (carrierReversal seed stage) =
      (carrierReversal seed stage).comp (carrierEulerAction seed stage) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext index
  rfl

def liftEdgeExponent
    (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage)
    (edgeExponent : EdgeExponent seed stage primeIndex) :
    EdgeExponent seed (stage + 1) (liftPrime seed stage primeIndex) := by
  refine ⟨edgeExponent.1, ?_⟩
  exact edgeExponent.2.trans_le
    (factorization_mono_succ seed stage primeIndex.1)

def liftEdgeIndex (seed : FactorizationPayload) (stage : Nat) :
    EdgeIndex seed stage → EdgeIndex seed (stage + 1)
  | ⟨primeIndex, edgeExponent, dualIndex⟩ =>
      ⟨liftPrime seed stage primeIndex,
        liftEdgeExponent seed stage primeIndex edgeExponent, dualIndex⟩

theorem edgeLowExponent_lift
    (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage)
    (edgeExponent : EdgeExponent seed stage primeIndex) :
    edgeLowExponent
        (liftEdgeExponent seed stage primeIndex edgeExponent) =
      liftExponent seed stage primeIndex
        (edgeLowExponent edgeExponent) := by
  apply Fin.ext
  simp [edgeLowExponent, liftEdgeExponent, liftExponent]

theorem edgeHighExponent_lift
    (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage)
    (edgeExponent : EdgeExponent seed stage primeIndex) :
    edgeHighExponent
        (liftEdgeExponent seed stage primeIndex edgeExponent) =
      liftExponent seed stage primeIndex
        (edgeHighExponent edgeExponent) := by
  apply Fin.ext
  simp [edgeHighExponent, liftEdgeExponent, liftExponent]

def vertexRestriction (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed (stage + 1) →ₗ[ℤ] VertexLattice seed stage :=
  restriction seed stage

def edgeRestriction (seed : FactorizationPayload) (stage : Nat) :
    EdgeLattice seed (stage + 1) →ₗ[ℤ] EdgeLattice seed stage where
  toFun := fun value index => value (liftEdgeIndex seed stage index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem restriction_recurrence_square
    (seed : FactorizationPayload) (stage : Nat) :
    (eulerRecurrence seed stage).comp (vertexRestriction seed stage) =
      (edgeRestriction seed stage).comp
        (eulerRecurrence seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  funext edge
  rcases edge with ⟨primeIndex, edgeExponent, dualIndex⟩
  change
    value ⟨liftPrime seed stage primeIndex,
        liftExponent seed stage primeIndex
          (edgeHighExponent edgeExponent), dualIndex⟩ -
      actualPrimeScalar seed stage primeIndex *
        value ⟨liftPrime seed stage primeIndex,
          liftExponent seed stage primeIndex
            (edgeLowExponent edgeExponent), dualIndex⟩ =
      value ⟨liftPrime seed stage primeIndex,
          edgeHighExponent
            (liftEdgeExponent seed stage primeIndex edgeExponent), dualIndex⟩ -
        actualPrimeScalar seed (stage + 1)
            (liftPrime seed stage primeIndex) *
          value ⟨liftPrime seed stage primeIndex,
            edgeLowExponent
              (liftEdgeExponent seed stage primeIndex edgeExponent), dualIndex⟩
  rw [edgeLowExponent_lift, edgeHighExponent_lift]
  unfold actualPrimeScalar
  rw [liftPrime_actualPrime]

def carrierRestriction (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed (stage + 1) →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage)
    ((vertexRestriction seed stage).comp (Carrier seed (stage + 1)).subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun
        (restriction_recurrence_square seed stage) value.1
      change eulerRecurrence seed stage
          (vertexRestriction seed stage value.1) = 0
      change eulerRecurrence seed stage
          (vertexRestriction seed stage value.1) =
        edgeRestriction seed stage
          (eulerRecurrence seed (stage + 1) value.1) at square
      rw [LinearMap.mem_ker.mp value.2, map_zero] at square
      exact square)

def baseRestriction (seed : FactorizationPayload) (stage : Nat) :
    BaseLattice seed (stage + 1) →ₗ[ℤ] BaseLattice seed stage where
  toFun := fun value index =>
    value (liftPrime seed stage index.1, index.2)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem liftPrime_injective
    (seed : FactorizationPayload) (stage : Nat) :
    Function.Injective (liftPrime seed stage) := by
  intro left right equality
  apply Subtype.ext
  exact congrArg (fun primeIndex => primeIndex.1) equality

theorem baseRestriction_surjective
    (seed : FactorizationPayload) (stage : Nat) :
    Function.Surjective (baseRestriction seed stage) := by
  intro value
  have liftBaseInjective : Function.Injective
      (Prod.map (liftPrime seed stage) id :
        BaseIndex seed stage → BaseIndex seed (stage + 1)) :=
    (liftPrime_injective seed stage).prodMap Function.injective_id
  obtain ⟨nextValue, equality⟩ :=
    liftBaseInjective.surjective_comp_right value
  refine ⟨nextValue, ?_⟩
  exact equality

theorem baseRead_carrierRestriction
    (seed : FactorizationPayload) (stage : Nat)
    (value : Carrier seed (stage + 1)) :
    baseRead seed stage (carrierRestriction seed stage value) =
      baseRestriction seed stage (baseRead seed (stage + 1) value) := by
  funext index
  rcases index with ⟨primeIndex, dualIndex⟩
  change value.1
      (liftIndex seed stage
        ⟨primeIndex, exponentZero seed stage primeIndex, dualIndex⟩) =
    value.1 ⟨liftPrime seed stage primeIndex,
      exponentZero seed (stage + 1) (liftPrime seed stage primeIndex),
      dualIndex⟩
  congr 2

theorem carrierRestriction_surjective
    (seed : FactorizationPayload) (stage : Nat) :
    Function.Surjective (carrierRestriction seed stage) := by
  intro value
  obtain ⟨nextBase, nextBaseRestriction⟩ :=
    baseRestriction_surjective seed stage (baseRead seed stage value)
  refine ⟨solutionOfBase seed (stage + 1) nextBase, ?_⟩
  apply (carrierEquivBase seed stage).injective
  change baseRead seed stage
      (carrierRestriction seed stage
        (solutionOfBase seed (stage + 1) nextBase)) =
    baseRead seed stage value
  rw [baseRead_carrierRestriction,
    baseRead_solutionOfBase, nextBaseRestriction]

theorem carrierRestriction_euler_square
    (seed : FactorizationPayload) (stage : Nat) :
    (carrierRestriction seed stage).comp
        (carrierEulerAction seed (stage + 1)) =
      (carrierEulerAction seed stage).comp
        (carrierRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext index
  change actualPrimeScalar seed (stage + 1)
      (liftPrime seed stage index.1) * value.1
        (liftIndex seed stage index) =
    actualPrimeScalar seed stage index.1 * value.1
      (liftIndex seed stage index)
  unfold actualPrimeScalar
  rw [liftPrime_actualPrime]

theorem carrierRestriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (carrierRestriction seed stage).comp
        (carrierReversal seed (stage + 1)) =
      (carrierReversal seed stage).comp
        (carrierRestriction seed stage) := by
  rfl

/-- Exact-root occurrence of the full integral Euler/reversal action. -/
def actionOccurrence (seed : FactorizationPayload) (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        ((Carrier seed stage →ₗ[ℤ] Carrier seed stage) ×
          (Carrier seed stage →ₗ[ℤ] Carrier seed stage))) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, (carrierEulerAction seed stage, carrierReversal seed stage))

theorem actionOccurrence_projects
    (seed : FactorizationPayload) (stage : Nat) :
    (actionOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold actionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem preserves_actual_relation_action_reversal_and_successor
    (seed : FactorizationPayload) (stage : Nat) :
    (actionOccurrence seed stage).root.2.1 =
        carrierEulerAction seed stage ∧
      (actionOccurrence seed stage).root.2.2 =
        carrierReversal seed stage ∧
      Function.Involutive (carrierReversal seed stage) ∧
      (carrierEulerAction seed stage).comp (carrierReversal seed stage) =
        (carrierReversal seed stage).comp (carrierEulerAction seed stage) ∧
      (carrierRestriction seed stage).comp
          (carrierEulerAction seed (stage + 1)) =
        (carrierEulerAction seed stage).comp
          (carrierRestriction seed stage) := by
  refine ⟨?_, ?_, carrierReversal_involutive seed stage,
    carrierEuler_reversal_commutes seed stage,
    carrierRestriction_euler_square seed stage⟩
  · simp [actionOccurrence]
  · simp [actionOccurrence]

end
end CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
