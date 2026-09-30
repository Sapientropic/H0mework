import Mathlib.LinearAlgebra.TensorProduct.Map
import H0mework.Arithmetic.EulerGlobal.ZeroFibre
import H0mework.Arithmetic.EulerGlobal.WholeGlobalAction

/-!
# Universal zero-fibre solution of the full-Euler whole relation complex

The global determinant zero fibre supplies only its universal scalar `r`.
On the same global whole relation complex we intersect two generated kernels:

* the degree-zero cocycle kernel of the actual factorization differential;
* the action kernel of `1 - rF`.

Thus every universal element is simultaneously an actual whole-factorization
solution and a zero-fibre Euler state.  Reversal preserves both kernels because
it is a chain involution commuting with the Euler action.  No selected point,
coordinate pair, quotient root, fixedness, or complex coordinate enters this
constructor.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CategoryTheory
open scoped TensorProduct

noncomputable section

abbrev CoefficientRing := GlobalZeroFiberRing

abbrev RelationGlobalState :=
  CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.GlobalState

abbrev GlobalVertex := (RelationGlobalState.X 0 : Type)
abbrev GlobalRelation := (RelationGlobalState.X 1 : Type)

abbrev ScalarVertex := TensorProduct ℤ CoefficientRing GlobalVertex
abbrev ScalarRelation := TensorProduct ℤ CoefficientRing GlobalRelation

def globalDifferential : GlobalVertex →ₗ[ℤ] GlobalRelation :=
  (RelationGlobalState.d 0 1).hom

def globalEulerZero : GlobalVertex →ₗ[ℤ] GlobalVertex :=
  (globalEulerAction.f 0).hom

def globalEulerOne : GlobalRelation →ₗ[ℤ] GlobalRelation :=
  (globalEulerAction.f 1).hom

def globalReversalZero : GlobalVertex →ₗ[ℤ] GlobalVertex :=
  (globalReversal.f 0).hom

def globalReversalOne : GlobalRelation →ₗ[ℤ] GlobalRelation :=
  (globalReversal.f 1).hom

def parameterMultiplication : CoefficientRing →ₗ[ℤ] CoefficientRing where
  toFun value := universalDeterminantParameter * value
  map_add' := by intro left right; exact mul_add _ _ _
  map_smul' := by
    intro scalar value
    simp only [RingHom.id_apply]
    ring

def extendedDifferential : ScalarVertex →ₗ[ℤ] ScalarRelation :=
  TensorProduct.map LinearMap.id globalDifferential

def extendedEulerZero : ScalarVertex →ₗ[ℤ] ScalarVertex :=
  TensorProduct.map parameterMultiplication globalEulerZero

def extendedEulerOne : ScalarRelation →ₗ[ℤ] ScalarRelation :=
  TensorProduct.map parameterMultiplication globalEulerOne

def extendedReversalZero : ScalarVertex →ₗ[ℤ] ScalarVertex :=
  TensorProduct.map LinearMap.id globalReversalZero

def extendedReversalOne : ScalarRelation →ₗ[ℤ] ScalarRelation :=
  TensorProduct.map LinearMap.id globalReversalOne

theorem globalDifferential_euler_square :
    globalDifferential.comp globalEulerZero =
      globalEulerOne.comp globalDifferential := by
  exact congrArg (fun arrow => arrow.hom) (globalEulerAction.comm 0 1)

theorem globalDifferential_reversal_square :
    globalDifferential.comp globalReversalZero =
      globalReversalOne.comp globalDifferential := by
  exact congrArg (fun arrow => arrow.hom) (globalReversal.comm 0 1)

theorem globalEulerReversalZero_commutes :
    globalReversalZero.comp globalEulerZero =
      globalEulerZero.comp globalReversalZero := by
  have commutation := congrArg
    (fun action : RelationGlobalState ⟶ RelationGlobalState => (action.f 0).hom)
    globalEuler_reversal_commutes
  exact commutation

theorem extendedDifferential_euler_square :
    extendedDifferential.comp extendedEulerZero =
      extendedEulerOne.comp extendedDifferential := by
  rw [extendedDifferential, extendedEulerZero, extendedEulerOne,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro value
    rfl
  · exact globalDifferential_euler_square

theorem extendedDifferential_reversal_square :
    extendedDifferential.comp extendedReversalZero =
      extendedReversalOne.comp extendedDifferential := by
  rw [extendedDifferential, extendedReversalZero, extendedReversalOne,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro value
    rfl
  · exact globalDifferential_reversal_square

theorem extendedEuler_reversalZero_commutes :
    extendedReversalZero.comp extendedEulerZero =
      extendedEulerZero.comp extendedReversalZero := by
  rw [extendedReversalZero, extendedEulerZero,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro value
    rfl
  · exact globalEulerReversalZero_commutes

def universalEulerOperator : ScalarVertex →ₗ[ℤ] ScalarVertex :=
  LinearMap.id - extendedEulerZero

theorem universalEulerOperator_reversal_commutes :
    universalEulerOperator.comp extendedReversalZero =
      extendedReversalZero.comp universalEulerOperator := by
  unfold universalEulerOperator
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]
  apply congrArg (fun current => extendedReversalZero - current)
  exact extendedEuler_reversalZero_commutes.symm

abbrev CocycleKernel := LinearMap.ker extendedDifferential
abbrev ActionKernel := LinearMap.ker universalEulerOperator

/-- Universal elements satisfy both the actual factorization equations and
the generated determinant-zero action equation. -/
abbrev UniversalSolutionKernel := CocycleKernel ⊓ ActionKernel

def universalInclusion : UniversalSolutionKernel →ₗ[ℤ] ScalarVertex :=
  UniversalSolutionKernel.subtype

theorem extendedReversalZero_involutive :
    Function.Involutive extendedReversalZero := by
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp [extendedReversalZero]
  | tmul coefficient vertex =>
      have involution := congrArg
        (fun action : RelationGlobalState ⟶ RelationGlobalState =>
          (action.f 0).hom vertex)
        globalReversal_involutive
      change globalReversalZero (globalReversalZero vertex) = vertex at involution
      simp [extendedReversalZero, involution]
  | add left right left_ih right_ih =>
      simp only [map_add, left_ih, right_ih]

def solutionReversal : UniversalSolutionKernel →ₗ[ℤ]
    UniversalSolutionKernel :=
  LinearMap.codRestrict UniversalSolutionKernel
    (extendedReversalZero.comp UniversalSolutionKernel.subtype)
    (fun value => by
      rw [Submodule.mem_inf]
      constructor
      · rw [LinearMap.mem_ker]
        have square := LinearMap.congr_fun
          extendedDifferential_reversal_square value.1
        change extendedDifferential (extendedReversalZero value.1) = 0
        change extendedDifferential (extendedReversalZero value.1) =
          extendedReversalOne (extendedDifferential value.1) at square
        have cocycleZero : extendedDifferential value.1 = 0 :=
          LinearMap.mem_ker.mp value.2.1
        rw [cocycleZero, map_zero] at square
        exact square
      · rw [LinearMap.mem_ker]
        have square := LinearMap.congr_fun
          universalEulerOperator_reversal_commutes value.1
        change universalEulerOperator (extendedReversalZero value.1) = 0
        change universalEulerOperator (extendedReversalZero value.1) =
          extendedReversalZero (universalEulerOperator value.1) at square
        have actionZero : universalEulerOperator value.1 = 0 :=
          LinearMap.mem_ker.mp value.2.2
        rw [actionZero, map_zero] at square
        exact square)

theorem solutionReversal_involutive : Function.Involutive solutionReversal := by
  intro value
  apply Subtype.ext
  exact extendedReversalZero_involutive value.1

def antiInvariantDifference (value : UniversalSolutionKernel) :
    UniversalSolutionKernel :=
  value - solutionReversal value

theorem solutionReversal_antiInvariantDifference
    (value : UniversalSolutionKernel) :
    solutionReversal (antiInvariantDifference value) =
      -antiInvariantDifference value := by
  unfold antiInvariantDifference
  rw [map_sub, solutionReversal_involutive]
  module

def universalSolutionOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      (UniversalSolutionKernel →ₗ[ℤ] ScalarVertex)) :=
  seedOccurrence.map fun owner => (owner, universalInclusion)

theorem universalSolutionOccurrence_projects :
    universalSolutionOccurrence.map Prod.fst = seedOccurrence := by
  unfold universalSolutionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_generated_D_relation_cocycle_and_action_kernel :
    universalSolutionOccurrence.map Prod.fst = seedOccurrence ∧
      (∀ value : UniversalSolutionKernel,
        extendedDifferential (universalInclusion value) = 0) ∧
      (∀ value : UniversalSolutionKernel,
        universalEulerOperator (universalInclusion value) = 0) ∧
      Function.Involutive solutionReversal := by
  refine ⟨universalSolutionOccurrence_projects, ?_, ?_,
    solutionReversal_involutive⟩
  · intro value
    exact LinearMap.mem_ker.mp value.2.1
  · intro value
    exact LinearMap.mem_ker.mp value.2.2

end
end CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
