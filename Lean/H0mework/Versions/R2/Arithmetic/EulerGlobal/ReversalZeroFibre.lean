import Mathlib.LinearAlgebra.TensorProduct.Map
import H0mework.Versions.R2.Arithmetic.EulerGlobal.Action
import H0mework.Versions.R2.Arithmetic.EulerGlobal.ZeroFibre

/-!
# Reversal-equivariant universal determinant kernel

The global determinant zero fibre supplies only its universal scalar.  The
same actual global Euler action then generates the scalar-extended operator
`1 - rF`.  Its kernel inclusion is the universal arithmetic inclusion.
Because the actual global reversal commutes with `F`, it preserves this
kernel and generates the anti-invariant difference of every kernel element.

No dual coordinate pair, chosen zero vector, fixedness, quotient landing, or
complex coordinate is supplied by a caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerReversalEquivariantZeroFiber

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
  (FactorizationPayload seedOccurrence)
open CanonicalUnitArithmeticFactorizationFullEulerGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CategoryTheory
open scoped TensorProduct

noncomputable section

abbrev CoefficientRing := GlobalZeroFiberRing

abbrev GlobalCarrier := (GlobalState.X 0 : Type)

abbrev ScalarExtendedCarrier :=
  TensorProduct ℤ CoefficientRing GlobalCarrier

def globalEulerLinear : GlobalCarrier →ₗ[ℤ] GlobalCarrier :=
  (globalEulerAction.f 0).hom

def globalReversalLinear : GlobalCarrier →ₗ[ℤ] GlobalCarrier :=
  (globalReversal.f 0).hom

def parameterMultiplication : CoefficientRing →ₗ[ℤ] CoefficientRing where
  toFun value := universalDeterminantParameter * value
  map_add' := by intro left right; exact mul_add _ _ _
  map_smul' := by
    intro scalar value
    simp only [RingHom.id_apply]
    ring

def extendedEulerAction : ScalarExtendedCarrier →ₗ[ℤ]
    ScalarExtendedCarrier :=
  TensorProduct.map parameterMultiplication globalEulerLinear

def extendedReversal : ScalarExtendedCarrier →ₗ[ℤ]
    ScalarExtendedCarrier :=
  TensorProduct.map LinearMap.id globalReversalLinear

/-- The action equation over the generated determinant zero-fibre scalar. -/
def universalEulerOperator : ScalarExtendedCarrier →ₗ[ℤ]
    ScalarExtendedCarrier :=
  LinearMap.id - extendedEulerAction

theorem globalEulerReversalLinear_commutes :
    globalReversalLinear.comp globalEulerLinear =
      globalEulerLinear.comp globalReversalLinear := by
  have commutation := congrArg
    (fun action : GlobalState ⟶ GlobalState => (action.f 0).hom)
    globalEuler_reversal_commutes
  exact commutation

theorem extendedEuler_reversal_commutes :
    extendedReversal.comp extendedEulerAction =
      extendedEulerAction.comp extendedReversal := by
  rw [extendedReversal, extendedEulerAction,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro value
    rfl
  · exact globalEulerReversalLinear_commutes

theorem universalEulerOperator_reversal_commutes :
    universalEulerOperator.comp extendedReversal =
      extendedReversal.comp universalEulerOperator := by
  unfold universalEulerOperator
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]
  apply congrArg (fun current => extendedReversal - current)
  exact extendedEuler_reversal_commutes.symm

theorem globalReversalLinear_involutive :
    Function.Involutive globalReversalLinear := by
  intro value
  have involution := congrArg
    (fun action : GlobalState ⟶ GlobalState => (action.f 0).hom value)
    globalReversal_involutive
  simpa [globalReversalLinear] using involution

theorem extendedReversal_involutive :
    Function.Involutive extendedReversal := by
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp [extendedReversal]
  | tmul coefficient carrier =>
      simp [extendedReversal, globalReversalLinear_involutive carrier]
  | add left right left_ih right_ih =>
      simp only [map_add, left_ih, right_ih]

/-- Universal action-kernel module over the already generated zero fibre. -/
abbrev UniversalKernel := LinearMap.ker universalEulerOperator

/-- The universal inclusion is a genuine submodule inclusion, not a selected
kernel element or a coordinate pair. -/
def universalInclusion : UniversalKernel →ₗ[ℤ] ScalarExtendedCarrier :=
  UniversalKernel.subtype

def kernelReversal : UniversalKernel →ₗ[ℤ] UniversalKernel :=
  LinearMap.codRestrict UniversalKernel
    (extendedReversal.comp UniversalKernel.subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun
        universalEulerOperator_reversal_commutes value.1
      change universalEulerOperator (extendedReversal value.1) = 0
      change universalEulerOperator (extendedReversal value.1) =
        extendedReversal (universalEulerOperator value.1) at square
      rw [LinearMap.mem_ker.mp value.2, map_zero] at square
      exact square)

theorem kernelReversal_involutive : Function.Involutive kernelReversal := by
  intro value
  apply Subtype.ext
  exact extendedReversal_involutive value.1

/-- Anti-invariant difference of an arbitrary universal kernel element. -/
def antiInvariantDifference (value : UniversalKernel) : UniversalKernel :=
  value - kernelReversal value

theorem kernelReversal_antiInvariantDifference (value : UniversalKernel) :
    kernelReversal (antiInvariantDifference value) =
      -antiInvariantDifference value := by
  unfold antiInvariantDifference
  rw [map_sub, kernelReversal_involutive]
  module

def universalKernelOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      (UniversalKernel →ₗ[ℤ] ScalarExtendedCarrier)) :=
  seedOccurrence.map fun owner => (owner, universalInclusion)

theorem universalKernelOccurrence_projects :
    universalKernelOccurrence.map Prod.fst = seedOccurrence := by
  unfold universalKernelOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_actual_action_reversal_and_universal_inclusion :
    universalKernelOccurrence.map Prod.fst = seedOccurrence ∧
      universalKernelOccurrence.root.2 = universalInclusion ∧
      Function.Involutive kernelReversal ∧
      (∀ value : UniversalKernel,
        kernelReversal (antiInvariantDifference value) =
          -antiInvariantDifference value) := by
  exact ⟨universalKernelOccurrence_projects, rfl,
    kernelReversal_involutive,
    kernelReversal_antiInvariantDifference⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerReversalEquivariantZeroFiber
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
