import Mathlib.RingTheory.Flat.Equalizer
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiberFlatness
import H0mework.Versions.R2.Arithmetic.EulerGlobal.CofiberCofinalRigidity

/-!
# Generated universal solution fixedness on the q-rich whole relation source

The universal coefficient layer is installed only after the actual integral
whole-relation cocycle has retained its whole and quotient roles.  The
generated action kernel therefore consists of coefficientwise integral
cocycles satisfying the existing `1-rF` equation.  Frozen prime-power
rigidity has already killed the integral anti-invariant component, and tensor
functoriality carries that same zero to every generated coefficientwise
solution.

No finite presentation of the coefficient ring, scalar division root,
selected point, endpoint law, or fixedness premise occurs here.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholeRelationGeneratedUniversalSolutionFixedness

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticIntegralActionCofiberCofinalRigidity
open scoped TensorProduct

noncomputable section

/-- Coefficients are attached to the already generated integral global
cocycle, whose source still contains every actual quotient role. -/
abbrev GeneratedCocycleCarrier := IntegralScalarCocycleCarrier

def generatedActionOperator :
    GeneratedCocycleCarrier →ₗ[ℤ] ScalarVertex :=
  universalEulerOperator.comp integralScalarCocycleInclusion

/-- The common determinant-zero action condition on the same q-rich source. -/
abbrev GeneratedUniversalSolutionCarrier :=
  LinearMap.ker generatedActionOperator

def generatedUniversalInclusion :
    GeneratedUniversalSolutionCarrier →ₗ[ℤ] ScalarVertex :=
  integralScalarCocycleInclusion.comp
    GeneratedUniversalSolutionCarrier.subtype

theorem generatedUniversalInclusion_differential_zero
    (value : GeneratedUniversalSolutionCarrier) :
    extendedDifferential (generatedUniversalInclusion value) = 0 :=
  integralScalarCocycleInclusion_differential_zero value.1

theorem generatedUniversalInclusion_action_zero
    (value : GeneratedUniversalSolutionCarrier) :
    universalEulerOperator (generatedUniversalInclusion value) = 0 :=
  LinearMap.mem_ker.mp value.2

def localGeneratedUniversalAntiInvariant (stage : Nat) :
    GeneratedUniversalSolutionCarrier →ₗ[ℤ] LocalScalarInner stage :=
  (localWholeAntiInvariantComponent stage).comp
    ((localTensorRestriction stage).comp generatedUniversalInclusion)

/-- The same coefficientwise universal solution is killed by the frozen
integral local-process consumer; the coefficient layer contributes no new
division argument. -/
theorem localGeneratedUniversalAntiInvariant_eq_zero
    (stage : Nat) (value : GeneratedUniversalSolutionCarrier) :
    localGeneratedUniversalAntiInvariant stage value = 0 := by
  exact integralScalarTautologicalAntiInvariant_eq_zero stage value.1

/-- The framework-owned tautological cofiber readback is evaluated on that
same generated q-rich solution, rather than paired with an independent
endpoint value. -/
theorem localGeneratedUniversalTautologicalReadback_eq_zero
    (stage : Nat) (value : GeneratedUniversalSolutionCarrier) :
    localTautologicalAntiInvariantReadback stage
        (generatedUniversalInclusion value)
        (generatedUniversalInclusion_differential_zero value) = 0 := by
  rw [localTautologicalAntiInvariantReadback_eq_component]
  have fixed := localGeneratedUniversalAntiInvariant_eq_zero stage value
  change localWholeAntiInvariantComponent stage
      (localTensorRestriction stage (generatedUniversalInclusion value)) = 0
    at fixed
  rw [fixed]
  simp

/-! ## Flat base change identifies the entire universal cocycle kernel -/

/-- This spelling retains the kernel's native submodule action.  It avoids
silently replacing that action with the propositionally equal canonical
integer module while applying the generic tensor-kernel equivalence. -/
abbrev NativeIntegralScalarCocycleCarrier :=
  @TensorProduct ℤ _ CoefficientRing (LinearMap.ker globalDifferential)
    _ _ _ globalDifferential.ker.module

abbrev TensorCocycleKernel :=
  LinearMap.ker
    (TensorProduct.AlgebraTensorModule.lTensor CoefficientRing CoefficientRing
      globalDifferential)

theorem extendedDifferential_eq_lTensor :
    extendedDifferential =
      TensorProduct.AlgebraTensorModule.lTensor CoefficientRing CoefficientRing
        globalDifferential := by
  apply LinearMap.ext
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient vertex => rfl
  | add left right leftHypothesis rightHypothesis =>
      simp [leftHypothesis, rightHypothesis]

noncomputable def scalarCocycleEquiv :
    NativeIntegralScalarCocycleCarrier ≃ₗ[CoefficientRing]
      TensorCocycleKernel :=
  LinearMap.tensorKerEquiv CoefficientRing CoefficientRing globalDifferential

noncomputable def cocycleToNativeIntegralScalar (value : CocycleKernel) :
    NativeIntegralScalarCocycleCarrier :=
  scalarCocycleEquiv.symm
    (⟨value.1, by
      rw [LinearMap.mem_ker]
      have zero := LinearMap.mem_ker.mp value.2
      rw [extendedDifferential_eq_lTensor] at zero
      exact zero⟩ : TensorCocycleKernel)

def nativeIntegralScalarInclusion :
    NativeIntegralScalarCocycleCarrier →ₗ[ℤ] ScalarVertex :=
  (TensorCocycleKernel.subtype.restrictScalars ℤ).comp
    (scalarCocycleEquiv.toLinearMap.restrictScalars ℤ)

theorem cocycleToNativeIntegralScalar_inclusion (value : CocycleKernel) :
    nativeIntegralScalarInclusion
        (cocycleToNativeIntegralScalar value) = value.1 := by
  let target : TensorCocycleKernel := ⟨value.1, by
    rw [LinearMap.mem_ker]
    have zero := LinearMap.mem_ker.mp value.2
    rw [extendedDifferential_eq_lTensor] at zero
    exact zero⟩
  have equality := LinearEquiv.apply_symm_apply scalarCocycleEquiv target
  change (scalarCocycleEquiv (scalarCocycleEquiv.symm target)).1 = value.1
  exact congrArg Subtype.val equality

theorem nativeIntegralScalar_localAntiInvariant_eq_zero
    (stage : Nat) (value : NativeIntegralScalarCocycleCarrier) :
    localWholeAntiInvariantComponent stage
        (localTensorRestriction stage
          (nativeIntegralScalarInclusion value)) = 0 := by
  letI : Module ℤ (LinearMap.ker globalDifferential) :=
    globalDifferential.ker.module
  induction value using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient integral =>
      rw [show nativeIntegralScalarInclusion
          (coefficient ⊗ₜ[ℤ] integral) =
            coefficient ⊗ₜ[ℤ] (integral : GlobalVertex) by
        change (scalarCocycleEquiv (coefficient ⊗ₜ[ℤ] integral) :
          TensorCocycleKernel).1 = _
        unfold scalarCocycleEquiv
        rw [LinearMap.tensorKerEquiv_apply]
        rfl]
      change (coefficientRestriction stage coefficient) ⊗ₜ[ℤ]
          localIntegralWholeAntiInvariant stage integral = 0
      rw [everyLocalIntegralWholeAntiInvariant_eq_zero,
        TensorProduct.tmul_zero]
  | add left right leftHypothesis rightHypothesis =>
      simp only [map_add, leftHypothesis, rightHypothesis, add_zero]

/-- Frozen integral rigidity already kills every global factorization
cocycle after flat coefficient extension.  The determinant-action kernel is
needed to select the zeta zero fibre, not to manufacture the arithmetic
anti-invariant vanishing. -/
theorem cocycle_localAntiInvariant_eq_zero
    (stage : Nat) (value : CocycleKernel) :
    localWholeAntiInvariantComponent stage
        (localTensorRestriction stage value.1) = 0 := by
  rw [← cocycleToNativeIntegralScalar_inclusion value]
  exact nativeIntegralScalar_localAntiInvariant_eq_zero stage
    (cocycleToNativeIntegralScalar value)

theorem cocycle_tautologicalReadback_eq_zero
    (stage : Nat) (value : CocycleKernel) :
    localTautologicalAntiInvariantReadback stage value.1
        (LinearMap.mem_ker.mp value.2) = 0 := by
  rw [localTautologicalAntiInvariantReadback_eq_component,
    cocycle_localAntiInvariant_eq_zero]
  simp

/-- Flatness of the generated zero-fibre coefficient ring promotes the
already frozen integral theorem to every element of the actual universal
solution kernel. -/
theorem universalSolution_localAntiInvariant_eq_zero
    (stage : Nat) (value : UniversalSolutionKernel) :
    localWholeAntiInvariantComponent stage
        (localTensorRestriction stage (universalInclusion value)) = 0 := by
  let cocycle : CocycleKernel := ⟨value.1, value.2.1⟩
  change localWholeAntiInvariantComponent stage
      (localTensorRestriction stage value.1) = 0
  rw [← cocycleToNativeIntegralScalar_inclusion cocycle]
  exact nativeIntegralScalar_localAntiInvariant_eq_zero stage
    (cocycleToNativeIntegralScalar cocycle)

theorem universalSolution_tautologicalReadback_eq_zero
    (stage : Nat) (value : UniversalSolutionKernel) :
    localTautologicalAntiInvariantReadback stage
        (universalInclusion value)
        (LinearMap.mem_ker.mp value.2.1) = 0 := by
  rw [localTautologicalAntiInvariantReadback_eq_component]
  rw [universalSolution_localAntiInvariant_eq_zero]
  simp

def generatedUniversalSolutionOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      (GeneratedUniversalSolutionCarrier →ₗ[ℤ] ScalarVertex)) :=
  seedOccurrence.map fun owner => (owner, generatedUniversalInclusion)

theorem generatedUniversalSolutionOccurrence_projects :
    generatedUniversalSolutionOccurrence.map Prod.fst = seedOccurrence := by
  unfold generatedUniversalSolutionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_exact_root_q_rich_source_action_and_fixedness
    (stage : Nat) (value : GeneratedUniversalSolutionCarrier) :
    generatedUniversalSolutionOccurrence.map Prod.fst = seedOccurrence ∧
      extendedDifferential (generatedUniversalInclusion value) = 0 ∧
      universalEulerOperator (generatedUniversalInclusion value) = 0 ∧
      localGeneratedUniversalAntiInvariant stage value = 0 ∧
      localTautologicalAntiInvariantReadback stage
          (generatedUniversalInclusion value)
          (generatedUniversalInclusion_differential_zero value) = 0 :=
  ⟨generatedUniversalSolutionOccurrence_projects,
    generatedUniversalInclusion_differential_zero value,
    generatedUniversalInclusion_action_zero value,
    localGeneratedUniversalAntiInvariant_eq_zero stage value,
    localGeneratedUniversalTautologicalReadback_eq_zero stage value⟩

end
end CanonicalUnitArithmeticFactorizationWholeRelationGeneratedUniversalSolutionFixedness
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
