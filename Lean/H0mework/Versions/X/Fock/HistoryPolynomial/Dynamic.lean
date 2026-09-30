import H0mework.Versions.X.Fock.HistoryPolynomial.Program
import Mathlib.RingTheory.Polynomial.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Polynomial
noncomputable section

abbrev DynamicSource := Module.AEval' nativeAction

def retained : SourceOperationNative.Carrier process ≃ₗ[ℤ] DynamicSource := Module.AEval'.of nativeAction

private theorem action_coefficients (word : SourceOperationNative.Carrier process) :
    coefficients.symm (nativeAction word) = X * coefficients.symm word := by
  apply coefficients.injective
  rw [coefficients.apply_symm_apply, ← program_is_coefficients, program_X_mul,
    program_is_coefficients, coefficients.apply_symm_apply]

def polynomialEquiv : DynamicSource ≃ₗ[Polynomial ℤ] Polynomial ℤ :=
  LinearEquiv.ofAEval nativeAction coefficients.symm (fun word => action_coefficients word)

theorem polynomial_program (polynomial : Polynomial ℤ) : polynomialEquiv (retained (program polynomial)) = polynomial := by
  change coefficients.symm (program polynomial) = polynomial
  rw [program_is_coefficients, coefficients.symm_apply_apply]

def generator : DynamicSource := retained (SourceOperationNative.point runtimeSeed)

theorem generator_is_one : polynomialEquiv generator = 1 := by
  rw [generator, ← program_one]
  exact polynomial_program 1

theorem program_is_action (polynomial : Polynomial ℤ) : retained (program polynomial) = polynomial • generator :=
  Module.AEval.of_aeval_smul nativeAction polynomial (SourceOperationNative.point runtimeSeed)

theorem X_is_native (word : SourceOperationNative.Carrier process) :
    (X : Polynomial ℤ) • retained word = retained (nativeAction word) :=
  Module.AEval'.X_smul_of nativeAction word

theorem single_generator (word : DynamicSource) : ∃! polynomial : Polynomial ℤ, polynomial • generator = word := by
  refine ⟨polynomialEquiv word, ?_, ?_⟩
  · apply polynomialEquiv.injective
    rw [map_smul, generator_is_one]
    exact mul_one _
  · intro polynomial generated
    have exactRead := congrArg polynomialEquiv generated
    simpa only [map_smul, generator_is_one, smul_eq_mul, mul_one] using exactRead

instance finite_polynomial : Module.Finite (Polynomial ℤ) DynamicSource :=
  Module.Finite.equiv polynomialEquiv.symm

instance noetherian_polynomial : IsNoetherian (Polynomial ℤ) DynamicSource := inferInstance

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
