import H0mework.Fock.PrimeField.RecoveryModel
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Polynomial.Basis

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open Polynomial
noncomputable section

def program (polynomial : Polynomial ℤ) : SourceOperationNative.Carrier process :=
  aeval nativeAction polynomial (SourceOperationNative.point runtimeSeed)

theorem original_root : SourceOperationNative.point runtimeSeed = SourceOperationNative.statePoint process 0 :=
  congrArg (SourceOperationNative.statePoint process) (runtimeAt_state 0)

theorem program_add (left right : Polynomial ℤ) : program (left + right) = program left + program right := by
  unfold program
  rw [map_add]
  rfl

theorem program_monomial (index : Nat) (coefficient : ℤ) :
    program (monomial index coefficient) = Finsupp.single index coefficient := by
  unfold program
  rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, original_root,
    source_iterate, Nat.zero_add]
  simp only [SourceOperationNative.statePoint, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem program_coefficient (polynomial : Polynomial ℤ) (index : Nat) :
    program polynomial index = polynomial.coeff index := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftProof rightProof =>
      rw [program_add, Finsupp.add_apply, leftProof, rightProof, coeff_add]
  | monomial degree coefficient =>
      rw [program_monomial, Finsupp.single_apply, coeff_monomial]

def coefficients : Polynomial ℤ ≃ₗ[ℤ] SourceOperationNative.Carrier process :=
  (Polynomial.toFinsuppIsoLinear ℤ).trans (AddMonoidAlgebra.coeffLinearEquiv ℤ)

theorem program_is_coefficients (polynomial : Polynomial ℤ) : program polynomial = coefficients polynomial := by
  apply Finsupp.ext
  intro index
  exact program_coefficient polynomial index

theorem program_injective : Function.Injective program := by
  intro left right same
  exact coefficients.injective ((program_is_coefficients left).symm.trans
    (same.trans (program_is_coefficients right)))

theorem program_surjective : Function.Surjective program := by
  intro word
  exact ⟨coefficients.symm word, (program_is_coefficients _).trans (coefficients.apply_symm_apply word)⟩

theorem program_one : program 1 = SourceOperationNative.point runtimeSeed := by
  unfold program
  rw [map_one]
  rfl

theorem program_X_mul (polynomial : Polynomial ℤ) :
    program (X * polynomial) = nativeAction (program polynomial) := by
  unfold program
  rw [map_mul, aeval_X, Module.End.mul_apply]

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
