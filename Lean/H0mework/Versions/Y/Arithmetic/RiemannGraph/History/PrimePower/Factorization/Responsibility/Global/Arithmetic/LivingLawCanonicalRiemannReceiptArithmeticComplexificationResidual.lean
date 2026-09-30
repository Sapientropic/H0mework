import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Cofiber.LivingLawCanonicalRiemannReceiptFactorizationCokernelSource
import H0mework.Versions.Y.Arithmetic.BlockSpecialization.CokernelGlobalOccurrence

/-!
# Integral arithmetic endpoint and its finite complexification residual

The existing global block action-cokernel class has a nonzero integral
arithmetic image.  At every finite stage a source-generated nonzero integer
determinant annihilates its endpoint class, so scalar extension to ℂ erases
that finite projection.  This is an exact tensor/limit representation
residual: the uncomplexified global class remains in the same receipt
occurrence and is not reclassified as zero.

No estimate, compatible family, descent, separator, finite generation, or
tensor/limit interchange is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open NoIslandNoMagic.CanonicalArithmeticState.BlockArithmeticSpecializationStage
open NoIslandNoMagic.CanonicalArithmeticState.BlockActionCokernelRead
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalTower
open NoIslandNoMagic.CanonicalArithmeticState.BlockCokernelGlobalOccurrence
open SourceGeneratedIntegralCoherentCompletion
open Cofinal
open Cofiber
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

theorem actualBlockSpecialization_blockDeterminantSection_ne_zero
    (stage : Nat) :
    actualBlockSpecialization
      (blockDeterminantSection seedOccurrence.root stage) ≠ 0 := by
  rw [blockDeterminantSection_eq_actual_product, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro primeIndex _membership
  rw [map_sub, map_pow, map_sub, map_one,
    actualBlockSpecialization_blockA,
    map_pow, actualBlockSpecialization_blockB]
  simp only [zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero]
  apply pow_ne_zero
  intro equality
  have primeOne : (((stageFactorization seedOccurrence.root stage).actualPrime
      primeIndex : Nat)) = 1 := by
    exact_mod_cast (sub_eq_zero.mp equality).symm
  exact ((stageFactorization seedOccurrence.root stage).actualPrime
    primeIndex).property.ne_one primeOne

theorem arithmeticDeterminant_smul_endpointClass_zero (stage : Nat) :
    actualBlockSpecialization
        (blockDeterminantSection seedOccurrence.root stage) •
      specializedIntegralEndpointBoundaryClass stage = 0 := by
  have mapped := congrArg
    (blockRelationActionCokernelArithmeticRead stage)
    (localEndpointBoundaryCokernelClass_determinant_zero stage)
  rw [map_zero] at mapped
  change blockRelationActionCokernelArithmeticRead stage
      (blockDeterminantSection seedOccurrence.root stage •
        localEndpointBoundaryCokernelClass stage) = 0 at mapped
  rw [(blockRelationActionCokernelArithmeticRead stage).map_smulₛₗ,
    blockRelationActionCokernelArithmeticRead_endpointClass] at mapped
  exact mapped

abbrev ComplexIntegralRelationOperatorCokernel (stage : Nat) :=
  ComplexifiedCarrier (IntegralRelationOperatorCokernel stage)

theorem complex_tmul_eq_zero_of_nonzero_int_annihilates
    {M : Type*} [AddCommGroup M]
    (coefficient : ℤ) (value : M)
    (coefficientNe : coefficient ≠ 0)
    (killed : coefficient • value = 0) :
    (1 : ℂ) ⊗ₜ[ℤ] value = 0 := by
  have coefficientCastNe : (coefficient : ℂ) ≠ 0 := by
    exact_mod_cast coefficientNe
  have determinantTensorZero :
      (coefficient : ℂ) ⊗ₜ[ℤ] value = 0 := by
    calc
      _ = (coefficient • (1 : ℂ)) ⊗ₜ[ℤ] value := by simp
      _ = (1 : ℂ) ⊗ₜ[ℤ] (coefficient • value) :=
            TensorProduct.smul_tmul _ _ _
      _ = 0 := by rw [killed, TensorProduct.tmul_zero]
  calc
    (1 : ℂ) ⊗ₜ[ℤ] value =
        ((coefficient : ℂ)⁻¹ * coefficient) ⊗ₜ[ℤ] value := by
            rw [inv_mul_cancel₀ coefficientCastNe]
    _ = (coefficient : ℂ)⁻¹ •
        ((coefficient : ℂ) ⊗ₜ[ℤ] value) := by
            rw [TensorProduct.smul_tmul']
            rfl
    _ = 0 := by rw [determinantTensorZero, smul_zero]

theorem complexifiedIntegralEndpointBoundaryClass_zero (stage : Nat) :
    (1 : ℂ) ⊗ₜ[ℤ] specializedIntegralEndpointBoundaryClass stage = 0 :=
  complex_tmul_eq_zero_of_nonzero_int_annihilates
    (actualBlockSpecialization
      (blockDeterminantSection seedOccurrence.root stage))
    (specializedIntegralEndpointBoundaryClass stage)
    (actualBlockSpecialization_blockDeterminantSection_ne_zero stage)
    (arithmeticDeterminant_smul_endpointClass_zero stage)

theorem globalArithmeticEndpoint_complexLocalRead_zero (stage : Nat) :
    (1 : ℂ) ⊗ₜ[ℤ]
      (limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op stage)).hom
          globalSpecializedIntegralEndpointBoundaryClass = 0 := by
  apply complex_tmul_eq_zero_of_nonzero_int_annihilates
    (actualBlockSpecialization
      (blockDeterminantSection seedOccurrence.root stage))
  · exact actualBlockSpecialization_blockDeterminantSection_ne_zero stage
  · rw [globalSpecializedIntegralEndpointBoundaryClass_restriction]
    exact arithmeticDeterminant_smul_endpointClass_zero stage

structure ArithmeticCokernelFiniteComplexificationResidual : Type where
  globalClass : RestrictedArithmeticGlobalCokernel
  globalClass_ne_zero : globalClass ≠ 0
  every_complexLocalRead_zero : ∀ stage,
    (1 : ℂ) ⊗ₜ[ℤ]
      (limit.π restrictedArithmeticCokernelDiagram
        (Opposite.op stage)).hom globalClass = 0

def globalArithmeticEndpointFiniteComplexificationResidual :
    ArithmeticCokernelFiniteComplexificationResidual where
  globalClass := globalSpecializedIntegralEndpointBoundaryClass
  globalClass_ne_zero := globalSpecializedIntegralEndpointBoundaryClass_ne_zero
  every_complexLocalRead_zero :=
    globalArithmeticEndpoint_complexLocalRead_zero

def zeroOwnedReceiptArithmeticResidualOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  (receiptCofinalFace observation nontrivial).root.map fun source =>
    (source, globalArithmeticEndpointFiniteComplexificationResidual)

theorem zeroOwnedReceiptArithmeticResidualOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedReceiptArithmeticResidualOccurrence observation nontrivial).map
        Prod.fst =
      (receiptCofinalFace observation nontrivial).root := by
  unfold zeroOwnedReceiptArithmeticResidualOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (receiptCofinalFace observation nontrivial).root.map id = _
  exact RootedAccountedUnfolding.map_id _

theorem globalSpecializedIntegralEndpointBoundaryOccurrence_projects_seed :
    globalSpecializedIntegralEndpointBoundaryOccurrence.map
        (fun payload => payload.1.1) = seedOccurrence := by
  calc
    _ = (globalSpecializedIntegralEndpointBoundaryOccurrence.map Prod.fst).map
        Prod.fst := by
      rw [RootedAccountedUnfolding.map_map]
      congr 1
    _ = globalEndpointBoundaryCokernelOccurrence.map Prod.fst := by
      rw [globalSpecializedIntegralEndpointBoundaryOccurrence_projects]
    _ = seedOccurrence := globalEndpointBoundaryCokernelOccurrence_projects

theorem receiptCofinalFace_globalSpecializedArithmetic_same_seed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((((((((receiptCofinalFace observation nontrivial).root.map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst =
      globalSpecializedIntegralEndpointBoundaryOccurrence.map
        (fun payload => payload.1.1) := by
  rw [receiptCofinalFace_projects_seed,
    globalSpecializedIntegralEndpointBoundaryOccurrence_projects_seed]

structure ZeroOwnedReceiptArithmeticComplexificationResidualCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Type where
  occurrence_projects : type_of%
    (zeroOwnedReceiptArithmeticResidualOccurrence_projects
      observation nontrivial)
  global_integral_class_ne_zero :
    globalSpecializedIntegralEndpointBoundaryClass ≠ 0
  every_finite_complexification_zero : ∀ stage,
    type_of% (globalArithmeticEndpoint_complexLocalRead_zero stage)
  shared_factorization_seed : type_of%
    (receiptCofinalFace_globalSpecializedArithmetic_same_seed
      observation nontrivial)

def generateZeroOwnedReceiptArithmeticComplexificationResidualCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ZeroOwnedReceiptArithmeticComplexificationResidualCertificate
      observation nontrivial where
  occurrence_projects :=
    zeroOwnedReceiptArithmeticResidualOccurrence_projects observation nontrivial
  global_integral_class_ne_zero :=
    globalSpecializedIntegralEndpointBoundaryClass_ne_zero
  every_finite_complexification_zero :=
    globalArithmeticEndpoint_complexLocalRead_zero
  shared_factorization_seed :=
    receiptCofinalFace_globalSpecializedArithmetic_same_seed
      observation nontrivial

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Arithmetic
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
