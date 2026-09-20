import H0mework.Arithmetic.EulerLocal.ZeroFibreLanding
import H0mework.Arithmetic.UnitArithmetic.Factorization

/-!
# Requested runtime prime-power landing

The universal-kernel coordinate landing is specialized to one actual
`RuntimePrimePowerFactorAt p k`.  Its support and exponent indices come from
the exact factorial-history occurrence; no numeric prime table or inverse
scalar is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerRuntimePrimePowerLanding

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerReversalEquivariantZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerZeroFiberLocalLanding

noncomputable section

variable {requestedPrime : Nat.Primes} {requestedExponent : Nat}

theorem stageHistory_eq_runtimeWholeHistory (stage : Nat) :
    StageHistory seedOccurrence.root stage = runtimeWholeHistory stage := by
  cases stage with
  | zero => rfl
  | succ stage => rfl

theorem castPrimeIndex_value
    {left right : ArithmeticGeneration.UnitHistory}
    (historyEquality : left = right) (index : PrimeIndex left) :
    (_root_.cast (congrArg PrimeIndex historyEquality) index :
      PrimeIndex right).1 = index.1 := by
  subst right
  rfl

def stagePrimeIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    StagePrime seedOccurrence.root factor.stage := by
  change PrimeIndex (StageHistory seedOccurrence.root factor.stage)
  exact _root_.cast
    (congrArg PrimeIndex
      (stageHistory_eq_runtimeWholeHistory factor.stage).symm)
    factor.primeIndex

@[simp] theorem stagePrimeIndex_value
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (stagePrimeIndex factor).1 = factor.primeIndex.1 := by
  unfold stagePrimeIndex
  exact castPrimeIndex_value
    (stageHistory_eq_runtimeWholeHistory factor.stage).symm
      factor.primeIndex

theorem stagePrimeIndex_multiplicity
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    CanonicalUnitArithmeticFactorizationOccurrence.multiplicity
        (StageHistory seedOccurrence.root factor.stage)
        (stagePrimeIndex factor) =
      CanonicalUnitArithmeticFactorizationOccurrence.multiplicity
        (runtimeWholeHistory factor.stage) factor.primeIndex := by
  unfold CanonicalUnitArithmeticFactorizationOccurrence.multiplicity
  rw [stagePrimeIndex_value, stageHistory_eq_runtimeWholeHistory]

def stageExponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    StageExponent seedOccurrence.root factor.stage (stagePrimeIndex factor) := by
  refine ⟨requestedExponent, ?_⟩
  have exponentBound := factor.exponentIndex.2
  have exponentValue := factor.exponent_eq
  change factor.exponentIndex.1 + 1 = requestedExponent at exponentValue
  rw [stagePrimeIndex_multiplicity]
  omega

theorem stagePrimeIndex_actualPrime
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (stageFactorization seedOccurrence.root factor.stage).actualPrime
        (stagePrimeIndex factor) = requestedPrime :=
  by
    apply Subtype.ext
    change (stagePrimeIndex factor).1 = requestedPrime.1
    rw [stagePrimeIndex_value]
    exact congrArg Subtype.val factor.prime_eq

def requestedComponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    LocalCoefficientRing factor.stage :=
  restrictedComponent factor.stage (stagePrimeIndex factor)
    (stageExponent factor) dualIndex value

def requestedDivisionRoot
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    LocalCoefficientRing factor.stage :=
  restrictedDivisionRoot factor.stage (stagePrimeIndex factor)
    dualIndex value

/-- Actual factorization-born requested landing. -/
theorem requestedComponent_eq_primePower_smul_root
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    requestedComponent factor dualIndex value =
      (requestedPrime : Nat) ^ requestedExponent •
        requestedDivisionRoot factor dualIndex value := by
  unfold requestedComponent requestedDivisionRoot
  rw [restrictedComponent_eq_primePower_smul_root]
  change
    (actualPrimeScalar seedOccurrence.root factor.stage
        (stagePrimeIndex factor) : ℤ) ^ requestedExponent • _ = _
  rw [actualPrimeScalar, stagePrimeIndex_actualPrime]
  rfl

theorem preserves_exact_runtime_factorization_and_requested_landing
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    factorialHistory (runtimeWholeHistory factor.stage) =
        (primePowerHistory factor.primeIndex factor.exponentIndex).joint
          (quotientHistory factor.primeIndex factor.exponentIndex) ∧
      requestedComponent factor dualIndex value =
        (requestedPrime : Nat) ^ requestedExponent •
          requestedDivisionRoot factor dualIndex value := by
  exact ⟨factor.actual_joint_landing,
    requestedComponent_eq_primePower_smul_root factor dualIndex value⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerRuntimePrimePowerLanding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
