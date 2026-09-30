import Mathlib.LinearAlgebra.TensorProduct.Map
import H0mework.Versions.X.Arithmetic.EulerGlobal.ReversalZeroFibre

/-!
# Integral local landing from the universal determinant kernel

An arbitrary element of the universal action kernel is restricted along the
framework-generated global zero-fibre and full-Euler carrier cones.  Reading
one actual prime/exponent coordinate then uses the integral Euler recurrence

`v(p,k,d) = p^k * v(p,0,d)`

to produce the requested multiplication-range relation.  No rational inverse
or chosen division root appears; the exponent-zero coordinate is the actual
root material that the generic quotient kernel will later extract.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerZeroFiberLocalLanding

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerReversalEquivariantZeroFiber
open CategoryTheory.Limits

noncomputable section

abbrev LocalCoefficientRing (stage : Nat) :=
  AdjoinRoot
    (GlobalDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial

abbrev LocalCarrier (stage : Nat) :=
  Carrier seedOccurrence.root stage

abbrev LocalScalarCarrier (stage : Nat) :=
  TensorProduct ℤ (LocalCoefficientRing stage) (LocalCarrier stage)

def coefficientRestriction (stage : Nat) :
    CoefficientRing →ₗ[ℤ] LocalCoefficientRing stage :=
  (limit.π GlobalZeroFiberDiagram
    (Opposite.op stage)).hom.toAddMonoidHom.toIntLinearMap

def carrierRestriction (stage : Nat) :
    GlobalCarrier →ₗ[ℤ] LocalCarrier stage :=
  (CanonicalUnitArithmeticFactorizationFullEulerGlobalAction.globalRestriction
    (Opposite.op stage)).f 0 |>.hom

def localTensorRestriction (stage : Nat) :
    ScalarExtendedCarrier →ₗ[ℤ] LocalScalarCarrier stage :=
  TensorProduct.map (coefficientRestriction stage)
    (carrierRestriction stage)

def carrierCoordinate (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) : LocalCarrier stage →ₗ[ℤ] ℤ where
  toFun value := value.1 ⟨primeIndex, localExponent, dualIndex⟩
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def localCoordinate (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) :
    LocalScalarCarrier stage →ₗ[ℤ] LocalCoefficientRing stage :=
  (TensorProduct.rid ℤ (LocalCoefficientRing stage)).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      (carrierCoordinate stage primeIndex localExponent dualIndex))

theorem carrierCoordinate_primePower
    (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) :
    carrierCoordinate stage primeIndex localExponent dualIndex =
      (actualPrimeScalar seedOccurrence.root stage primeIndex : ℤ) ^
          localExponent.1 •
        carrierCoordinate stage primeIndex
          (exponentZero seedOccurrence.root stage primeIndex) dualIndex := by
  apply LinearMap.ext
  intro value
  change value.1 ⟨primeIndex, localExponent, dualIndex⟩ =
    (actualPrimeScalar seedOccurrence.root stage primeIndex : ℤ) ^
        localExponent.1 *
      value.1 ⟨primeIndex,
        exponentZero seedOccurrence.root stage primeIndex, dualIndex⟩
  exact carrier_value_at_nat seedOccurrence.root stage value
    primeIndex dualIndex localExponent.1 localExponent.2

theorem localCoordinate_primePower_landing
    (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) (value : LocalScalarCarrier stage) :
    localCoordinate stage primeIndex localExponent dualIndex value =
      (actualPrimeScalar seedOccurrence.root stage primeIndex : ℤ) ^
          localExponent.1 •
        localCoordinate stage primeIndex
          (exponentZero seedOccurrence.root stage primeIndex)
          dualIndex value := by
  change ((TensorProduct.rid ℤ (LocalCoefficientRing stage)).toLinearMap.comp
      (TensorProduct.map LinearMap.id
        (carrierCoordinate stage primeIndex localExponent dualIndex))) value = _
  rw [carrierCoordinate_primePower,
    TensorProduct.map_smul_right, LinearMap.comp_smul]
  rfl

def localRestrictedKernelValue (stage : Nat) (value : UniversalKernel) :
    LocalScalarCarrier stage :=
  localTensorRestriction stage (universalInclusion value)

def localRestrictedDifference (stage : Nat) (value : UniversalKernel) :
    LocalScalarCarrier stage :=
  localTensorRestriction stage
    (universalInclusion (antiInvariantDifference value))

def restrictedComponent (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    LocalCoefficientRing stage :=
  localCoordinate stage primeIndex localExponent dualIndex
    (localRestrictedDifference stage value)

def restrictedDivisionRoot (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    LocalCoefficientRing stage :=
  localCoordinate stage primeIndex
    (exponentZero seedOccurrence.root stage primeIndex) dualIndex
    (localRestrictedDifference stage value)

/-- The sole element-level domain feed: an actual exponent occurrence gives
an integral `p^k` multiplication row for the universal anti-invariant
difference restriction. -/
theorem restrictedComponent_eq_primePower_smul_root
    (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    restrictedComponent stage primeIndex localExponent dualIndex value =
      (actualPrimeScalar seedOccurrence.root stage primeIndex : ℤ) ^
          localExponent.1 •
        restrictedDivisionRoot stage primeIndex dualIndex value :=
  localCoordinate_primePower_landing stage primeIndex localExponent dualIndex
    (localRestrictedDifference stage value)

theorem preserves_universal_kernel_and_actual_factorization_coordinate
    (stage : Nat)
    (primeIndex : StagePrime seedOccurrence.root stage)
    (localExponent : StageExponent seedOccurrence.root stage primeIndex)
    (dualIndex : Fin 2) (value : UniversalKernel) :
    universalKernelOccurrence.map Prod.fst = seedOccurrence ∧
      (GlobalDeterminantSectionDiagram.obj
        (Opposite.op stage)).polynomial =
          determinantPolynomial seedOccurrence.root stage ∧
      restrictedComponent stage primeIndex localExponent dualIndex value =
        (actualPrimeScalar seedOccurrence.root stage primeIndex : ℤ) ^
            localExponent.1 •
          restrictedDivisionRoot stage primeIndex dualIndex value := by
  exact ⟨universalKernelOccurrence_projects,
    globalSection_local_restriction stage,
    restrictedComponent_eq_primePower_smul_root
      stage primeIndex localExponent dualIndex value⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerZeroFiberLocalLanding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
