import H0mework.Versions.Y.Arithmetic.EulerGlobal.WholeUniversalSolution

/-!
# Local factorization landing of the universal whole solution

The universal state is first restricted along the generated zero-fibre cone
and the generated global relation-complex cone.  Its cocycle membership then
forces every actual factorization row

`whole = p^k * quotient`

on the entire whole slot.  This is not an exponent coordinate recurrence and
does not use a presentation quotient or a division root.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

abbrev LocalCoefficientRing (stage : Nat) :=
  AdjoinRoot
    (GlobalDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial

abbrev LocalVertex (stage : Nat) :=
  WholeVertexModule seedOccurrence.root stage

abbrev LocalRelation (stage : Nat) :=
  WholeRelationModule seedOccurrence.root stage

abbrev LocalScalarVertex (stage : Nat) :=
  TensorProduct ℤ (LocalCoefficientRing stage) (LocalVertex stage)

abbrev LocalScalarRelation (stage : Nat) :=
  TensorProduct ℤ (LocalCoefficientRing stage) (LocalRelation stage)

abbrev LocalScalarInner (stage : Nat) :=
  TensorProduct ℤ (LocalCoefficientRing stage)
    (InnerCarrier seedOccurrence.root stage)

def coefficientRestriction (stage : Nat) :
    CoefficientRing →ₗ[ℤ] LocalCoefficientRing stage :=
  (limit.π GlobalZeroFiberDiagram (Opposite.op stage)).hom
    |>.toAddMonoidHom.toIntLinearMap

def vertexRestriction (stage : Nat) :
    GlobalVertex →ₗ[ℤ] LocalVertex stage :=
  (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalRestriction
    (Opposite.op stage)).f 0 |>.hom

def relationRestriction (stage : Nat) :
    GlobalRelation →ₗ[ℤ] LocalRelation stage :=
  (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalRestriction
    (Opposite.op stage)).f 1 |>.hom

def localTensorRestriction (stage : Nat) :
    ScalarVertex →ₗ[ℤ] LocalScalarVertex stage :=
  TensorProduct.map (coefficientRestriction stage) (vertexRestriction stage)

def localRelationTensorRestriction (stage : Nat) :
    ScalarRelation →ₗ[ℤ] LocalScalarRelation stage :=
  TensorProduct.map (coefficientRestriction stage) (relationRestriction stage)

def localExtendedDifferential (stage : Nat) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarRelation stage :=
  TensorProduct.map LinearMap.id
    (factorizationDifferential seedOccurrence.root stage)

theorem globalRestriction_differential_square (stage : Nat) :
    (factorizationDifferential seedOccurrence.root stage).comp
        (vertexRestriction stage) =
      (relationRestriction stage).comp globalDifferential := by
  have square :=
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction.globalRestriction
      (Opposite.op stage)).comm 0 1
  exact congrArg (fun arrow => arrow.hom) square

theorem localTensorRestriction_differential_square (stage : Nat) :
    (localExtendedDifferential stage).comp (localTensorRestriction stage) =
      (localRelationTensorRestriction stage).comp extendedDifferential := by
  rw [localExtendedDifferential, localTensorRestriction,
    localRelationTensorRestriction, extendedDifferential,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro value
    rfl
  · exact globalRestriction_differential_square stage

def localRestrictedValue (stage : Nat) (value : UniversalSolutionKernel) :
    LocalScalarVertex stage :=
  localTensorRestriction stage (universalInclusion value)

theorem localRestrictedValue_cocycle (stage : Nat)
    (value : UniversalSolutionKernel) :
    localExtendedDifferential stage (localRestrictedValue stage value) = 0 := by
  have square := LinearMap.congr_fun
    (localTensorRestriction_differential_square stage)
      (universalInclusion value)
  change localExtendedDifferential stage (localRestrictedValue stage value) =
    localRelationTensorRestriction stage
      (extendedDifferential (universalInclusion value)) at square
  have cocycleZero : extendedDifferential (universalInclusion value) = 0 :=
    LinearMap.mem_ker.mp value.2.1
  rw [cocycleZero, map_zero] at square
  exact square

def wholeProjection (stage : Nat) :
    LocalVertex stage →ₗ[ℤ] InnerCarrier seedOccurrence.root stage where
  toFun value := value none
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def quotientProjection (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalVertex stage →ₗ[ℤ] InnerCarrier seedOccurrence.root stage where
  toFun value := value (some row)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def relationRowProjection (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalRelation stage →ₗ[ℤ] InnerCarrier seedOccurrence.root stage where
  toFun value := value row
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def localWholeComponent (stage : Nat) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarInner stage :=
  TensorProduct.map LinearMap.id (wholeProjection stage)

def localQuotientComponent (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarInner stage :=
  TensorProduct.map LinearMap.id (quotientProjection stage row)

def wholeAntiInvariantProjection (stage : Nat) :
    LocalVertex stage →ₗ[ℤ] InnerCarrier seedOccurrence.root stage :=
  (innerAntiInvariant seedOccurrence.root stage).comp (wholeProjection stage)

def quotientAntiInvariantProjection (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalVertex stage →ₗ[ℤ] InnerCarrier seedOccurrence.root stage :=
  (innerAntiInvariant seedOccurrence.root stage).comp
    (quotientProjection stage row)

def localWholeAntiInvariantComponent (stage : Nat) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarInner stage :=
  TensorProduct.map LinearMap.id (wholeAntiInvariantProjection stage)

def localQuotientAntiInvariantComponent (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarInner stage :=
  TensorProduct.map LinearMap.id (quotientAntiInvariantProjection stage row)

def localRelationRow (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalScalarRelation stage →ₗ[ℤ] LocalScalarInner stage :=
  TensorProduct.map LinearMap.id (relationRowProjection stage row)

theorem localRelationRow_differential
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : LocalScalarVertex stage) :
    localRelationRow stage row (localExtendedDifferential stage value) =
      localWholeAntiInvariantComponent stage value -
        (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
          localQuotientAntiInvariantComponent stage row value := by
  induction value using TensorProduct.induction_on with
  | zero => simp
  | tmul coefficient vertex =>
      change coefficient ⊗ₜ[ℤ]
          (factorizationDifferential seedOccurrence.root stage vertex row) =
        coefficient ⊗ₜ[ℤ]
            innerAntiInvariant seedOccurrence.root stage (vertex none) -
          (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
            (coefficient ⊗ₜ[ℤ]
              innerAntiInvariant seedOccurrence.root stage (vertex (some row)))
      simp [factorizationDifferential, wholeValue, quotientValue,
        TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  | add left right left_ih right_ih =>
      simp only [map_add, left_ih, right_ih]
      module

/-- Anti-invariant whole-slot landing generated from cocycle membership. -/
theorem localWholeAntiInvariant_eq_primePower_smul_quotient
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : UniversalSolutionKernel) :
    localWholeAntiInvariantComponent stage (localRestrictedValue stage value) =
      (rowPrime row : Nat) ^ rowExponent row •
        localQuotientAntiInvariantComponent stage row
          (localRestrictedValue stage value) := by
  have relationEquation := localRelationRow_differential stage row
    (localRestrictedValue stage value)
  rw [localRestrictedValue_cocycle, map_zero] at relationEquation
  change 0 = _ - _ at relationEquation
  change localWholeAntiInvariantComponent stage
      (localRestrictedValue stage value) =
    (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
      localQuotientAntiInvariantComponent stage row
        (localRestrictedValue stage value)
  exact sub_eq_zero.mp relationEquation.symm

def localRestrictedDifference (stage : Nat)
    (value : UniversalSolutionKernel) : LocalScalarVertex stage :=
  localRestrictedValue stage (antiInvariantDifference value)

theorem localDifferenceAntiInvariant_eq_primePower_smul_quotient
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : UniversalSolutionKernel) :
    localWholeAntiInvariantComponent stage
        (localRestrictedDifference stage value) =
      (rowPrime row : Nat) ^ rowExponent row •
        localQuotientAntiInvariantComponent stage row
          (localRestrictedDifference stage value) :=
  localWholeAntiInvariant_eq_primePower_smul_quotient stage row
    (antiInvariantDifference value)

theorem preserves_same_universal_solution_and_actual_antiInvariant_landing
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : UniversalSolutionKernel) :
    universalSolutionOccurrence.map Prod.fst = seedOccurrence ∧
      localExtendedDifferential stage (localRestrictedDifference stage value) = 0 ∧
      localWholeAntiInvariantComponent stage
          (localRestrictedDifference stage value) =
        (rowPrime row : Nat) ^ rowExponent row •
          localQuotientAntiInvariantComponent stage row
            (localRestrictedDifference stage value) := by
  exact ⟨universalSolutionOccurrence_projects,
    localRestrictedValue_cocycle stage (antiInvariantDifference value),
    localDifferenceAntiInvariant_eq_primePower_smul_quotient stage row value⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
