import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import H0mework.Arithmetic.UnitArithmetic.PrimePowerIncidence
import H0mework.Realization.Completion.PrimePowerQuotient
import H0mework.Foundation.Relations.FiniteDefectDeterminant

/-!
# Coordinate-free canonical unit arithmetic common carrier

The exact unit-root occurrence generates its finite Euler prefix by folding
the actual `UnitHistory`: each new unit exposes the next canonical prime-local
factor.  The same source point generates the reversal boundary presentation,
its cokernel, and the rooted generic prime-power quotient face.

No complex coordinate, zeta zero, global Euler coefficient table, evaluator
table, division root, kernel-zero result, determinant, or coverage witness is
accepted by this producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCommonCarrier

open ArithmeticGeneration
open AdditiveFamilyFaithfulRealization
open AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt
open CanonicalUnitArithmeticPrimePowerIncidence
open CanonicalUnitArithmeticRoot
open FiniteDefectDeterminant
open Polynomial
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt
open RootArithmeticUnfoldingFace

noncomputable section

/-! ## Unit-history-generated finite Euler prefix -/

/-- The prime restriction born at one unit stage.  The source stores only the
stage history; primality is a downstream theorem of canonical enumeration. -/
def primeAtStage (stage : Nat) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime stage, Nat.prime_nth_prime stage⟩

def stageOfPrime (prime : Nat.Primes) : Nat :=
  Nat.count Nat.Prime prime

@[simp] theorem primeAtStage_stageOfPrime (prime : Nat.Primes) :
    primeAtStage (stageOfPrime prime) = prime := by
  apply Subtype.ext
  exact Nat.nth_count prime.property

def sourceLocalZetaPolynomial (_prime : Nat.Primes) : Polynomial ℤ :=
  1 - X

noncomputable def sourceLocalZetaPowerSeries (prime : Nat.Primes) :
    PowerSeries ℤ :=
  PowerSeries.invOfUnit
    (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) 1

noncomputable def sourceLocalFormalEulerFactor (prime : Nat.Primes) :
    ArithmeticFunction ℤ :=
  ArithmeticFunction.ofPowerSeries (prime : Nat)
    (sourceLocalZetaPowerSeries prime)

theorem sourceLocalZetaPowerSeries_eq_mk_one (prime : Nat.Primes) :
    sourceLocalZetaPowerSeries prime = PowerSeries.mk 1 := by
  have constantTerm :
      PowerSeries.constantCoeff
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) = 1 := by
    simp [sourceLocalZetaPolynomial]
  have inverseLaw :
      PowerSeries.invOfUnit
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) 1 *
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) = 1 :=
    PowerSeries.invOfUnit_mul _ 1 constantTerm
  have geometricLaw :
      (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) *
          PowerSeries.mk 1 = 1 := by
    simpa [sourceLocalZetaPolynomial, mul_comm] using
      PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  rw [sourceLocalZetaPowerSeries]
  calc
    PowerSeries.invOfUnit
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) 1 =
        PowerSeries.invOfUnit
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) 1 * 1 :=
      (mul_one _).symm
    _ = PowerSeries.invOfUnit
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) 1 *
        ((↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) *
          PowerSeries.mk 1) := by rw [geometricLaw]
    _ = (PowerSeries.invOfUnit
          (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ) 1 *
        (↑(sourceLocalZetaPolynomial prime) : PowerSeries ℤ)) *
          PowerSeries.mk 1 := by rw [mul_assoc]
    _ = PowerSeries.mk 1 := by rw [inverseLaw, one_mul]

@[simp] theorem sourceLocalZetaPowerSeries_coeff
    (prime : Nat.Primes) (exponent : Nat) :
    (sourceLocalZetaPowerSeries prime).coeff exponent = 1 := by
  rw [sourceLocalZetaPowerSeries_eq_mk_one]
  simp

@[simp] theorem sourceLocalFormalEulerFactor_apply_primePower
    (prime : Nat.Primes) (exponent : Nat) :
    sourceLocalFormalEulerFactor prime ((prime : Nat) ^ exponent) = 1 := by
  rw [sourceLocalFormalEulerFactor,
    ArithmeticFunction.ofPowerSeries_apply_pow prime.property.one_lt,
    sourceLocalZetaPowerSeries_coeff]

/-- Calculation points expose only the prior unit history. -/
inductive EulerPrefixFoldPoint : Type
  | seed
  | local (prior : UnitHistory)

/-- The Euler calculation tree is definitionally the unit-history tree. -/
def eulerPrefixUnfolding :
    UnitHistory → RootedAccountedUnfolding EulerPrefixFoldPoint
  | .empty => RootedAccountedUnfolding.zero .seed
  | .next prior =>
      .occur (.local prior) <|
        .singleton (eulerPrefixUnfolding prior)

private def firstChildOr {Carrier : Type}
    (fallback : Carrier) : List Carrier → Carrier
  | [] => fallback
  | first :: _ => first

/-- Local fold law: a new unit multiplies by the next prime-local factor. -/
def eulerPrefixAlgebra
    (point : EulerPrefixFoldPoint)
    (children : List (ArithmeticFunction ℤ)) : ArithmeticFunction ℤ :=
  match point with
  | .seed => 1
  | .local prior =>
      sourceLocalFormalEulerFactor
          (primeAtStage prior.cardinalShadow) *
        firstChildOr 1 children

/-- Finite Euler prefix generated by the actual unit history. -/
def finiteEulerPrefix (history : UnitHistory) : ArithmeticFunction ℤ :=
  (eulerPrefixUnfolding history).fold eulerPrefixAlgebra

@[simp] theorem finiteEulerPrefix_empty :
    finiteEulerPrefix .empty = 1 :=
  rfl

@[simp] theorem finiteEulerPrefix_next (prior : UnitHistory) :
    finiteEulerPrefix (.next prior) =
      sourceLocalFormalEulerFactor (primeAtStage prior.cardinalShadow) *
        finiteEulerPrefix prior :=
  rfl

/-! ## One source-generated Euler/reversal relation occurrence -/

abbrev RelationRank : Nat :=
  CanonicalUnitArithmeticRoot.initialStep.material.whole.cardinalShadow

abbrev RelationLattice := Fin RelationRank → ℤ

def reversal : RelationLattice →ₗ[ℤ] RelationLattice where
  toFun := fun value index => value index.rev
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar value
    rfl

@[simp] theorem reversal_apply
    (value : RelationLattice) (index : Fin RelationRank) :
    reversal value index = value index.rev :=
  rfl

theorem reversal_involutive : Function.Involutive reversal := by
  intro value
  funext index
  simp [reversal]

def antiInvariantBoundary : RelationLattice →ₗ[ℤ] RelationLattice :=
  LinearMap.id - reversal

/-- Coordinate-free material generated from one exact root point.  Its
constructor is private, so no caller can replace the unit fold or boundary. -/
structure CoordinateFreeRelationSource : Type where
  private mk ::
  history : UnitHistory

namespace CoordinateFreeRelationSource

def generate (history : UnitHistory) : CoordinateFreeRelationSource :=
  ⟨history⟩

def eulerCalculation (source : CoordinateFreeRelationSource) :
    RootedAccountedUnfolding EulerPrefixFoldPoint :=
  eulerPrefixUnfolding source.history

def boundary (_source : CoordinateFreeRelationSource) :
    RelationLattice →ₗ[ℤ] RelationLattice :=
  antiInvariantBoundary

def eulerPrefix (source : CoordinateFreeRelationSource) :
    ArithmeticFunction ℤ :=
  source.eulerCalculation.fold eulerPrefixAlgebra

@[simp] theorem eulerPrefix_generate (history : UnitHistory) :
    (generate history).eulerPrefix = finiteEulerPrefix history :=
  rfl

theorem eulerCalculation_eq_unfolding
    (source : CoordinateFreeRelationSource) :
    source.eulerCalculation = eulerPrefixUnfolding source.history := by
  rfl

theorem eulerPrefix_eq_finiteEulerPrefix
    (source : CoordinateFreeRelationSource) :
    source.eulerPrefix = finiteEulerPrefix source.history := by
  rw [eulerPrefix, eulerCalculation_eq_unfolding]
  rfl

end CoordinateFreeRelationSource

def sourceAt (point : DomainPoint) : CoordinateFreeRelationSource :=
  CoordinateFreeRelationSource.generate point.installedMaterial.whole

/-- The first authoritative common occurrence.  Removing the exact unit root
removes Euler calculation, reversal boundary, presentation, and rigidity. -/
def commonOccurrence :
    RootedAccountedUnfolding (DomainPoint × CoordinateFreeRelationSource) :=
  rootOccurrence.map fun point => (point, sourceAt point)

theorem commonOccurrence_projects_to_exact_unit_root :
    commonOccurrence.map Prod.fst = rootOccurrence := by
  rw [commonOccurrence, RootedAccountedUnfolding.map_map]
  change rootOccurrence.map id = rootOccurrence
  exact RootedAccountedUnfolding.map_id _

/-- Euler prefix is a restriction of the common occurrence, not a constant
attached after source generation. -/
def eulerPrefixOccurrence :
    RootedAccountedUnfolding (DomainPoint × ArithmeticFunction ℤ) :=
  commonOccurrence.map fun point => (point.1, point.2.eulerPrefix)

theorem eulerPrefixOccurrence_projects_to_exact_unit_root :
    eulerPrefixOccurrence.map Prod.fst = rootOccurrence := by
  rw [eulerPrefixOccurrence, RootedAccountedUnfolding.map_map]
  exact commonOccurrence_projects_to_exact_unit_root

def sourceOccurrences (value : RelationLattice) :
    RootedAccountedUnfolding RelationLattice :=
  RootedAccountedUnfolding.zero value

def targetOccurrences (value : RelationLattice) :
    RootedAccountedUnfolding RelationLattice :=
  RootedAccountedUnfolding.zero value

/-- The boundary occurrence is projected from the same common source. -/
def boundaryOccurrence :
    RootedAccountedUnfolding (RelationLattice →ₗ[ℤ] RelationLattice) :=
  commonOccurrence.map fun point => point.2.boundary

def presentation : RootGeneratedFiniteDefectPresentationAt
    commonOccurrence sourceOccurrences targetOccurrences boundaryOccurrence :=
  RootGeneratedFiniteDefectPresentationAt.generate

abbrev Carrier : Type := presentation.cokernel

theorem generatedFinitePresentationFG : AddGroup.FG Carrier :=
  Module.Finite.iff_addGroup_fg.mp inferInstance

abbrev PrimePowerState := PrimePowerQuotientEvaluation.State Carrier

/-- The generic quotient evaluator is installed on the coordinate-free
common occurrence itself. -/
def quotientEvaluationFace :
    RootGeneratedPrimePowerQuotientEvaluationAt Carrier
      commonOccurrence generatedFinitePresentationFG :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate Carrier

def dependentOccurrence : RootedAccountedUnfolding
    ((DomainPoint × CoordinateFreeRelationSource) ×
      PrimePowerKernelIncidenceAt Carrier PrimePowerState) :=
  quotientEvaluationFace.dependentOccurrence

def rigidityFace : RootGeneratedPrimePowerKernelIncidenceRigidityAt
    dependentOccurrence :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem rigidity_preserves_common_occurrence :
    rigidityFace.root = commonOccurrence :=
  quotientEvaluationFace.dependentOccurrence_projects_to_root

theorem rigidity_projects_to_exact_unit_root :
    rigidityFace.root.map Prod.fst = rootOccurrence := by
  rw [rigidity_preserves_common_occurrence]
  exact commonOccurrence_projects_to_exact_unit_root

theorem sourceKernelResidualZero :
    GeneratedSourceKernelResidualZeroAt rigidityFace.faithfulFace
      rigidityFace.additiveCalculation :=
  rigidityFace.sourceKernelResidualZero

noncomputable def canonicalSourceComponentEquiv :=
  rigidityFace.canonicalSourceComponentEquiv

end


end CanonicalUnitArithmeticCommonCarrier
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
