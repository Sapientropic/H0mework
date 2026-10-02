import H0mework.Versions.R2.Arithmetic.EulerLocal.Operator

/-!
# Actual factorization division landing

For one source-generated runtime prime-power factor, the exact unit-history
joint landing is linearized into a four-generator finite presentation:

* whole / quotient-history role;
* original / reversed dual bit.

For each dual bit the relation is

`whole - p^k · quotientHistory`.

The domain uses that relation only to prove the requested canonical
prime-power quotient class is zero.  Range membership and extraction of an
actual division root remain inside the generic quotient-evaluation kernel.
No rigidity, fixedness, equivalence, determinant or positive settlement is
accepted by the mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationDivisionLanding

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open FiniteDefectDeterminant
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt

noncomputable section

inductive FactorRole
  | whole
  | quotientHistory
  deriving DecidableEq

instance factorRoleFintype : Fintype FactorRole where
  elems := {.whole, .quotientHistory}
  complete := by
    intro role
    cases role <;> simp

abbrev RelationIndex := Fin 2
abbrev RelationLattice := RelationIndex → ℤ
abbrev GeneratorIndex := FactorRole × Fin 2
abbrev GeneratorLattice := GeneratorIndex → ℤ

def relationBasis (dualIndex : Fin 2) : RelationLattice :=
  Pi.single dualIndex 1

def generatorBasis (role : FactorRole) (dualIndex : Fin 2) :
    GeneratorLattice :=
  Pi.single (role, dualIndex) 1

def requestedPrimePower
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (_factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Nat :=
  (requestedPrime : Nat) ^ requestedExponent

/-- Relation map calculated from one actual prime-power factor. -/
def relationMap
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (_factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationLattice →ₗ[ℤ] GeneratorLattice where
  toFun := fun coefficient index =>
    match index.1 with
    | .whole => coefficient index.2
    | .quotientHistory =>
        -((requestedPrime : ℤ) ^ requestedExponent * coefficient index.2)
  map_add' := by
    intro left right
    funext index
    rcases index with ⟨role, dualIndex⟩
    cases role
    · rfl
    · dsimp
      ring
  map_smul' := by
    intro scalar value
    funext index
    rcases index with ⟨role, dualIndex⟩
    cases role
    · rfl
    · dsimp
      ring

theorem relationMap_basis
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) :
    relationMap factor (relationBasis dualIndex) =
      generatorBasis .whole dualIndex -
        (requestedPrime : Nat) ^ requestedExponent •
          generatorBasis .quotientHistory dualIndex := by
  funext index
  rcases index with ⟨role, currentDual⟩
  cases role <;>
    simp [relationMap, relationBasis, generatorBasis,
      Pi.single_apply, nsmul_eq_mul]

def relationOccurrences (value : RelationLattice) :
    RootedAccountedUnfolding RelationLattice :=
  RootedAccountedUnfolding.zero value

def generatorOccurrences (value : GeneratorLattice) :
    RootedAccountedUnfolding GeneratorLattice :=
  RootedAccountedUnfolding.zero value

def relationMapOccurrence
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RootedAccountedUnfolding (RelationLattice →ₗ[ℤ] GeneratorLattice) :=
  (factorizationOccurrence factor.stage).map fun _root => relationMap factor

def presentation
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RootGeneratedFiniteDefectPresentationAt
      (factorizationOccurrence factor.stage)
      relationOccurrences generatorOccurrences
      (relationMapOccurrence factor) :=
  RootGeneratedFiniteDefectPresentationAt.generate

abbrev Carrier
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  (presentation factor).cokernel

theorem carrierFG
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    AddGroup.FG (Carrier factor) := by
  apply Module.Finite.iff_addGroup_fg.mp
  unfold Carrier
  exact Module.Finite.quotient ℤ
    (LinearMap.range (relationMap factor))

abbrev PrimePowerState
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  PrimePowerQuotientEvaluation.State (Carrier factor)

def quotientFace
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RootGeneratedPrimePowerQuotientEvaluationAt (Carrier factor)
      (factorizationOccurrence factor.stage) (carrierFG factor) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate (Carrier factor)

def quotientEvaluator
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor → PrimePowerState factor :=
  (quotientFace factor).accountedEvaluator

def presentedGenerator
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (role : FactorRole) (dualIndex : Fin 2) : Carrier factor :=
  Submodule.Quotient.mk (generatorBasis role dualIndex)

def component
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  presentedGenerator factor .whole 0

def reversalComponent
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  presentedGenerator factor .whole 1

def difference
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  component factor - reversalComponent factor

private def quotientHistoryDifference
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  presentedGenerator factor .quotientHistory 0 -
    presentedGenerator factor .quotientHistory 1

private theorem presentedWhole_eq_primePower_smul_quotientHistory
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) :
    presentedGenerator factor .whole dualIndex =
      (requestedPrime : Nat) ^ requestedExponent •
        presentedGenerator factor .quotientHistory dualIndex := by
  apply (Submodule.Quotient.eq _).2
  change generatorBasis .whole dualIndex -
      (requestedPrime : Nat) ^ requestedExponent •
        generatorBasis .quotientHistory dualIndex ∈
    LinearMap.range (relationMap factor)
  exact ⟨relationBasis dualIndex, relationMap_basis factor dualIndex⟩

private theorem primePower_smul_quotientHistoryDifference_eq_difference
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (requestedPrime : Nat) ^ requestedExponent •
        quotientHistoryDifference factor =
      difference factor := by
  unfold quotientHistoryDifference difference component reversalComponent
  rw [smul_sub, presentedWhole_eq_primePower_smul_quotientHistory,
    presentedWhole_eq_primePower_smul_quotientHistory]

/-- Actual domain restriction incidence: the anti-invariant difference is
zero in the requested canonical `p^k` quotient.  The theorem exposes no
division root; the generic quotient kernel extracts it from this equality. -/
theorem difference_quotientZero
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    quotientEvaluator factor (difference factor)
        requestedPrime requestedExponent = 0 := by
  unfold quotientEvaluator
  rw [(quotientFace factor).accountedEvaluator_eq_canonical]
  apply (QuotientAddGroup.eq_zero_iff (difference factor)).2
  rw [← primePower_smul_quotientHistoryDifference_eq_difference factor]
  exact ⟨quotientHistoryDifference factor, rfl⟩

/-- The presentation relation is anchored by the actual unit-history joint
factorization, rather than by a bare numeric prime label. -/
theorem divisionLanding_preserves_actual_joint_factorization
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    factorialHistory (runtimeWholeHistory factor.stage) =
        (primePowerHistory factor.primeIndex factor.exponentIndex).joint
          (quotientHistory factor.primeIndex factor.exponentIndex) ∧
      (prime (runtimeWholeHistory factor.stage) factor.primeIndex : Nat) ^
          exponent factor.exponentIndex =
        (requestedPrime : Nat) ^ requestedExponent ∧
      quotientEvaluator factor (difference factor)
          requestedPrime requestedExponent = 0 :=
  ⟨factor.actual_joint_landing, factor.actual_prime_power_value,
    difference_quotientZero factor⟩

theorem presentation_projects_to_exact_factorization_occurrence
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (presentation factor).root =
      factorizationOccurrence factor.stage :=
  rfl

end
end CanonicalUnitArithmeticFactorizationDivisionLanding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
