import H0mework.Arithmetic.EulerLocal.DivisionLanding

/-!
# Actual factorization/Euler local landing

For one source-generated prime-power factor, the exact relation

`whole = p^k · quotientHistory`

is installed at every exponent/dual coordinate.  The full local Euler
convolution and reversal act on both roles and preserve that relation, so
they descend to the presentation carrier.  Applying the descended
`id - Euler ∘ reversal` boundary to the common whole component produces an
evaluation-zero component whose anti-invariant difference has an actual
`p^k` division landing.  Only its canonical quotient-zero class is exposed;
the generic quotient kernel owns range extraction and the division root.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationEulerLocalLanding

open CanonicalUnitArithmeticFactorizationDivisionLanding
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerOperator
open FiniteDefectDeterminant
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt

noncomputable section

variable {requestedPrime : Nat.Primes} {requestedExponent : Nat}

abbrev LocalExponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  Fin (multiplicity (runtimeWholeHistory factor.stage) factor.primeIndex + 1)

abbrev RelationIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  LocalExponent factor × Fin 2

abbrev RelationLattice
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  RelationIndex factor → ℤ

abbrev GeneratorIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  FactorRole × RelationIndex factor

abbrev GeneratorLattice
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  GeneratorIndex factor → ℤ

def primePower
    (_factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) : Nat :=
  (requestedPrime : Nat) ^ requestedExponent

def exponentSub
    {factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent}
    (localExponent : LocalExponent factor) (amount : Nat) :
    LocalExponent factor :=
  ⟨localExponent - amount,
    (Nat.sub_le localExponent amount).trans_lt localExponent.isLt⟩

def roleEmbedding
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (role : FactorRole) :
    RelationLattice factor →ₗ[ℤ] GeneratorLattice factor where
  toFun := fun value index => if index.1 = role then value index.2 else 0
  map_add' := by
    intro left right
    funext index
    by_cases same : index.1 = role <;> simp [same]
  map_smul' := by
    intro scalar value
    funext index
    by_cases same : index.1 = role <;> simp [same]

/-- Coordinatewise linearization of the actual joint factorization. -/
def relationMap
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationLattice factor →ₗ[ℤ] GeneratorLattice factor where
  toFun := fun value index =>
    match index.1 with
    | .whole => value index.2
    | .quotientHistory => -((primePower factor : ℤ) * value index.2)
  map_add' := by
    intro left right
    funext index
    rcases index with ⟨role, localIndex⟩
    cases role with
    | whole => rfl
    | quotientHistory =>
        simp only [Pi.add_apply]
        ring
  map_smul' := by
    intro scalar value
    funext index
    rcases index with ⟨role, localIndex⟩
    cases role with
    | whole => rfl
    | quotientHistory =>
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring

theorem relationMap_eq_role_difference
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (value : RelationLattice factor) :
    relationMap factor value =
      roleEmbedding factor .whole value -
        primePower factor • roleEmbedding factor .quotientHistory value := by
  funext index
  rcases index with ⟨role, localIndex⟩
  cases role <;>
    simp [relationMap, roleEmbedding, primePower, nsmul_eq_mul]

def relationOccurrences
    {factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent}
    (value : RelationLattice factor) :
    RootedAccountedUnfolding (RelationLattice factor) :=
  RootedAccountedUnfolding.zero value

def generatorOccurrences
    {factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent}
    (value : GeneratorLattice factor) :
    RootedAccountedUnfolding (GeneratorLattice factor) :=
  RootedAccountedUnfolding.zero value

def relationMapOccurrence
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RootedAccountedUnfolding
      (RelationLattice factor →ₗ[ℤ] GeneratorLattice factor) :=
  (factorizationOccurrence factor.stage).map fun _root => relationMap factor

def presentation
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RootGeneratedFiniteDefectPresentationAt
      (factorizationOccurrence factor.stage)
      (relationOccurrences (factor := factor))
      (generatorOccurrences (factor := factor))
      (relationMapOccurrence factor) :=
  RootGeneratedFiniteDefectPresentationAt.generate

abbrev Carrier
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  (presentation factor).cokernel

theorem carrierFG
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    AddGroup.FG (Carrier factor) := by
  apply Module.Finite.iff_addGroup_fg.mp
  unfold Carrier
  exact Module.Finite.quotient ℤ (LinearMap.range (relationMap factor))

def actualPrime
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Nat.Primes :=
  prime (runtimeWholeHistory factor.stage) factor.primeIndex

def relationEuler
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationLattice factor →ₗ[ℤ] RelationLattice factor where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.1 + 1),
      (localEulerPowerSeries (actualPrime factor)).coeff amount *
        value (exponentSub index.1 amount, index.2)
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    ring

def generatorEuler
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    GeneratorLattice factor →ₗ[ℤ] GeneratorLattice factor where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      (localEulerPowerSeries (actualPrime factor)).coeff amount *
        value (index.1, exponentSub index.2.1 amount, index.2.2)
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    ring

def relationReversal
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationLattice factor →ₗ[ℤ] RelationLattice factor where
  toFun := fun value index => value (index.1, index.2.rev)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def generatorReversal
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    GeneratorLattice factor →ₗ[ℤ] GeneratorLattice factor where
  toFun := fun value index => value (index.1, index.2.1, index.2.2.rev)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem relationMap_euler_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (generatorEuler factor).comp (relationMap factor) =
      (relationMap factor).comp (relationEuler factor) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨role, localExponent, dualIndex⟩
  cases role with
  | whole => rfl
  | quotientHistory =>
      simp only [LinearMap.comp_apply, generatorEuler, relationMap,
        relationEuler, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [localEulerCoefficient, one_mul]
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum]

theorem relationMap_reversal_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (generatorReversal factor).comp (relationMap factor) =
      (relationMap factor).comp (relationReversal factor) := by
  rfl

theorem generatorEuler_maps_relationRange
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    LinearMap.range (relationMap factor) ≤
      (LinearMap.range (relationMap factor)).comap (generatorEuler factor) := by
  intro value value_mem
  rcases value_mem with ⟨source, rfl⟩
  refine ⟨relationEuler factor source, ?_⟩
  exact (LinearMap.congr_fun (relationMap_euler_square factor) source).symm

theorem generatorReversal_maps_relationRange
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    LinearMap.range (relationMap factor) ≤
      (LinearMap.range (relationMap factor)).comap
        (generatorReversal factor) := by
  intro value value_mem
  rcases value_mem with ⟨source, rfl⟩
  refine ⟨relationReversal factor source, ?_⟩
  exact LinearMap.congr_fun (relationMap_reversal_square factor) source

def carrierEuler
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor →ₗ[ℤ] Carrier factor :=
  Submodule.mapQ (LinearMap.range (relationMap factor))
    (LinearMap.range (relationMap factor)) (generatorEuler factor)
    (generatorEuler_maps_relationRange factor)

def carrierReversal
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor →ₗ[ℤ] Carrier factor :=
  Submodule.mapQ (LinearMap.range (relationMap factor))
    (LinearMap.range (relationMap factor)) (generatorReversal factor)
    (generatorReversal_maps_relationRange factor)

theorem generatorEuler_reversal_commutes
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (generatorEuler factor).comp (generatorReversal factor) =
      (generatorReversal factor).comp (generatorEuler factor) := by
  rfl

theorem carrierEuler_reversal_commutes
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (carrierEuler factor).comp (carrierReversal factor) =
      (carrierReversal factor).comp (carrierEuler factor) := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change Submodule.Quotient.mk
      (generatorEuler factor (generatorReversal factor representative)) =
    Submodule.Quotient.mk
      (generatorReversal factor (generatorEuler factor representative))
  apply congrArg Submodule.Quotient.mk
  exact LinearMap.congr_fun
    (generatorEuler_reversal_commutes factor) representative

def carrierBoundary
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor →ₗ[ℤ] Carrier factor :=
  LinearMap.id - (carrierEuler factor).comp (carrierReversal factor)

theorem carrierBoundary_reversal_commutes
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (carrierBoundary factor).comp (carrierReversal factor) =
      (carrierReversal factor).comp (carrierBoundary factor) := by
  apply LinearMap.ext
  intro value
  change carrierReversal factor value -
      carrierEuler factor
        (carrierReversal factor (carrierReversal factor value)) =
    carrierReversal factor
      (value - carrierEuler factor (carrierReversal factor value))
  rw [map_sub]
  apply congrArg (fun current => carrierReversal factor value - current)
  exact LinearMap.congr_fun
    (carrierEuler_reversal_commutes factor)
    (carrierReversal factor value)

def orientedRelation
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationLattice factor :=
  fun index => if index.2 = (0 : Fin 2) then 1 else 0

def presentedRole
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (role : FactorRole) : Carrier factor :=
  Submodule.Quotient.mk
    (roleEmbedding factor role (orientedRelation factor))

def component
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  carrierBoundary factor (presentedRole factor .whole)

def quotientHistoryComponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  carrierBoundary factor (presentedRole factor .quotientHistory)

def reversedComponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  carrierReversal factor (component factor)

def difference
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  component factor - reversedComponent factor

private theorem presentedWhole_eq_primePower_smul_quotientHistory
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    presentedRole factor .whole =
      primePower factor • presentedRole factor .quotientHistory := by
  apply (Submodule.Quotient.eq _).2
  change roleEmbedding factor .whole (orientedRelation factor) -
      primePower factor •
        roleEmbedding factor .quotientHistory (orientedRelation factor) ∈
    LinearMap.range (relationMap factor)
  refine ⟨orientedRelation factor, ?_⟩
  exact relationMap_eq_role_difference factor (orientedRelation factor)

private theorem component_eq_primePower_smul_quotientHistoryComponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    component factor =
      primePower factor • quotientHistoryComponent factor := by
  have equality := congrArg (fun value => carrierBoundary factor value)
    (presentedWhole_eq_primePower_smul_quotientHistory factor)
  simpa [component, quotientHistoryComponent, map_nsmul] using equality

private def quotientHistoryDifference
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor :=
  quotientHistoryComponent factor -
    carrierReversal factor (quotientHistoryComponent factor)

theorem primePower_smul_quotientHistoryDifference_eq_difference
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    primePower factor • quotientHistoryDifference factor =
      difference factor := by
  unfold quotientHistoryDifference difference reversedComponent
  rw [smul_sub, ← map_nsmul,
    ← component_eq_primePower_smul_quotientHistoryComponent]

abbrev EvaluationRelation
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  LinearMap.range (carrierBoundary factor)

abbrev EvaluationCarrier
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  Carrier factor ⧸ EvaluationRelation factor

def evaluation
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor →ₗ[ℤ] EvaluationCarrier factor :=
  (EvaluationRelation factor).mkQ

theorem evaluation_component_zero
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    evaluation factor (component factor) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨presentedRole factor .whole, rfl⟩

theorem carrierReversal_maps_evaluationRelation
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    EvaluationRelation factor ≤
      (EvaluationRelation factor).comap (carrierReversal factor) := by
  intro value value_mem
  rcases value_mem with ⟨source, rfl⟩
  refine ⟨carrierReversal factor source, ?_⟩
  exact LinearMap.congr_fun
    (carrierBoundary_reversal_commutes factor) source

def evaluationReversal
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    EvaluationCarrier factor →ₗ[ℤ] EvaluationCarrier factor :=
  Submodule.mapQ (EvaluationRelation factor) (EvaluationRelation factor)
    (carrierReversal factor)
    (carrierReversal_maps_evaluationRelation factor)

theorem evaluation_reversal
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (value : Carrier factor) :
    evaluation factor (carrierReversal factor value) =
      evaluationReversal factor (evaluation factor value) := by
  exact (Submodule.mapQ_apply _ _ _ value).symm

theorem evaluation_reversedComponent_zero
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    evaluation factor (reversedComponent factor) = 0 := by
  unfold reversedComponent
  rw [evaluation_reversal, evaluation_component_zero, map_zero]

theorem evaluation_difference_zero
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    evaluation factor (difference factor) = 0 := by
  unfold difference
  rw [map_sub, evaluation_component_zero,
    evaluation_reversedComponent_zero, sub_self]

abbrev PrimePowerState
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :=
  PrimePowerQuotientEvaluation.State (Carrier factor)

def quotientFace
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RootGeneratedPrimePowerQuotientEvaluationAt (Carrier factor)
      (factorizationOccurrence factor.stage) (carrierFG factor) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate (Carrier factor)

def quotientEvaluator
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor → PrimePowerState factor :=
  (quotientFace factor).accountedEvaluator

/-- The exact local domain feed.  Range membership and the selected division
root remain inside `LivingLawPrimePowerQuotientEvaluationKernel`. -/
theorem difference_quotientZero
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    quotientEvaluator factor (difference factor)
        requestedPrime requestedExponent = 0 := by
  unfold quotientEvaluator
  rw [(quotientFace factor).accountedEvaluator_eq_canonical]
  apply (QuotientAddGroup.eq_zero_iff (difference factor)).2
  rw [← primePower_smul_quotientHistoryDifference_eq_difference factor]
  exact ⟨quotientHistoryDifference factor, rfl⟩

theorem localLanding_preserves_actual_factorization_and_fullEuler
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    factorialHistory (runtimeWholeHistory factor.stage) =
        (primePowerHistory factor.primeIndex factor.exponentIndex).joint
          (quotientHistory factor.primeIndex factor.exponentIndex) ∧
      (prime (runtimeWholeHistory factor.stage) factor.primeIndex : Nat) ^
          exponent factor.exponentIndex =
        (requestedPrime : Nat) ^ requestedExponent ∧
      evaluation factor (component factor) = 0 ∧
      evaluation factor (difference factor) = 0 ∧
      quotientEvaluator factor (difference factor)
          requestedPrime requestedExponent = 0 :=
  ⟨factor.actual_joint_landing, factor.actual_prime_power_value,
    evaluation_component_zero factor, evaluation_difference_zero factor,
    difference_quotientZero factor⟩

theorem presentation_projects_to_exact_occurrence
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (presentation factor).root = factorizationOccurrence factor.stage :=
  rfl

end
end CanonicalUnitArithmeticFactorizationEulerLocalLanding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
