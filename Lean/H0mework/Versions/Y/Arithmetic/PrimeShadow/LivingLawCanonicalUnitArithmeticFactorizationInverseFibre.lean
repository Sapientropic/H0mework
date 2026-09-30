import H0mework.Versions.X.Arithmetic.EulerLocal.FiniteEnvelope
import H0mework.Versions.Y.Foundation.Ledger.CanonicalUnitOldRowNoGo

/-!
# The factor key lost by the unit-normalized relation

The complete prime-power indices and joint landings already belong to the
actual factorization occurrence.  The finite-envelope relation forgets the
prime-power key at a fixed stage; this file records that inverse fibre using
the existing source inventory, without adding another inventory carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationInverseFibre

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope

noncomputable section

@[simp] theorem factorizationOccurrence_root_whole (stage : Nat) :
    authorityWholeHistory (factorizationOccurrence stage).root.1 =
      runtimeWholeHistory stage :=
  rfl

/-- The generated factor inventory is indexed by the original executable
unit action's target at this activated occurrence. -/
theorem factorizationOccurrence_root_whole_eq_action_target (stage : Nat) :
    authorityWholeHistory (factorizationOccurrence stage).root.1 =
      CanonicalUnitArithmeticRoot.nativeActionTarget
        (CanonicalUnitArithmeticRoot.nativeActionTrace
          (runtimeAt stage).current.visit.current) :=
  rfl

abbrev FactorKeyAt (root : FactorizationRoot) : Type :=
  (index : PrimeIndex (authorityWholeHistory root.1)) ×
    ExponentIndex (authorityWholeHistory root.1) index

/-- The old finite-envelope relation, evaluated on one actual factor key. -/
def oldRelationProjectionAt (root : FactorizationRoot)
    (key : FactorKeyAt root) : Lattice :=
  componentDifference -
    ((prime (authorityWholeHistory root.1) key.1 : Nat) ^ exponent key.2 *
      (quotientHistory key.1 key.2).cardinalShadow) • quotientUnitDifference

theorem oldRelationProjectionAt_eq_whole (root : FactorizationRoot)
    (key : FactorKeyAt root) :
    oldRelationProjectionAt root key = componentDifference -
      (factorialHistory (authorityWholeHistory root.1)).cardinalShadow •
        quotientUnitDifference := by
  have landing := congrArg UnitHistory.cardinalShadow
    (primePower_joint_landing key.1 key.2)
  have coefficient :
      (prime (authorityWholeHistory root.1) key.1 : Nat) ^ exponent key.2 *
        (quotientHistory key.1 key.2).cardinalShadow =
          (factorialHistory (authorityWholeHistory root.1)).cardinalShadow := by
    simpa [UnitHistory.cardinalShadow_joint, primePowerHistory,
      quotientHistory, UnitHistory.cardinalShadow_generate] using landing.symm
  simp only [oldRelationProjectionAt, coefficient]

theorem oldRelationProjectionAt_eq_existing
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    oldRelationProjectionAt (factorizationOccurrence factor.stage).root
      ⟨factor.primeIndex, factor.exponentIndex⟩ = relation factor := by
  simp only [oldRelationProjectionAt, relation, quotientUnitCoefficient]
  change componentDifference -
      ((prime (runtimeWholeHistory factor.stage) factor.primeIndex : Nat) ^
          exponent factor.exponentIndex *
        (quotientHistory factor.primeIndex factor.exponentIndex).cardinalShadow) •
          quotientUnitDifference =
    componentDifference -
      ((requestedPrime : Nat) ^ requestedExponent *
        (quotientHistory factor.primeIndex factor.exponentIndex).cardinalShadow) •
          quotientUnitDifference
  rw [factor.actual_prime_power_value]

theorem old_relation_occurrence_is_key_projection
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (relationOccurrence factor).root =
      ((factorizationOccurrence factor.stage).root,
        oldRelationProjectionAt (factorizationOccurrence factor.stage).root
          ⟨factor.primeIndex, factor.exponentIndex⟩) := by
  rw [oldRelationProjectionAt_eq_existing]
  rfl

def keyTwo : FactorKeyAt (factorizationOccurrence 1).root := by
  refine ⟨⟨2, ?_⟩, ⟨0, ?_⟩⟩
  · have shadow : (runtimeWholeHistory 1).cardinalShadow = 3 := by
      exact runtimeWholeHistory_cardinalShadow 1
    rw [Finsupp.mem_support_iff, factorization_eq_cardinal_factorization,
      factorizationOccurrence_root_whole, shadow]
    have bound : 1 ≤ (Nat.factorial 3).factorization 2 :=
      ((by decide : Nat.Prime 2).dvd_iff_one_le_factorization
        (by decide : Nat.factorial 3 ≠ 0)).mp (by decide)
    omega
  · exact multiplicity_pos _ _

def keyThree : FactorKeyAt (factorizationOccurrence 1).root := by
  refine ⟨⟨3, ?_⟩, ⟨0, ?_⟩⟩
  · have shadow : (runtimeWholeHistory 1).cardinalShadow = 3 := by
      exact runtimeWholeHistory_cardinalShadow 1
    rw [Finsupp.mem_support_iff, factorization_eq_cardinal_factorization,
      factorizationOccurrence_root_whole, shadow]
    have bound : 1 ≤ (Nat.factorial 3).factorization 3 :=
      ((by decide : Nat.Prime 3).dvd_iff_one_le_factorization
        (by decide : Nat.factorial 3 ≠ 0)).mp (by decide)
    omega
  · exact multiplicity_pos _ _

theorem keyTwo_ne_keyThree : keyTwo ≠ keyThree := by
  intro same
  have primeSame := congrArg
    (fun key : FactorKeyAt (factorizationOccurrence 1).root => key.1.1) same
  norm_num [keyTwo, keyThree] at primeSame

theorem both_keys_same_actual_factorization :
    factorialHistory (authorityWholeHistory (factorizationOccurrence 1).root.1) =
        ((factorizationOccurrence 1).root.2.actualPrimePowerHistory
          keyTwo.1 keyTwo.2).joint
          ((factorizationOccurrence 1).root.2.actualQuotientHistory
            keyTwo.1 keyTwo.2) ∧
      factorialHistory (authorityWholeHistory (factorizationOccurrence 1).root.1) =
        ((factorizationOccurrence 1).root.2.actualPrimePowerHistory
          keyThree.1 keyThree.2).joint
          ((factorizationOccurrence 1).root.2.actualQuotientHistory
            keyThree.1 keyThree.2) :=
  ⟨(factorizationOccurrence 1).root.2.actualPrimePower_joint_landing
      keyTwo.1 keyTwo.2,
    (factorizationOccurrence 1).root.2.actualPrimePower_joint_landing
      keyThree.1 keyThree.2⟩

theorem oldRelationProjectionAt_not_injective :
    ¬ Function.Injective
      (oldRelationProjectionAt (factorizationOccurrence 1).root) := by
  intro faithful
  apply keyTwo_ne_keyThree
  apply faithful
  rw [oldRelationProjectionAt_eq_whole,
    oldRelationProjectionAt_eq_whole]

/-- The two actual factor keys cannot be encoded injectively in the literal
old single-row evolution.  This is a representation boundary for that row,
not a new disposition or a U8 realization. -/
theorem old_whole_row_cannot_encode_actual_factor_keys :
    ¬ ∃ encode : FactorKeyAt (factorizationOccurrence 1).root →
        LedgerWriteEvolutionAt CanonicalUnitArithmeticRoot.N
          ⟨(runtimeAt 1).current.visit.current⟩
          ⟨CanonicalUnitArithmeticRoot.next
            (runtimeAt 1).current.visit.current⟩,
      Function.Injective encode := by
  rintro ⟨encode, faithful⟩
  apply keyTwo_ne_keyThree
  exact faithful
    ((CanonicalUnitArithmeticRoot.old_whole_evolution_subsingleton
      (runtimeAt 1).current.visit.current).elim
        (encode keyTwo) (encode keyThree))

end
end CanonicalUnitArithmeticFactorizationInverseFibre
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
