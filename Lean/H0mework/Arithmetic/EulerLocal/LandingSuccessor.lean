import H0mework.Arithmetic.EulerLocal.EulerLanding

/-!
# Successor square for one actual factorization/Euler landing

The domain contributes exactly one transition datum.  A prime-power factor
already present at an exact runtime occurrence is lifted to the next exact
runtime occurrence, and restriction along that lift preserves the actual
factorization relation, full Euler action, reversal, boundary, evaluation
zero component, and canonical quotient-zero row.

This file does not enumerate prime powers, choose a cofinal schedule, identify
different local carriers with a global component, or extract division roots.
Those closures belong to the generic living-law framework.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationEulerLocalLandingSuccessor

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerLocalLanding
open PrimePowerQuotientEvaluation

noncomputable section

variable {requestedPrime : Nat.Primes} {requestedExponent : Nat}

abbrev FactorRole :=
  CanonicalUnitArithmeticFactorizationDivisionLanding.FactorRole

def liftLocalExponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (localExponent : LocalExponent factor) :
    LocalExponent factor.advance := by
  refine ⟨localExponent.1, ?_⟩
  have order := RuntimePrimePowerFactorAt.runtimeFactorization_mono_succ
    factor.stage factor.primeIndex.1
  have oldBound := localExponent.2
  change localExponent.1 <
    factorization (runtimeWholeHistory (factor.stage + 1))
      factor.primeIndex.1 + 1
  change localExponent.1 <
    factorization (runtimeWholeHistory factor.stage)
      factor.primeIndex.1 + 1 at oldBound
  omega

@[simp] theorem liftLocalExponent_value
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (localExponent : LocalExponent factor) :
    (liftLocalExponent factor localExponent).1 = localExponent.1 :=
  rfl

theorem exponentSub_liftLocalExponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (localExponent : LocalExponent factor) (amount : Nat) :
    exponentSub (liftLocalExponent factor localExponent) amount =
      liftLocalExponent factor (exponentSub localExponent amount) := by
  apply Fin.ext
  rfl

def liftRelationIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationIndex factor → RelationIndex factor.advance
  | ⟨localExponent, dualIndex⟩ =>
      ⟨liftLocalExponent factor localExponent, dualIndex⟩

def liftGeneratorIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    GeneratorIndex factor → GeneratorIndex factor.advance
  | ⟨role, localExponent, dualIndex⟩ =>
      ⟨role, liftLocalExponent factor localExponent, dualIndex⟩

/-- The sole domain transition on relation coordinates. -/
def relationRestriction
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RelationLattice factor.advance →ₗ[ℤ] RelationLattice factor where
  toFun := fun value index => value (liftRelationIndex factor index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

/-- The matching transition on presented generators. -/
def generatorRestriction
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    GeneratorLattice factor.advance →ₗ[ℤ] GeneratorLattice factor where
  toFun := fun value index => value (liftGeneratorIndex factor index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

/-- The successor restriction preserves the actual
`whole - p^k · quotientHistory` row. -/
theorem restriction_relation_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (generatorRestriction factor).comp (relationMap factor.advance) =
      (relationMap factor).comp (relationRestriction factor) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨role, localExponent, dualIndex⟩
  cases role <;> rfl

theorem actualPrime_advance
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    actualPrime factor.advance = actualPrime factor := by
  apply Subtype.ext
  rfl

theorem restriction_relationEuler_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (relationRestriction factor).comp (relationEuler factor.advance) =
      (relationEuler factor).comp (relationRestriction factor) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨localExponent, dualIndex⟩
  change
    (∑ amount ∈ Finset.range (localExponent.1 + 1),
      (CanonicalUnitArithmeticFactorizationEulerOperator.localEulerPowerSeries
        (actualPrime factor.advance)).coeff amount *
        value
          (exponentSub (liftLocalExponent factor localExponent) amount,
            dualIndex)) =
      ∑ amount ∈ Finset.range (localExponent.1 + 1),
        (CanonicalUnitArithmeticFactorizationEulerOperator.localEulerPowerSeries
          (actualPrime factor)).coeff amount *
          value
            (liftLocalExponent factor (exponentSub localExponent amount),
              dualIndex)
  apply Finset.sum_congr rfl
  intro amount _membership
  rw [actualPrime_advance, exponentSub_liftLocalExponent]

theorem restriction_generatorEuler_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (generatorRestriction factor).comp (generatorEuler factor.advance) =
      (generatorEuler factor).comp (generatorRestriction factor) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨role, localExponent, dualIndex⟩
  change
    (∑ amount ∈ Finset.range (localExponent.1 + 1),
      (CanonicalUnitArithmeticFactorizationEulerOperator.localEulerPowerSeries
        (actualPrime factor.advance)).coeff amount *
        value
          (role,
            exponentSub (liftLocalExponent factor localExponent) amount,
            dualIndex)) =
      ∑ amount ∈ Finset.range (localExponent.1 + 1),
        (CanonicalUnitArithmeticFactorizationEulerOperator.localEulerPowerSeries
          (actualPrime factor)).coeff amount *
          value
            (role,
              liftLocalExponent factor (exponentSub localExponent amount),
              dualIndex)
  apply Finset.sum_congr rfl
  intro amount _membership
  rw [actualPrime_advance, exponentSub_liftLocalExponent]

theorem restriction_relationReversal_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (relationRestriction factor).comp (relationReversal factor.advance) =
      (relationReversal factor).comp (relationRestriction factor) := by
  rfl

theorem restriction_generatorReversal_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (generatorRestriction factor).comp (generatorReversal factor.advance) =
      (generatorReversal factor).comp (generatorRestriction factor) := by
  rfl

theorem generatorRestriction_maps_relationRange
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    LinearMap.range (relationMap factor.advance) ≤
      (LinearMap.range (relationMap factor)).comap
        (generatorRestriction factor) := by
  intro value value_mem
  rcases value_mem with ⟨source, rfl⟩
  refine ⟨relationRestriction factor source, ?_⟩
  exact LinearMap.congr_fun (restriction_relation_square factor) source

def carrierRestriction
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    Carrier factor.advance →ₗ[ℤ] Carrier factor :=
  Submodule.mapQ (LinearMap.range (relationMap factor.advance))
    (LinearMap.range (relationMap factor)) (generatorRestriction factor)
    (generatorRestriction_maps_relationRange factor)

theorem carrierRestriction_euler_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (carrierRestriction factor).comp (carrierEuler factor.advance) =
      (carrierEuler factor).comp (carrierRestriction factor) := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change Submodule.Quotient.mk
      (generatorRestriction factor (generatorEuler factor.advance representative)) =
    Submodule.Quotient.mk
      (generatorEuler factor (generatorRestriction factor representative))
  apply congrArg Submodule.Quotient.mk
  exact LinearMap.congr_fun (restriction_generatorEuler_square factor)
    representative

theorem carrierRestriction_reversal_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (carrierRestriction factor).comp (carrierReversal factor.advance) =
      (carrierReversal factor).comp (carrierRestriction factor) := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change Submodule.Quotient.mk
      (generatorRestriction factor
        (generatorReversal factor.advance representative)) =
    Submodule.Quotient.mk
      (generatorReversal factor (generatorRestriction factor representative))
  apply congrArg Submodule.Quotient.mk
  exact LinearMap.congr_fun (restriction_generatorReversal_square factor)
    representative

theorem carrierRestriction_boundary_square
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (carrierRestriction factor).comp (carrierBoundary factor.advance) =
      (carrierBoundary factor).comp (carrierRestriction factor) := by
  apply LinearMap.ext
  intro value
  change carrierRestriction factor
      (value - carrierEuler factor.advance
        (carrierReversal factor.advance value)) =
    carrierRestriction factor value -
      carrierEuler factor
        (carrierReversal factor (carrierRestriction factor value))
  rw [map_sub]
  apply congrArg (fun current => carrierRestriction factor value - current)
  calc
    carrierRestriction factor
        (carrierEuler factor.advance
          (carrierReversal factor.advance value)) =
      carrierEuler factor
        (carrierRestriction factor
          (carrierReversal factor.advance value)) :=
      LinearMap.congr_fun (carrierRestriction_euler_square factor)
        (carrierReversal factor.advance value)
    _ = carrierEuler factor
        (carrierReversal factor (carrierRestriction factor value)) := by
      apply congrArg (carrierEuler factor)
      exact LinearMap.congr_fun
        (carrierRestriction_reversal_square factor) value

theorem restriction_orientedRelation
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    relationRestriction factor (orientedRelation factor.advance) =
      orientedRelation factor := by
  funext index
  rfl

theorem restriction_roleEmbedding
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (role : FactorRole) (value : RelationLattice factor.advance) :
    generatorRestriction factor (roleEmbedding factor.advance role value) =
      roleEmbedding factor role (relationRestriction factor value) := by
  funext index
  rcases index with ⟨indexRole, localExponent, dualIndex⟩
  by_cases same : indexRole = role
  · simp [generatorRestriction, liftGeneratorIndex, roleEmbedding,
      relationRestriction, liftRelationIndex, same]
  · simp [generatorRestriction, liftGeneratorIndex, roleEmbedding,
      relationRestriction, liftRelationIndex, same]

theorem carrierRestriction_presentedRole
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (role : FactorRole) :
    carrierRestriction factor (presentedRole factor.advance role) =
      presentedRole factor role := by
  change Submodule.Quotient.mk
      (generatorRestriction factor
        (roleEmbedding factor.advance role (orientedRelation factor.advance))) =
    Submodule.Quotient.mk
      (roleEmbedding factor role (orientedRelation factor))
  rw [restriction_roleEmbedding, restriction_orientedRelation]

theorem carrierRestriction_component
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    carrierRestriction factor (component factor.advance) = component factor := by
  unfold component
  have boundarySquare := LinearMap.congr_fun
    (carrierRestriction_boundary_square factor)
    (presentedRole factor.advance .whole)
  simpa only [LinearMap.comp_apply, carrierRestriction_presentedRole]
    using boundarySquare

theorem carrierRestriction_reversedComponent
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    carrierRestriction factor (reversedComponent factor.advance) =
      reversedComponent factor := by
  unfold reversedComponent
  have reversalSquare := LinearMap.congr_fun
    (carrierRestriction_reversal_square factor) (component factor.advance)
  simpa only [LinearMap.comp_apply, carrierRestriction_component]
    using reversalSquare

/-- The anti-invariant evaluation-zero component is natural along the one
actual successor square. -/
theorem carrierRestriction_difference
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    carrierRestriction factor (difference factor.advance) = difference factor := by
  unfold difference
  rw [map_sub, carrierRestriction_component,
    carrierRestriction_reversedComponent]

/-- Canonical quotient evaluation turns the domain successor square into a
quotient restriction square. -/
theorem quotientRestriction_difference
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    quotientMap (carrierRestriction factor).toAddMonoidHom
        requestedPrime requestedExponent
        (quotientEvaluator factor.advance (difference factor.advance)
          requestedPrime requestedExponent) =
      quotientEvaluator factor (difference factor)
        requestedPrime requestedExponent := by
  unfold quotientEvaluator
  rw [(quotientFace factor.advance).accountedEvaluator_eq_canonical,
    (quotientFace factor).accountedEvaluator_eq_canonical]
  calc
    quotientMap (carrierRestriction factor).toAddMonoidHom
        requestedPrime requestedExponent
        (evaluator (Carrier factor.advance) (difference factor.advance)
          requestedPrime requestedExponent) =
      evaluator (Carrier factor)
        (carrierRestriction factor (difference factor.advance))
          requestedPrime requestedExponent :=
      evaluator_naturality (carrierRestriction factor).toAddMonoidHom
        (difference factor.advance) requestedPrime requestedExponent
    _ = evaluator (Carrier factor) (difference factor)
        requestedPrime requestedExponent := by
      apply congrArg (fun value => evaluator (Carrier factor) value
        requestedPrime requestedExponent)
      exact carrierRestriction_difference factor

/-- The local quotient-zero row is preserved by the successor square. -/
theorem successor_quotientZero
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    quotientMap (carrierRestriction factor).toAddMonoidHom
        requestedPrime requestedExponent
        (quotientEvaluator factor.advance (difference factor.advance)
          requestedPrime requestedExponent) = 0 := by
  rw [quotientRestriction_difference,
    difference_quotientZero factor]

end
end CanonicalUnitArithmeticFactorizationEulerLocalLandingSuccessor
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
