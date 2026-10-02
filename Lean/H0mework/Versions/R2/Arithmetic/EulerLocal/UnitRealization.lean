import H0mework.Versions.R2.Arithmetic.EulerLocal.CrossPrimeResidual
import H0mework.Versions.R2.Arithmetic.EulerLocal.UnitRelationHistory

/-!
# Actual local Euler realization in the unit-normalized relation history

The unit-normalized cofinal history is not reached by quotienting the old
completion.  Instead, every exact local factorization/Euler carrier has a
direct fold into the new framework-generated completion.

The two exponent-zero probes are relation-compatible and invariant under
the full local Euler convolution; reversal exchanges them.  Weighting their
two outputs by the actual quotient-history cardinality therefore gives one
linear realization whose Euler/reversal boundary is exactly the shared
cofinal component.  This is the missing local-carrier-to-common-carrier
commuting square; no faithfulness, fixedness or division root is supplied to
its mouth.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticUnitNormalizedEulerLocalRealization

open CanonicalUnitArithmeticFactorizationEulerCrossPrimeRestrictionObstruction
open CanonicalUnitArithmeticFactorizationEulerLocalLanding
open CanonicalUnitArithmeticFactorizationEulerUnitNormalizedFiniteEnvelope
open CanonicalUnitArithmeticUnitNormalizedRelationHistory
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
  (scheduledFactor scheduledPrime scheduledExponent)

noncomputable section

def localRealization (cursor : Nat) :
    Carrier (scheduledFactor cursor) →ₗ[ℤ] history.CompletionCarrier where
  toFun value :=
    ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        carrierProbe (scheduledFactor cursor) 0 value) •
          quotientUnitClassAt cursor 0 +
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        carrierProbe (scheduledFactor cursor) 1 value) •
          quotientUnitClassAt cursor 1
  map_add' := by
    intro left right
    simp only [map_add]
    module
  map_smul' := by
    intro scalar value
    simp only [map_smul, smul_eq_mul]
    module

theorem localRealization_apply (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    localRealization cursor value =
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        carrierProbe (scheduledFactor cursor) 0 value) •
          quotientUnitClassAt cursor 0 +
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        carrierProbe (scheduledFactor cursor) 1 value) •
          quotientUnitClassAt cursor 1 :=
  rfl

/-- Full Euler convolution is consumed before the finite unit-normalized
readout; it is not replaced by a submitted evaluator table. -/
theorem localRealization_euler (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    localRealization cursor
        (carrierEuler (scheduledFactor cursor) value) =
      localRealization cursor value := by
  rw [localRealization_apply, localRealization_apply,
    carrierProbe_euler, carrierProbe_euler]

def reversedRealization (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    history.CompletionCarrier :=
  ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
      carrierProbe (scheduledFactor cursor) 1 value) •
        quotientUnitClassAt cursor 0 +
    ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
      carrierProbe (scheduledFactor cursor) 0 value) •
        quotientUnitClassAt cursor 1

/-- Reversal exchanges the two actual probe coordinates. -/
theorem localRealization_reversal (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    localRealization cursor
        (carrierReversal (scheduledFactor cursor) value) =
      reversedRealization cursor value := by
  rw [localRealization_apply]
  unfold reversedRealization
  rw [carrierProbe_reversal, carrierProbe_reversal]
  have reverseZero : (0 : Fin 2).rev = 1 := by decide
  have reverseOne : (1 : Fin 2).rev = 0 := by decide
  rw [reverseZero, reverseOne]

/-- The actual coupled boundary descends to the difference of the two
unit-normalized readouts. -/
theorem localRealization_boundary (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    localRealization cursor
        (carrierBoundary (scheduledFactor cursor) value) =
      localRealization cursor value - reversedRealization cursor value := by
  change localRealization cursor
      (value - carrierEuler (scheduledFactor cursor)
        (carrierReversal (scheduledFactor cursor) value)) = _
  rw [map_sub, localRealization_euler, localRealization_reversal]

theorem localRealization_presentedWhole (cursor : Nat) :
    localRealization cursor
        (presentedRole (scheduledFactor cursor) .whole) =
      normalizedComponentAt cursor 0 := by
  rw [localRealization_apply,
    carrierProbe_presentedRole, carrierProbe_presentedRole]
  norm_num
  unfold normalizedComponentAt
  rw [wholeUnitCoefficient_eq_primePower_mul_quotient]
  simp only [primePower, Int.natCast_pow]
  module

theorem reversedRealization_presentedWhole (cursor : Nat) :
    reversedRealization cursor
        (presentedRole (scheduledFactor cursor) .whole) =
      normalizedComponentAt cursor 1 := by
  unfold reversedRealization
  rw [carrierProbe_presentedRole, carrierProbe_presentedRole]
  norm_num
  unfold normalizedComponentAt
  rw [wholeUnitCoefficient_eq_primePower_mul_quotient]
  simp only [primePower, Int.natCast_pow]
  module

/-- The local full-Euler evaluation-zero component lands on the exact shared
component generated by the direct unit-normalized history. -/
theorem localRealization_component (cursor : Nat) :
    localRealization cursor (component (scheduledFactor cursor)) =
      globalComponent := by
  unfold component
  rw [localRealization_boundary,
    localRealization_presentedWhole,
    reversedRealization_presentedWhole,
    normalizedComponent_difference_eq_global]

theorem localRealization_component_zero (cursor : Nat) :
    localRealization cursor (component (scheduledFactor cursor)) = 0 := by
  rw [localRealization_component, globalComponent_eq_zero]

/-- The realization map itself is installed at the same exact factorization
occurrence as the local Euler carrier. -/
def realizationOccurrence (cursor : Nat) : RootedAccountedUnfolding
    (CanonicalUnitArithmeticUnitNormalizedRelationHistory.FactorizationRoot ×
      (Carrier (scheduledFactor cursor) →ₗ[ℤ]
        history.CompletionCarrier)) :=
  (CanonicalUnitArithmeticFactorizationOccurrence.factorizationOccurrence
      (scheduledFactor cursor).stage).map fun root =>
    (root, localRealization cursor)

theorem realizationOccurrence_projects_to_factorization (cursor : Nat) :
    (realizationOccurrence cursor).map Prod.fst =
      CanonicalUnitArithmeticFactorizationOccurrence.factorizationOccurrence
        (scheduledFactor cursor).stage := by
  rw [realizationOccurrence, RootedAccountedUnfolding.map_map]
  change
    (CanonicalUnitArithmeticFactorizationOccurrence.factorizationOccurrence
      (scheduledFactor cursor).stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem actual_local_euler_reversal_evaluator_square (cursor : Nat) :
    (localRealization cursor
        (carrierEuler (scheduledFactor cursor)
          (presentedRole (scheduledFactor cursor) .whole)) =
      localRealization cursor
        (presentedRole (scheduledFactor cursor) .whole)) ∧
    (localRealization cursor
        (carrierReversal (scheduledFactor cursor)
          (presentedRole (scheduledFactor cursor) .whole)) =
      reversedRealization cursor
        (presentedRole (scheduledFactor cursor) .whole)) ∧
    (localRealization cursor (component (scheduledFactor cursor)) =
      globalComponent) :=
  ⟨localRealization_euler cursor _,
    localRealization_reversal cursor _,
    localRealization_component cursor⟩

/-! ## Nontrivial two-exponent Euler readout -/

/-- Every scheduled factor has a genuine exponent-one coordinate. -/
def localExponentOne (cursor : Nat) :
    LocalExponent (scheduledFactor cursor) := by
  refine ⟨1, ?_⟩
  have positive := CanonicalUnitArithmeticFactorizationOccurrence.multiplicity_pos
    (CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory
      (scheduledFactor cursor).stage)
    (scheduledFactor cursor).primeIndex
  omega

/-- Relation-compatible probe at an arbitrary local exponent coordinate. -/
def freeProbeAt (cursor : Nat)
    (localExponent : LocalExponent (scheduledFactor cursor))
    (dualIndex : Fin 2) :
    GeneratorLattice (scheduledFactor cursor) →ₗ[ℤ] ℤ where
  toFun value :=
    (primePower (scheduledFactor cursor) : ℤ) *
        value (.whole, localExponent, dualIndex) +
      value (.quotientHistory, localExponent, dualIndex)
  map_add' := by
    intro left right
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro scalar value
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem relationRange_le_freeProbeAtKernel (cursor : Nat)
    (localExponent : LocalExponent (scheduledFactor cursor))
    (dualIndex : Fin 2) :
    LinearMap.range (relationMap (scheduledFactor cursor)) ≤
      LinearMap.ker (freeProbeAt cursor localExponent dualIndex) := by
  rintro _ ⟨source, rfl⟩
  rw [LinearMap.mem_ker]
  change
    (primePower (scheduledFactor cursor) : ℤ) *
          source (localExponent, dualIndex) +
        -((primePower (scheduledFactor cursor) : ℤ) *
          source (localExponent, dualIndex)) = 0
  ring

def carrierProbeAt (cursor : Nat)
    (localExponent : LocalExponent (scheduledFactor cursor))
    (dualIndex : Fin 2) :
    Carrier (scheduledFactor cursor) →ₗ[ℤ] ℤ :=
  (LinearMap.range (relationMap (scheduledFactor cursor))).liftQ
    (freeProbeAt cursor localExponent dualIndex)
    (relationRange_le_freeProbeAtKernel cursor localExponent dualIndex)

theorem carrierProbeAt_presentedRole (cursor : Nat)
    (localExponent : LocalExponent (scheduledFactor cursor))
    (role : CanonicalUnitArithmeticFactorizationDivisionLanding.FactorRole)
    (dualIndex : Fin 2) :
    carrierProbeAt cursor localExponent dualIndex
        (presentedRole (scheduledFactor cursor) role) =
      if dualIndex = 0 then
        match role with
        | .whole => primePower (scheduledFactor cursor)
        | .quotientHistory => 1
      else 0 := by
  change freeProbeAt cursor localExponent dualIndex
      (roleEmbedding (scheduledFactor cursor) role
        (orientedRelation (scheduledFactor cursor))) = _
  fin_cases dualIndex <;> cases role <;>
    simp [freeProbeAt, roleEmbedding, orientedRelation]

theorem carrierProbeAt_reversal (cursor : Nat)
    (localExponent : LocalExponent (scheduledFactor cursor))
    (dualIndex : Fin 2) (value : Carrier (scheduledFactor cursor)) :
    carrierProbeAt cursor localExponent dualIndex
        (carrierReversal (scheduledFactor cursor) value) =
      carrierProbeAt cursor localExponent dualIndex.rev value := by
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change freeProbeAt cursor localExponent dualIndex
      (generatorReversal (scheduledFactor cursor) representative) =
    freeProbeAt cursor localExponent dualIndex.rev representative
  simp [freeProbeAt, generatorReversal]

theorem exponentSub_one_zero (cursor : Nat) :
    exponentSub (localExponentOne cursor) 0 = localExponentOne cursor := by
  apply Fin.ext
  rfl

theorem exponentSub_one_one (cursor : Nat) :
    exponentSub (localExponentOne cursor) 1 =
      zeroLocalExponent (scheduledFactor cursor) := by
  apply Fin.ext
  rfl

/-- At exponent one the genuine Euler convolution reads both exponent-one
and exponent-zero coordinates.  Bare reversal has no such term. -/
theorem carrierProbeAt_euler_one (cursor : Nat) (dualIndex : Fin 2)
    (value : Carrier (scheduledFactor cursor)) :
    carrierProbeAt cursor (localExponentOne cursor) dualIndex
        (carrierEuler (scheduledFactor cursor) value) =
      carrierProbeAt cursor (localExponentOne cursor) dualIndex value +
        carrierProbe (scheduledFactor cursor) dualIndex value := by
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change freeProbeAt cursor (localExponentOne cursor) dualIndex
      (generatorEuler (scheduledFactor cursor) representative) =
    freeProbeAt cursor (localExponentOne cursor) dualIndex representative +
      freeProbe (scheduledFactor cursor) dualIndex representative
  unfold freeProbeAt freeProbe generatorEuler
  simp only [
    CanonicalUnitArithmeticFactorizationEulerOperator.localEulerCoefficient,
    one_mul]
  change
    (primePower (scheduledFactor cursor) : ℤ) *
          (∑ amount ∈ Finset.range 2,
            representative (.whole,
              exponentSub (localExponentOne cursor) amount, dualIndex)) +
        (∑ amount ∈ Finset.range 2,
          representative (.quotientHistory,
            exponentSub (localExponentOne cursor) amount, dualIndex)) =
      ((primePower (scheduledFactor cursor) : ℤ) *
          representative (.whole, localExponentOne cursor, dualIndex) +
        representative (.quotientHistory,
          localExponentOne cursor, dualIndex)) +
      ((primePower (scheduledFactor cursor) : ℤ) *
          representative (.whole,
            zeroLocalExponent (scheduledFactor cursor), dualIndex) +
        representative (.quotientHistory,
          zeroLocalExponent (scheduledFactor cursor), dualIndex))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    exponentSub_one_zero, exponentSub_one_one]
  ring

def twoLevelRealization (cursor : Nat) :
    Carrier (scheduledFactor cursor) →ₗ[ℤ]
      CanonicalUnitArithmeticUnitNormalizedRelationHistory.history.CompletionCarrier where
  toFun value :=
    ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
      (carrierProbe (scheduledFactor cursor) 0 value +
        carrierProbeAt cursor (localExponentOne cursor) 0 value)) •
          quotientUnitClassAt cursor 0 +
    ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
      (carrierProbe (scheduledFactor cursor) 1 value +
        carrierProbeAt cursor (localExponentOne cursor) 1 value)) •
          quotientUnitClassAt cursor 1
  map_add' := by
    intro left right
    simp only [map_add]
    module
  map_smul' := by
    intro scalar value
    simp only [map_smul, smul_eq_mul]
    module

theorem twoLevelRealization_apply (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    twoLevelRealization cursor value =
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        (carrierProbe (scheduledFactor cursor) 0 value +
          carrierProbeAt cursor (localExponentOne cursor) 0 value)) •
            quotientUnitClassAt cursor 0 +
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        (carrierProbe (scheduledFactor cursor) 1 value +
          carrierProbeAt cursor (localExponentOne cursor) 1 value)) •
            quotientUnitClassAt cursor 1 :=
  rfl

theorem twoLevelRealization_reversal (cursor : Nat)
    (value : Carrier (scheduledFactor cursor)) :
    twoLevelRealization cursor
        (carrierReversal (scheduledFactor cursor) value) =
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        (carrierProbe (scheduledFactor cursor) 1 value +
          carrierProbeAt cursor (localExponentOne cursor) 1 value)) •
            quotientUnitClassAt cursor 0 +
      ((quotientUnitCoefficient (scheduledFactor cursor) : ℤ) *
        (carrierProbe (scheduledFactor cursor) 0 value +
          carrierProbeAt cursor (localExponentOne cursor) 0 value)) •
            quotientUnitClassAt cursor 1 := by
  rw [twoLevelRealization_apply]
  rw [carrierProbe_reversal, carrierProbe_reversal,
    carrierProbeAt_reversal, carrierProbeAt_reversal]
  have reverseZero : (0 : Fin 2).rev = 1 := by decide
  have reverseOne : (1 : Fin 2).rev = 0 := by decide
  rw [reverseZero, reverseOne]

theorem carrierProbeAt_one_component_zeroDual (cursor : Nat) :
    carrierProbeAt cursor (localExponentOne cursor) 0
        (component (scheduledFactor cursor)) =
      primePower (scheduledFactor cursor) := by
  unfold component carrierBoundary
  change carrierProbeAt cursor (localExponentOne cursor) 0
      (presentedRole (scheduledFactor cursor) .whole -
        carrierEuler (scheduledFactor cursor)
          (carrierReversal (scheduledFactor cursor)
            (presentedRole (scheduledFactor cursor) .whole))) = _
  rw [map_sub, carrierProbeAt_euler_one,
    carrierProbeAt_reversal, carrierProbe_reversal,
    carrierProbeAt_presentedRole, carrierProbeAt_presentedRole]
  have reverseZero : (0 : Fin 2).rev = 1 := by decide
  rw [reverseZero]
  simp
  rw [carrierProbe_presentedRole]
  norm_num

theorem carrierProbeAt_one_component_oneDual (cursor : Nat) :
    carrierProbeAt cursor (localExponentOne cursor) 1
        (component (scheduledFactor cursor)) =
      -(2 * (primePower (scheduledFactor cursor) : ℤ)) := by
  unfold component carrierBoundary
  change carrierProbeAt cursor (localExponentOne cursor) 1
      (presentedRole (scheduledFactor cursor) .whole -
        carrierEuler (scheduledFactor cursor)
          (carrierReversal (scheduledFactor cursor)
            (presentedRole (scheduledFactor cursor) .whole))) = _
  rw [map_sub, carrierProbeAt_euler_one,
    carrierProbeAt_reversal, carrierProbe_reversal]
  have reverseOne : (1 : Fin 2).rev = 0 := by decide
  rw [reverseOne, carrierProbeAt_presentedRole,
    carrierProbeAt_presentedRole]
  simp
  rw [carrierProbe_presentedRole]
  simp
  ring

/-- The nontrivial Euler component uses coefficients `2` and `-3`; bare
reversal would give `2` and `-2`. -/
theorem twoLevelRealization_component (cursor : Nat) :
    twoLevelRealization cursor (component (scheduledFactor cursor)) =
      2 • normalizedComponentAt cursor 0 -
        3 • normalizedComponentAt cursor 1 := by
  rw [twoLevelRealization_apply,
    carrierProbe_component_zeroDual,
    carrierProbe_component_oneDual,
    carrierProbeAt_one_component_zeroDual,
    carrierProbeAt_one_component_oneDual]
  unfold normalizedComponentAt
  rw [wholeUnitCoefficient_eq_primePower_mul_quotient]
  simp only [primePower, Int.natCast_pow]
  module

theorem twoLevelRealization_reversedComponent (cursor : Nat) :
    twoLevelRealization cursor
        (reversedComponent (scheduledFactor cursor)) =
      -(3 • normalizedComponentAt cursor 0) +
        2 • normalizedComponentAt cursor 1 := by
  unfold reversedComponent
  rw [twoLevelRealization_reversal,
    carrierProbe_component_zeroDual,
    carrierProbe_component_oneDual,
    carrierProbeAt_one_component_zeroDual,
    carrierProbeAt_one_component_oneDual]
  unfold normalizedComponentAt
  rw [wholeUnitCoefficient_eq_primePower_mul_quotient]
  simp only [primePower, Int.natCast_pow]
  module

theorem twoLevelRealization_difference (cursor : Nat) :
    twoLevelRealization cursor (difference (scheduledFactor cursor)) =
      5 • globalComponent := by
  unfold difference
  rw [map_sub, twoLevelRealization_component,
    twoLevelRealization_reversedComponent]
  calc
    2 • normalizedComponentAt cursor 0 -
          3 • normalizedComponentAt cursor 1 -
        (-(3 • normalizedComponentAt cursor 0) +
          2 • normalizedComponentAt cursor 1) =
        5 • (normalizedComponentAt cursor 0 -
          normalizedComponentAt cursor 1) := by module
    _ = 5 • globalComponent := by
      rw [normalizedComponent_difference_eq_global]

theorem twoLevelRealization_difference_zero (cursor : Nat) :
    twoLevelRealization cursor (difference (scheduledFactor cursor)) = 0 := by
  rw [twoLevelRealization_difference, globalComponent_eq_zero, smul_zero]

/-- The actual full-Euler component and its reversal become one generated
fixed component in the common arithmetic completion. -/
theorem twoLevelRealization_generatedFixedComponent (cursor : Nat) :
    twoLevelRealization cursor (component (scheduledFactor cursor)) =
      twoLevelRealization cursor
        (reversedComponent (scheduledFactor cursor)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact twoLevelRealization_difference_zero cursor

/-- The local oriented test difference itself is nonzero.  Hence the
unit-normalized realization is an incidence/readout, not a faithful
realization of the one-factor Euler carrier. -/
theorem localDifference_ne_zero (cursor : Nat) :
    difference (scheduledFactor cursor) ≠ 0 := by
  intro differenceZero
  have evaluated := congrArg
    (carrierProbe (scheduledFactor cursor) 0) differenceZero
  rw [carrierProbe_difference, map_zero] at evaluated
  have primePowerPositive :
      0 < primePower (scheduledFactor cursor) := by
    unfold primePower
    exact pow_pos
      (RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure.scheduledPrime
        cursor).property.pos _
  have nonzero :
      (2 * (primePower (scheduledFactor cursor) : ℤ)) ≠ 0 := by
    exact_mod_cast (mul_pos (by omega : 0 < 2) primePowerPositive).ne'
  exact nonzero evaluated

theorem twoLevelRealization_not_injective (cursor : Nat) :
    ¬ Function.Injective (twoLevelRealization cursor) := by
  intro injective
  apply localDifference_ne_zero cursor
  apply injective
  rw [twoLevelRealization_difference_zero, map_zero]

end

end CanonicalUnitArithmeticUnitNormalizedEulerLocalRealization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
