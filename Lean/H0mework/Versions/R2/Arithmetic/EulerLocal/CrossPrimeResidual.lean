import H0mework.Versions.R2.Arithmetic.EulerLocal.LandingSuccessor

/-!
# Cross-prime restriction obstruction for the one-factor Euler carriers

The existing successor square is exact for one fixed actual prime-power
factor and all of its later runtime occurrences.  It cannot be reused as the
cross-factor transition required by cofinal restriction-to-seed rigidity.

For the concrete `3^1` and `2^1` local carriers, any additive map preserving
their anti-invariant differences would transport the generated `3`-division
landing to the `2`-carrier.  A relation-compatible integral probe reads the
target difference as `4`, so such a landing would assert `3 ∣ 4`.

This rejects the one-factor carrier as the global stage carrier.  It does not
reject a stronger finite-prefix carrier whose full Euler/factorization
relations genuinely generate the missing transition.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationEulerCrossPrimeRestrictionObstruction

open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerLocalLanding
open PrimePowerQuotientEvaluation

noncomputable section

abbrev PrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
abbrev PrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

def twoFactor : RuntimePrimePowerFactorAt PrimeTwo 1 :=
  RuntimePrimePowerFactorAt.generate PrimeTwo 1 (by omega)

def threeFactor : RuntimePrimePowerFactorAt PrimeThree 1 :=
  RuntimePrimePowerFactorAt.generate PrimeThree 1 (by omega)

def zeroLocalExponent
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    LocalExponent factor :=
  ⟨0, Nat.succ_pos _⟩

/-- Relation-compatible probe at exponent zero and one dual coordinate.
The whole role has weight `p^k`, while the quotient-history role has weight
one, so `whole - p^k · quotientHistory` lies in its kernel. -/
def freeProbe
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) : GeneratorLattice factor →ₗ[ℤ] ℤ where
  toFun := fun value =>
    (primePower factor : ℤ) *
        value (.whole, zeroLocalExponent factor, dualIndex) +
      value (.quotientHistory, zeroLocalExponent factor, dualIndex)
  map_add' := by
    intro left right
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro scalar value
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem relationRange_le_freeProbeKernel
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) :
    LinearMap.range (relationMap factor) ≤
      LinearMap.ker (freeProbe factor dualIndex) := by
  rintro _ ⟨source, rfl⟩
  rw [LinearMap.mem_ker]
  change
    (primePower factor : ℤ) *
          source (zeroLocalExponent factor, dualIndex) +
        -((primePower factor : ℤ) *
          source (zeroLocalExponent factor, dualIndex)) = 0
  ring

def carrierProbe
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) : Carrier factor →ₗ[ℤ] ℤ :=
  (LinearMap.range (relationMap factor)).liftQ
    (freeProbe factor dualIndex)
    (relationRange_le_freeProbeKernel factor dualIndex)

theorem carrierProbe_presentedRole
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (role : CanonicalUnitArithmeticFactorizationDivisionLanding.FactorRole)
    (dualIndex : Fin 2) :
    carrierProbe factor dualIndex (presentedRole factor role) =
      if dualIndex = 0 then
        match role with
        | .whole => primePower factor
        | .quotientHistory => 1
      else 0 := by
  change freeProbe factor dualIndex
      (roleEmbedding factor role (orientedRelation factor)) = _
  fin_cases dualIndex <;> cases role <;>
    simp [freeProbe, roleEmbedding, orientedRelation,
      zeroLocalExponent]

theorem carrierProbe_euler
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) (value : Carrier factor) :
    carrierProbe factor dualIndex (carrierEuler factor value) =
      carrierProbe factor dualIndex value := by
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change freeProbe factor dualIndex (generatorEuler factor representative) =
    freeProbe factor dualIndex representative
  simp [freeProbe, generatorEuler, zeroLocalExponent,
    CanonicalUnitArithmeticFactorizationEulerOperator.localEulerCoefficient]
  have exponentSub_zero :
      exponentSub (0 : LocalExponent factor) 0 = 0 := by
    apply Fin.ext
    rfl
  rw [exponentSub_zero]

theorem carrierProbe_reversal
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent)
    (dualIndex : Fin 2) (value : Carrier factor) :
    carrierProbe factor dualIndex (carrierReversal factor value) =
      carrierProbe factor dualIndex.rev value := by
  refine Submodule.Quotient.induction_on _ value ?_
  intro representative
  change freeProbe factor dualIndex
      (generatorReversal factor representative) =
    freeProbe factor dualIndex.rev representative
  simp [freeProbe, generatorReversal, zeroLocalExponent]

theorem carrierProbe_component_zeroDual
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    carrierProbe factor 0 (component factor) = primePower factor := by
  unfold component carrierBoundary
  change carrierProbe factor 0
      (presentedRole factor .whole -
        carrierEuler factor
          (carrierReversal factor (presentedRole factor .whole))) = _
  rw [map_sub, carrierProbe_euler,
    carrierProbe_reversal, carrierProbe_presentedRole,
    carrierProbe_presentedRole]
  norm_num

theorem carrierProbe_component_oneDual
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    carrierProbe factor 1 (component factor) = -(primePower factor : ℤ) := by
  unfold component carrierBoundary
  change carrierProbe factor 1
      (presentedRole factor .whole -
        carrierEuler factor
          (carrierReversal factor (presentedRole factor .whole))) = _
  rw [map_sub, carrierProbe_euler, carrierProbe_reversal]
  have reverseOne : (1 : Fin 2).rev = 0 := by decide
  rw [reverseOne, carrierProbe_presentedRole,
    carrierProbe_presentedRole]
  norm_num

theorem carrierProbe_difference
    {requestedPrime : Nat.Primes} {requestedExponent : Nat}
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    carrierProbe factor 0 (difference factor) =
      2 * (primePower factor : ℤ) := by
  unfold difference reversedComponent
  rw [map_sub, carrierProbe_reversal,
    carrierProbe_component_zeroDual]
  have reverseZero : (0 : Fin 2).rev = 1 := by decide
  rw [reverseZero, carrierProbe_component_oneDual]
  ring

theorem twoDifference_probe_eq_four :
    carrierProbe twoFactor 0 (difference twoFactor) = 4 := by
  rw [carrierProbe_difference]
  norm_num [twoFactor, primePower]

theorem twoDifference_not_threeDivisible :
    ¬ ∃ root : Carrier twoFactor,
      3 • root = difference twoFactor := by
  rintro ⟨root, landing⟩
  have evaluated := congrArg (carrierProbe twoFactor 0) landing
  rw [map_nsmul, twoDifference_probe_eq_four] at evaluated
  change 3 * carrierProbe twoFactor 0 root = 4 at evaluated
  omega

/-- The existing one-factor carriers cannot furnish even the `3 → 2`
component-preserving transition required by a common cofinal table. -/
theorem no_threeToTwo_componentPreservingRestriction :
    ¬ ∃ restriction : Carrier threeFactor →+ Carrier twoFactor,
      restriction (difference threeFactor) = difference twoFactor := by
  rintro ⟨restriction, preserves⟩
  have localZero := difference_quotientZero threeFactor
  unfold CanonicalUnitArithmeticFactorizationEulerLocalLanding.quotientEvaluator at localZero
  rw [(quotientFace threeFactor).accountedEvaluator_eq_canonical] at localZero
  have rangeMembership :=
    PrimePowerQuotientEvaluation.rangeMembershipOfQuotientZero
      (Carrier threeFactor) (difference threeFactor) PrimeThree 1 localZero
  rcases rangeMembership with ⟨root, landing⟩
  change 3 • root = difference threeFactor at landing
  apply twoDifference_not_threeDivisible
  refine ⟨restriction root, ?_⟩
  have mapped := congrArg restriction landing
  rw [map_nsmul, preserves] at mapped
  simpa [PrimeThree] using mapped

end
end CanonicalUnitArithmeticFactorizationEulerCrossPrimeRestrictionObstruction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
