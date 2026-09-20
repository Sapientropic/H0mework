import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import H0mework.Arithmetic.Goldbach.EffectiveDisposition
import H0mework.Arithmetic.UnitArithmetic.CommonCarrier
import H0mework.Arithmetic.UnitArithmetic.DeterminantState

/-!
# Canonical unit arithmetic dual readouts

Formal Euler coefficients, one generated additive fibre, and the self-dual
determinant/unit coordinate are restrictions of the existing canonical unit
root.  This file creates no zeta root, Riemann state, second runtime, or
determinant.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticDualReadouts

open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticCommonDeterminantState
open CanonicalUnitArithmeticPrimePowerIncidence
open CanonicalUnitArithmeticRoot
open ArithmeticGeneration
open GradedIntegralDeterminantLine
open Polynomial
open RootArithmeticUnfoldingFace
open scoped ArithmeticFunction.zeta
open scoped ComplexConjugate

noncomputable section

/-! ## Formal Euler restriction -/

/-- Source-independent rational-prime local polynomial.  The rational prime
enters through the power-series-to-arithmetic-function support, not as a
second arithmetic source. -/
def localZetaPolynomial (_prime : Nat.Primes) : Polynomial ℤ :=
  1 - X

noncomputable def localZetaPowerSeries (prime : Nat.Primes) : PowerSeries ℤ :=
  PowerSeries.invOfUnit
    (↑(localZetaPolynomial prime) : PowerSeries ℤ) 1

noncomputable def localFormalEulerFactor (prime : Nat.Primes) :
    ArithmeticFunction ℤ :=
  ArithmeticFunction.ofPowerSeries (prime : Nat)
    (localZetaPowerSeries prime)

theorem sourceLocalFormalEulerFactor_eq (prime : Nat.Primes) :
    CanonicalUnitArithmeticCommonCarrier.sourceLocalFormalEulerFactor prime =
      localFormalEulerFactor prime := by
  rfl

/-- All-prime formal arithmetic zeta coefficients.  This is the cofinal
mathematical readout of finite unit-generated prefixes; it is not primitive
root material. -/
noncomputable def formalEulerCoefficients : ArithmeticFunction ℤ :=
  ArithmeticFunction.eulerProduct localFormalEulerFactor

/-- The authoritative Euler occurrence is the finite prefix folded from the
actual `UnitHistory` in the coordinate-free common carrier. -/
def formalEulerOccurrence : RootedAccountedUnfolding
    (DomainPoint × ArithmeticFunction ℤ) :=
  CanonicalUnitArithmeticCommonCarrier.eulerPrefixOccurrence

theorem formalEulerOccurrence_projects_to_exact_unit_root :
    formalEulerOccurrence.map Prod.fst =
      CanonicalUnitArithmeticPrimePowerIncidence.rootOccurrence := by
  exact CanonicalUnitArithmeticCommonCarrier.eulerPrefixOccurrence_projects_to_exact_unit_root

theorem localFormalEulerFactor_primePower
    (prime : Nat.Primes) (exponent : Nat) :
    localFormalEulerFactor prime ((prime : Nat) ^ exponent) =
      (localZetaPowerSeries prime).coeff exponent := by
  exact ArithmeticFunction.ofPowerSeries_apply_pow
    prime.property.one_lt (localZetaPowerSeries prime) exponent

/-- The reciprocal of the local polynomial `1 - X` is the canonical
geometric series. -/
theorem localZetaPowerSeries_eq_mk_one (prime : Nat.Primes) :
    localZetaPowerSeries prime = PowerSeries.mk 1 := by
  have constantTerm :
      PowerSeries.constantCoeff
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) = 1 := by
    simp [localZetaPolynomial]
  have inverseLaw :
      PowerSeries.invOfUnit
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) 1 *
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) = 1 :=
    PowerSeries.invOfUnit_mul _ 1 constantTerm
  have geometricLaw :
      (↑(localZetaPolynomial prime) : PowerSeries ℤ) *
          PowerSeries.mk 1 = 1 := by
    simpa [localZetaPolynomial, mul_comm] using
      PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  rw [localZetaPowerSeries]
  calc
    PowerSeries.invOfUnit
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) 1 =
        PowerSeries.invOfUnit
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) 1 * 1 :=
      (mul_one _).symm
    _ = PowerSeries.invOfUnit
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) 1 *
        ((↑(localZetaPolynomial prime) : PowerSeries ℤ) *
          PowerSeries.mk 1) := by rw [geometricLaw]
    _ = (PowerSeries.invOfUnit
          (↑(localZetaPolynomial prime) : PowerSeries ℤ) 1 *
        (↑(localZetaPolynomial prime) : PowerSeries ℤ)) *
          PowerSeries.mk 1 := by rw [mul_assoc]
    _ = PowerSeries.mk 1 := by rw [inverseLaw, one_mul]

@[simp] theorem localZetaPowerSeries_coeff
    (prime : Nat.Primes) (exponent : Nat) :
    (localZetaPowerSeries prime).coeff exponent = 1 := by
  rw [localZetaPowerSeries_eq_mk_one]
  simp

@[simp] theorem localFormalEulerFactor_apply_primePower
    (prime : Nat.Primes) (exponent : Nat) :
    localFormalEulerFactor prime ((prime : Nat) ^ exponent) = 1 := by
  rw [localFormalEulerFactor_primePower, localZetaPowerSeries_coeff]

/-- Every coefficient is eventually computed by a finite product of the
actual rational-prime local factors. -/
theorem formalEulerCoefficients_eventually_finite (n : Nat) :
    ∀ᶠ primes : Finset Nat.Primes in Filter.atTop,
      (∏ prime ∈ primes, localFormalEulerFactor prime) n =
        formalEulerCoefficients n := by
  let _ : Northcott (fun prime : Nat.Primes ↦ (prime : Nat)) :=
    { finite_le := fun bound ↦
        (Set.finite_Iic bound).preimage Subtype.val_injective.injOn }
  exact ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries
    (fun prime : Nat.Primes ↦ (prime : Nat)) localZetaPowerSeries
    (fun prime ↦ by simp [localZetaPowerSeries]) n

theorem localFormalEulerFactor_apply_one (prime : Nat.Primes) :
    localFormalEulerFactor prime 1 = 1 := by
  rw [localFormalEulerFactor, ArithmeticFunction.ofPowerSeries_apply_one]
  simp [localZetaPowerSeries]

private theorem arithmeticFunction_mul_apply_primePower
    (left right : ArithmeticFunction ℤ)
    (prime exponent : Nat) (primeIsPrime : prime.Prime) :
    (left * right) (prime ^ exponent) =
      ∑ index ∈ Finset.range (exponent + 1),
        left (prime ^ index) * right (prime ^ (exponent - index)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ left x * right y),
    Nat.sum_divisors_prime_pow primeIsPrime]
  apply Finset.sum_congr rfl
  intro index indexMem
  rw [Nat.pow_div (by simpa using indexMem) primeIsPrime.pos]

private theorem localFormalEulerFactor_apply_otherPrimePower
    (prime otherPrime : Nat.Primes) (different : prime ≠ otherPrime)
    (exponent : Nat) (exponentNonzero : exponent ≠ 0) :
    localFormalEulerFactor otherPrime ((prime : Nat) ^ exponent) = 0 := by
  rw [localFormalEulerFactor,
    ArithmeticFunction.ofPowerSeries_apply otherPrime.property.one_lt]
  have notOtherPower :
      ¬∃ otherExponent : Nat,
        (otherPrime : Nat) ^ otherExponent = (prime : Nat) ^ exponent := by
    rintro ⟨otherExponent, powerEq⟩
    have primeEq : (otherPrime : Nat) = (prime : Nat) :=
      eq_of_prime_pow_eq' otherPrime.property.prime prime.property.prime
        (Nat.pos_of_ne_zero exponentNonzero) powerEq
    exact different (Subtype.ext primeEq.symm)
  rw [Function.extend_apply' _ _ _ notOtherPower]
  rfl

private theorem finiteFormalEulerProduct_apply_one
    (primes : Finset Nat.Primes) :
    (∏ prime ∈ primes, localFormalEulerFactor prime) 1 = 1 := by
  classical
  induction primes using Finset.induction_on with
  | empty => simp
  | @insert prime primes fresh inductionHypothesis =>
      rw [Finset.prod_insert fresh, ArithmeticFunction.mul_apply_one,
        localFormalEulerFactor_apply_one, inductionHypothesis, one_mul]

private theorem finiteFormalEulerProduct_withoutPrime_apply_primePower
    (prime : Nat.Primes) (primes : Finset Nat.Primes)
    (primeAbsent : prime ∉ primes)
    (exponent : Nat) (exponentNonzero : exponent ≠ 0) :
    (∏ otherPrime ∈ primes, localFormalEulerFactor otherPrime)
        ((prime : Nat) ^ exponent) = 0 := by
  classical
  induction primes using Finset.induction_on generalizing exponent with
  | empty =>
      simp [exponentNonzero, prime.property.ne_one]
  | @insert otherPrime primes fresh inductionHypothesis =>
      have absent : prime ≠ otherPrime ∧ prime ∉ primes := by
        simpa using primeAbsent
      rw [Finset.prod_insert fresh,
        arithmeticFunction_mul_apply_primePower _ _ (prime : Nat)
          exponent prime.property]
      apply Finset.sum_eq_zero
      intro index indexMem
      by_cases indexZero : index = 0
      · subst index
        rw [pow_zero, localFormalEulerFactor_apply_one, one_mul]
        simpa using inductionHypothesis absent.2 exponent exponentNonzero
      · rw [localFormalEulerFactor_apply_otherPrimePower
          prime otherPrime absent.1 index indexZero]
        simp

private theorem finiteFormalEulerProduct_insertPrime_apply_primePower
    (prime : Nat.Primes) (primes : Finset Nat.Primes)
    (primeAbsent : prime ∉ primes) (exponent : Nat) :
    (∏ otherPrime ∈ insert prime primes,
      localFormalEulerFactor otherPrime) ((prime : Nat) ^ exponent) =
        localFormalEulerFactor prime ((prime : Nat) ^ exponent) := by
  classical
  rw [Finset.prod_insert primeAbsent,
    arithmeticFunction_mul_apply_primePower _ _ (prime : Nat)
      exponent prime.property]
  have onlyFinalIndex :
      (∑ index ∈ Finset.range (exponent + 1),
          localFormalEulerFactor prime ((prime : Nat) ^ index) *
            (∏ otherPrime ∈ primes, localFormalEulerFactor otherPrime)
              ((prime : Nat) ^ (exponent - index))) =
        localFormalEulerFactor prime ((prime : Nat) ^ exponent) := by
    calc
      _ = localFormalEulerFactor prime ((prime : Nat) ^ exponent) *
          (∏ otherPrime ∈ primes, localFormalEulerFactor otherPrime) 1 := by
        rw [Finset.sum_eq_single exponent]
        · simp
        · intro index indexMem indexNe
          have indexLe : index ≤ exponent := by simpa using indexMem
          have differenceNonzero : exponent - index ≠ 0 := by omega
          rw [finiteFormalEulerProduct_withoutPrime_apply_primePower
            prime primes primeAbsent (exponent - index) differenceNonzero]
          simp
        · simp
      _ = _ := by
        rw [finiteFormalEulerProduct_apply_one, mul_one]
  exact onlyFinalIndex

/-- Actual all-prime-to-local factorization at every prime power.  This is a
source arithmetic calculation and contains no complex coordinate. -/
theorem formalEulerCoefficients_apply_primePower
    (prime : Nat.Primes) (exponent : Nat) :
    formalEulerCoefficients ((prime : Nat) ^ exponent) =
      localFormalEulerFactor prime ((prime : Nat) ^ exponent) := by
  classical
  have eventuallyFinite :=
    formalEulerCoefficients_eventually_finite ((prime : Nat) ^ exponent)
  rw [Filter.eventually_atTop] at eventuallyFinite
  obtain ⟨primes, stable⟩ := eventuallyFinite
  have finiteValue := stable (insert prime primes) (Finset.subset_insert prime primes)
  have localValue := finiteFormalEulerProduct_insertPrime_apply_primePower
    prime (primes.erase prime) (by simp) exponent
  have sameInsert : insert prime (primes.erase prime) = insert prime primes := by
    ext otherPrime
    by_cases same : prime = otherPrime
    · simp [same]
    · have reverse : otherPrime ≠ prime := same ∘ Eq.symm
      simp [reverse]
  rw [sameInsert] at localValue
  exact finiteValue.symm.trans localValue

theorem localFormalEulerFactor_isMultiplicative (prime : Nat.Primes) :
    ArithmeticFunction.IsMultiplicative (localFormalEulerFactor prime) := by
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · exact prime.property.prime.isPrimePow
  · simp [localZetaPowerSeries]

theorem formalEulerCoefficients_isMultiplicative :
    ArithmeticFunction.IsMultiplicative formalEulerCoefficients := by
  apply ArithmeticFunction.isMultiplicative_eulerProduct
  exact localFormalEulerFactor_isMultiplicative

/-- The formal all-prime Euler occurrence is exactly the Dirichlet-convolution
zeta unit.  This is an arithmetic-function identity, not an analytic
continuation statement. -/
theorem formalEulerCoefficients_eq_zeta :
    formalEulerCoefficients = (ζ : ArithmeticFunction ℤ) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    formalEulerCoefficients formalEulerCoefficients_isMultiplicative
    (ζ : ArithmeticFunction ℤ)
    ArithmeticFunction.isMultiplicative_zeta.natCast).2
  intro prime exponent primeIsPrime
  let primePoint : Nat.Primes := ⟨prime, primeIsPrime⟩
  have primePowerNonzero : prime ^ exponent ≠ 0 :=
    pow_ne_zero exponent primeIsPrime.ne_zero
  have primePointPowerNonzero : (primePoint : Nat) ^ exponent ≠ 0 := by
    simpa [primePoint] using primePowerNonzero
  rw [show prime = (primePoint : Nat) from rfl,
    formalEulerCoefficients_apply_primePower primePoint exponent,
    localFormalEulerFactor_apply_primePower]
  rw [ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne primePointPowerNonzero]
  norm_num

theorem formalEulerCoefficients_isUnit :
    IsUnit formalEulerCoefficients := by
  rw [formalEulerCoefficients_eq_zeta]
  exact (ArithmeticFunction.zetaUnit :
    (ArithmeticFunction ℤ)ˣ).isUnit

/-- No unital multiplicative evaluator can turn the formal Euler occurrence
into a zero in a nontrivial target ring.  Therefore a classical zeta-zero
bridge, if generated, must be a derived/restriction incidence rather than an
ordinary ring-hom evaluation. -/
theorem no_unitalFormalEulerZeroEvaluation
    {Target : Type*} [Ring Target] [Nontrivial Target]
    (evaluation : ArithmeticFunction ℤ →+* Target) :
    evaluation formalEulerCoefficients ≠ 0 :=
  (formalEulerCoefficients_isUnit.map evaluation).ne_zero

/-- Exact-root ownership of the global-to-local Euler factorization. -/
structure EulerPrimePowerFactorizationAt
    (rootOccurrence : RootedAccountedUnfolding DomainPoint)
    (eulerOccurrence : RootedAccountedUnfolding
      (DomainPoint × ArithmeticFunction ℤ))
    (prime : Nat.Primes) (exponent : Nat) : Prop where
  rootProjects : eulerOccurrence.map Prod.fst = rootOccurrence
  factorizes :
    eulerOccurrence.root.2 ((prime : Nat) ^ exponent) =
      localFormalEulerFactor prime ((prime : Nat) ^ exponent)
  unitNormalization :
    IsUnit (eulerOccurrence.root.2 ((prime : Nat) ^ exponent))

/-! ## Same-occurrence effective additive calculation -/

abbrev AdditiveCalculationPoint : Type :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.AdditiveCalculationPoint

def additiveCalculationOccurrence :
    RootedAccountedUnfolding AdditiveCalculationPoint :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.additiveCalculationOccurrence

def additiveTargetHistory : UnitHistory :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.additiveTargetHistory

def leftPrimeHistory : UnitHistory :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.leftPrimeHistory

def rightPrimeHistory : UnitHistory :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.rightPrimeHistory

abbrev GoldbachAdditiveFibreAt (index : Nat) : Type :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.GoldbachAdditiveFibreAt index

def goldbachAdditiveFibre : GoldbachAdditiveFibreAt 1 :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.goldbachAdditiveFibre

@[simp] theorem additiveTargetHistory_eq_generate_four :
    additiveTargetHistory = UnitHistory.generate 4 :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.additiveTargetHistory_eq_generate_four

theorem leftPrimeHistory_isPrime :
    Nat.Prime leftPrimeHistory.cardinalShadow :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.leftPrimeHistory_isPrime

theorem rightPrimeHistory_isPrime :
    Nat.Prime rightPrimeHistory.cardinalShadow :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.rightPrimeHistory_isPrime

theorem additivePrimePair_lands :
    additiveTargetHistory = leftPrimeHistory.parallel rightPrimeHistory :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.additivePrimePair_lands

theorem additivePrimePair_siblingFold_lands :
    additiveTargetHistory =
      parallelChildren [leftPrimeHistory, rightPrimeHistory] :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.additivePrimePair_siblingFold_lands

theorem additiveCalculation_points_share_exact_root
    (point : AdditiveCalculationPoint) :
    point.rootOccurrence = initialStep.generated.occurrence :=
  CanonicalUnitArithmeticEffectiveAdditiveProducer.additiveCalculation_points_share_exact_root
    point

/-! ## Self-dual determinant restriction -/

structure SelfDualArithmeticZetaDeterminantFibreAt
    (eulerOccurrence : RootedAccountedUnfolding
      (DomainPoint × ArithmeticFunction ℤ)) : Type where
  private mk ::

def selfDualArithmeticZetaDeterminantFibre :
    SelfDualArithmeticZetaDeterminantFibreAt formalEulerOccurrence :=
  ⟨⟩

theorem selfDualFibre_preserves_reversal :
    Function.Involutive
      CanonicalUnitArithmeticCommonCarrier.reversal :=
  CanonicalUnitArithmeticCommonCarrier.reversal_involutive

/-- Classical coordinate readout of an already generated fixed point.  The
fixed-point landing itself is not a premise of the arithmetic producer. -/
theorem real_eq_half_of_complement_fixed
    (coordinate : ℂ)
    (fixed : coordinate = 1 - conj coordinate) :
    coordinate.re = 1 / 2 := by
  have realFixed := congrArg Complex.re fixed
  change coordinate.re = 1 - coordinate.re at realFixed
  linarith

theorem selfDualFibre_preserves_determinant_root :
    determinantState.determinantFace.root = commonOccurrence :=
  determinant_preserves_common_occurrence

theorem selfDualFibre_has_generated_unit :
    Module.finrank ℤ IntegralLine = 1 ∧
      Nonempty (CanonicalIntegralUnitTorsor IntegralLine) :=
  ⟨determinantState.determinantFace.integralLine_finrank,
    ⟨unitTorsor⟩⟩

/-! ## Raw runtime projections below the generated settlement facade -/

inductive CommonFace
  | goldbachAdditiveFibre
  | selfDualZetaDeterminantFibre
  deriving DecidableEq

def rawFace : CommonFace → FacadeFace
  | .goldbachAdditiveFibre => .additiveRestriction
  | .selfDualZetaDeterminantFibre => .multiplicativeRestriction

/-- This base facade recovers only the raw sibling/dependent runtime
projection and its common receipts.  In particular, the
`.goldbachAdditiveFibre` label here does not mint effective-fibre authority;
that admission is performed by
`CanonicalUnitArithmeticGeneratedSettlementFacade.goldbachCoverage`, whose
consumer depends on the actual prime-pair fibre. -/
def commonFacade : SourceNativeLivingRuntimeFacade N where
  process := CanonicalUnitArithmeticRoot.runtimeFacade.process
  FaceAt := fun _runtime => CommonFace
  componentAt := fun runtime face =>
    CanonicalUnitArithmeticRoot.runtimeFacade.componentAt runtime (rawFace face)
  installationAt := fun runtime face =>
    CanonicalUnitArithmeticRoot.runtimeFacade.installationAt runtime (rawFace face)
  projectionAt := fun runtime face =>
    CanonicalUnitArithmeticRoot.runtimeFacade.projectionAt runtime (rawFace face)

def commonFacadeSeed : LivingRuntimeState commonFacade.process :=
  commonFacade.seed

theorem coversAt_factorizes
    (runtime : LivingRuntimeState commonFacade.process)
    (face : commonFacade.FaceAt runtime) :
    commonFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up runtime.state) = ULift.up runtime.tick.generated ∧
      runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      HEq (commonFacade.readoutAt runtime face)
        (runtime.tick.generated.projectionOutcome
          ((commonFacade.installationAt runtime face).embed
            (commonFacade.projectionAt runtime face))) ∧
      runtime.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor runtime.state) :=
  commonFacade.readoutAt_factorizes runtime face

theorem both_named_faces_share_occurrence_ledger_and_next :
    commonFacadeSeed.tick.generated.occurrence =
        commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          commonFacadeSeed.current.visit.current ∧
      HEq commonFacadeSeed.tick.generated.wholeLedgerWriteBack
        (commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          commonFacadeSeed.current.visit.current) ∧
      commonFacadeSeed.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor commonFacadeSeed.state) := by
  have additiveCoverage := coversAt_factorizes commonFacadeSeed
    .goldbachAdditiveFibre
  have zetaCoverage := coversAt_factorizes commonFacadeSeed
    .selfDualZetaDeterminantFibre
  exact ⟨additiveCoverage.2.1, zetaCoverage.2.2.1,
    additiveCoverage.2.2.2.2⟩

/-- The two downstream fibres form one sealed arithmetic readout state. -/
structure CommonArithmeticReadoutStateAt
    (_additive : GoldbachAdditiveFibreAt 1)
    (_zeta : SelfDualArithmeticZetaDeterminantFibreAt
      formalEulerOccurrence) : Type where
  private mk ::

def commonArithmeticReadoutState : CommonArithmeticReadoutStateAt
    goldbachAdditiveFibre selfDualArithmeticZetaDeterminantFibre :=
  ⟨⟩

end

end CanonicalUnitArithmeticDualReadouts
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
