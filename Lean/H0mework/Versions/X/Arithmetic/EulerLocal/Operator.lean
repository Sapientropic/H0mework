import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import H0mework.Versions.X.Arithmetic.UnitArithmetic.Factorization
import H0mework.Realization.Completion.PrimePowerQuotient
import H0mework.Foundation.Relations.FiniteDefectDeterminant

/-!
# Factorization-born finite Euler/reversal operator

The prime and exponent axes of this stage are the actual support and
multiplicity of the dependent factorial fold carried by one exact runtime
factorization occurrence.  No prime enumeration occurs in the carrier.

The local Euler operator is the full truncated convolution by the inverse of
`1-X`; reversal flips the dual bit; their coupled action is
`EulerConvolution ∘ reversal`.  A zero-relation finite presentation owns the
finite-free carrier and its FG instance, after which the generic arithmetic
kernel installs the canonical family of all prime-power quotient evaluators.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationEulerOperator

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open FiniteDefectDeterminant
open Polynomial
open PrimePowerKernelIncidenceRigidity
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt
open PrimePowerQuotientEvaluation
open PrimePowerQuotientEvaluation.RootGeneratedPrimePowerQuotientEvaluationAt

noncomputable section

abbrev StageRoot :=
  Σ authority : RuntimeAuthority,
    GeneratedUnitFactorizationAt (authorityWholeHistory authority)

abbrev StageHistory (stage : Nat) : UnitHistory :=
  authorityWholeHistory (factorizationOccurrence stage).root.1

def stageFactorization (stage : Nat) :
    GeneratedUnitFactorizationAt (StageHistory stage) :=
  (factorizationOccurrence stage).root.2

@[simp] theorem stageHistory_eq_runtimeWholeHistory (stage : Nat) :
    StageHistory stage = runtimeWholeHistory stage :=
  rfl

@[simp] theorem stageHistory_cardinalShadow (stage : Nat) :
    (StageHistory stage).cardinalShadow = stage + 2 := by
  rw [stageHistory_eq_runtimeWholeHistory,
    runtimeWholeHistory_cardinalShadow]

abbrev StagePrime (stage : Nat) := PrimeIndex (StageHistory stage)

abbrev StageExponent (stage : Nat) (primeIndex : StagePrime stage) :=
  Fin (multiplicity (StageHistory stage) primeIndex + 1)

abbrev EulerIndex (stage : Nat) :=
  Σ primeIndex : StagePrime stage, StageExponent stage primeIndex × Fin 2

abbrev EulerLattice (stage : Nat) := EulerIndex stage → ℤ

def exponentSub {stage : Nat} {primeIndex : StagePrime stage}
    (localExponent : StageExponent stage primeIndex) (amount : Nat) :
    StageExponent stage primeIndex :=
  ⟨localExponent - amount,
    (Nat.sub_le localExponent amount).trans_lt localExponent.isLt⟩

/-! ## Actual local Euler factor -/

def localEulerPolynomial (_prime : Nat.Primes) : Polynomial ℤ :=
  1 - X

noncomputable def localEulerPowerSeries (prime : Nat.Primes) :
    PowerSeries ℤ :=
  PowerSeries.invOfUnit
    (↑(localEulerPolynomial prime) : PowerSeries ℤ) 1

theorem localEulerPowerSeries_eq_mk_one (prime : Nat.Primes) :
    localEulerPowerSeries prime = PowerSeries.mk 1 := by
  have constantTerm :
      PowerSeries.constantCoeff
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) = 1 := by
    simp [localEulerPolynomial]
  have inverseLaw :
      PowerSeries.invOfUnit
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) 1 *
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) = 1 :=
    PowerSeries.invOfUnit_mul _ 1 constantTerm
  have geometricLaw :
      (↑(localEulerPolynomial prime) : PowerSeries ℤ) *
          PowerSeries.mk 1 = 1 := by
    simpa [localEulerPolynomial, mul_comm] using
      PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  rw [localEulerPowerSeries]
  calc
    PowerSeries.invOfUnit
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) 1 =
        PowerSeries.invOfUnit
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) 1 * 1 :=
      (mul_one _).symm
    _ = PowerSeries.invOfUnit
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) 1 *
        ((↑(localEulerPolynomial prime) : PowerSeries ℤ) *
          PowerSeries.mk 1) := by rw [geometricLaw]
    _ = (PowerSeries.invOfUnit
          (↑(localEulerPolynomial prime) : PowerSeries ℤ) 1 *
        (↑(localEulerPolynomial prime) : PowerSeries ℤ)) *
          PowerSeries.mk 1 := by rw [mul_assoc]
    _ = PowerSeries.mk 1 := by rw [inverseLaw, one_mul]

@[simp] theorem localEulerCoefficient
    (prime : Nat.Primes) (localExponent : Nat) :
    (localEulerPowerSeries prime).coeff localExponent = 1 := by
  rw [localEulerPowerSeries_eq_mk_one]
  simp

def localPolynomialCoefficient
    (prime : Nat.Primes) (localExponent : Nat) : ℤ :=
  (localEulerPolynomial prime).coeff localExponent

@[simp] theorem localPolynomialCoefficient_zero (prime : Nat.Primes) :
    localPolynomialCoefficient prime 0 = 1 := by
  simp [localPolynomialCoefficient, localEulerPolynomial]

@[simp] theorem localPolynomialCoefficient_one (prime : Nat.Primes) :
    localPolynomialCoefficient prime 1 = -1 := by
  simp [localPolynomialCoefficient, localEulerPolynomial,
    Polynomial.coeff_one]

@[simp] theorem localPolynomialCoefficient_of_two_le
    (prime : Nat.Primes) (localExponent : Nat) (large : 2 ≤ localExponent) :
    localPolynomialCoefficient prime localExponent = 0 := by
  simp [localPolynomialCoefficient, localEulerPolynomial,
    Polynomial.coeff_X, Polynomial.coeff_one,
    (show localExponent ≠ 0 by omega),
    (show (1 : Nat) ≠ localExponent by omega)]

/-! ## Coupled action on actual factorization indices -/

def localEulerOperator (stage : Nat) :
    EulerLattice stage →ₗ[ℤ] EulerLattice stage where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      (localEulerPowerSeries
          ((stageFactorization stage).actualPrime index.1)).coeff amount *
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    simp [mul_left_comm]

theorem localEulerOperator_apply (stage : Nat) (value : EulerLattice stage)
    (index : EulerIndex stage) :
    localEulerOperator stage value index =
      ∑ amount ∈ Finset.range (index.2.1 + 1),
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩ := by
  change
    (∑ amount ∈ Finset.range (index.2.1 + 1),
      (localEulerPowerSeries
          ((stageFactorization stage).actualPrime index.1)).coeff amount *
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩) = _
  apply Finset.sum_congr rfl
  intro amount _membership
  rw [localEulerCoefficient, one_mul]

def exponentZero (stage : Nat) (primeIndex : StagePrime stage) :
    StageExponent stage primeIndex :=
  ⟨0, Nat.zero_lt_succ _⟩

def exponentOne (stage : Nat) (primeIndex : StagePrime stage) :
    StageExponent stage primeIndex := by
  refine ⟨1, ?_⟩
  have positive := multiplicity_pos (StageHistory stage) primeIndex
  omega

def exponentZeroBasis (stage : Nat) (primeIndex : StagePrime stage)
    (dualIndex : Fin 2) : EulerLattice stage :=
  Pi.single ⟨primeIndex, exponentZero stage primeIndex, dualIndex⟩ 1

def localEulerPolynomialOperator (stage : Nat) :
    EulerLattice stage →ₗ[ℤ] EulerLattice stage where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      localPolynomialCoefficient
          ((stageFactorization stage).actualPrime index.1) amount *
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    simp [mul_left_comm]

def reversal (stage : Nat) :
    EulerLattice stage →ₗ[ℤ] EulerLattice stage where
  toFun := fun value index =>
    value ⟨index.1, index.2.1, index.2.2.rev⟩
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem reversal_involutive (stage : Nat) :
    Function.Involutive (reversal stage) := by
  intro value
  funext index
  simp [reversal]

/-- Non-degeneration kill test: the actual factorization multiplicity gives
an exponent-one coordinate.  Euler convolution propagates an exponent-zero
basis vector to it, while bare reversal cannot change exponent. -/
theorem localEulerOperator_differs_from_bare_reversal
    (stage : Nat) (primeIndex : StagePrime stage) (dualIndex : Fin 2) :
    localEulerOperator stage
        (exponentZeroBasis stage primeIndex dualIndex)
        ⟨primeIndex, exponentOne stage primeIndex, dualIndex⟩ = 1 ∧
      reversal stage
        (exponentZeroBasis stage primeIndex dualIndex)
        ⟨primeIndex, exponentOne stage primeIndex, dualIndex⟩ = 0 := by
  classical
  have subZero :
      exponentSub (exponentOne stage primeIndex) 0 =
        exponentOne stage primeIndex := by
    apply Fin.ext
    rfl
  have subOne :
      exponentSub (exponentOne stage primeIndex) 1 =
        exponentZero stage primeIndex := by
    apply Fin.ext
    rfl
  have basisAtZero :
      exponentZeroBasis stage primeIndex dualIndex
        ⟨primeIndex, exponentZero stage primeIndex, dualIndex⟩ = 1 := by
    simp [exponentZeroBasis]
  have basisAtOne (otherDual : Fin 2) :
      exponentZeroBasis stage primeIndex dualIndex
        ⟨primeIndex, exponentOne stage primeIndex, otherDual⟩ = 0 := by
    have indexDifferent :
        (⟨primeIndex, exponentZero stage primeIndex, dualIndex⟩ :
          EulerIndex stage) ≠
        ⟨primeIndex, exponentOne stage primeIndex, otherDual⟩ := by
      intro equality
      have exponentEquality := congrArg
        (fun index : EulerIndex stage => index.2.1.val) equality
      change 0 = 1 at exponentEquality
      omega
    simp [exponentZeroBasis, indexDifferent]
  constructor
  · rw [localEulerOperator_apply]
    rw [show (exponentOne stage primeIndex : Nat) + 1 = 2 by rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    rw [subZero, subOne, basisAtOne, basisAtZero]
    norm_num
  · exact basisAtOne dualIndex.rev

def eulerReversalAction (stage : Nat) :
    EulerLattice stage →ₗ[ℤ] EulerLattice stage :=
  (localEulerOperator stage).comp (reversal stage)

def boundary (stage : Nat) :
    EulerLattice stage →ₗ[ℤ] EulerLattice stage :=
  LinearMap.id - eulerReversalAction stage

/-! ## Actual factorization inclusions and restriction squares -/

theorem factorization_mono_succ (stage : Nat) :
    factorization (StageHistory stage) ≤
      factorization (StageHistory (stage + 1)) := by
  rw [factorization_eq_cardinal_factorization,
    factorization_eq_cardinal_factorization]
  apply (Nat.factorization_le_iff_dvd
    (Nat.factorial_ne_zero (StageHistory stage).cardinalShadow)
    (Nat.factorial_ne_zero
      (StageHistory (stage + 1)).cardinalShadow)).2
  apply Nat.factorial_dvd_factorial
  rw [stageHistory_cardinalShadow, stageHistory_cardinalShadow]
  omega

def liftPrime (stage : Nat) (primeIndex : StagePrime stage) :
    StagePrime (stage + 1) := by
  refine ⟨primeIndex.1, Finsupp.mem_support_iff.mpr ?_⟩
  have oldNonzero : factorization (StageHistory stage) primeIndex.1 ≠ 0 :=
    Finsupp.mem_support_iff.mp primeIndex.2
  have order := factorization_mono_succ stage primeIndex.1
  omega

@[simp] theorem liftPrime_value (stage : Nat)
    (primeIndex : StagePrime stage) :
    (liftPrime stage primeIndex).1 = primeIndex.1 :=
  rfl

theorem liftPrime_actualPrime (stage : Nat)
    (primeIndex : StagePrime stage) :
    (stageFactorization (stage + 1)).actualPrime
        (liftPrime stage primeIndex) =
      (stageFactorization stage).actualPrime primeIndex := by
  apply Subtype.ext
  rfl

def liftExponent (stage : Nat) (primeIndex : StagePrime stage)
    (localExponent : StageExponent stage primeIndex) :
    StageExponent (stage + 1) (liftPrime stage primeIndex) := by
  refine ⟨localExponent.1, ?_⟩
  have order := factorization_mono_succ stage primeIndex.1
  change localExponent.1 <
    factorization (StageHistory (stage + 1)) primeIndex.1 + 1
  have oldBound := localExponent.2
  change localExponent.1 <
    factorization (StageHistory stage) primeIndex.1 + 1 at oldBound
  omega

@[simp] theorem liftExponent_value (stage : Nat)
    (primeIndex : StagePrime stage)
    (localExponent : StageExponent stage primeIndex) :
    (liftExponent stage primeIndex localExponent).1 = localExponent.1 :=
  rfl

theorem exponentSub_liftExponent (stage : Nat)
    (primeIndex : StagePrime stage)
    (localExponent : StageExponent stage primeIndex) (amount : Nat) :
    exponentSub (liftExponent stage primeIndex localExponent) amount =
      liftExponent stage primeIndex (exponentSub localExponent amount) := by
  apply Fin.ext
  rfl

def liftIndex (stage : Nat) : EulerIndex stage → EulerIndex (stage + 1)
  | ⟨primeIndex, localExponent, dualIndex⟩ =>
      ⟨liftPrime stage primeIndex,
        liftExponent stage primeIndex localExponent, dualIndex⟩

def restriction (stage : Nat) :
    EulerLattice (stage + 1) →ₗ[ℤ] EulerLattice stage where
  toFun := fun value index => value (liftIndex stage index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem restriction_euler_square (stage : Nat) :
    (restriction stage).comp (localEulerOperator (stage + 1)) =
      (localEulerOperator stage).comp (restriction stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, localExponent, dualIndex⟩
  simp only [LinearMap.comp_apply]
  change
    localEulerOperator (stage + 1) value
        ⟨liftPrime stage primeIndex,
          liftExponent stage primeIndex localExponent, dualIndex⟩ =
      localEulerOperator stage (restriction stage value)
        ⟨primeIndex, localExponent, dualIndex⟩
  rw [localEulerOperator_apply, localEulerOperator_apply]
  apply Finset.sum_congr rfl
  intro amount _membership
  change
    value ⟨liftPrime stage primeIndex,
        exponentSub (liftExponent stage primeIndex localExponent) amount,
        dualIndex⟩ =
      value ⟨liftPrime stage primeIndex,
        liftExponent stage primeIndex
          (exponentSub localExponent amount), dualIndex⟩
  rw [exponentSub_liftExponent]

theorem restriction_polynomial_square (stage : Nat) :
    (restriction stage).comp (localEulerPolynomialOperator (stage + 1)) =
      (localEulerPolynomialOperator stage).comp (restriction stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, localExponent, dualIndex⟩
  change
    (∑ amount ∈ Finset.range (localExponent.1 + 1),
      localPolynomialCoefficient
          ((stageFactorization (stage + 1)).actualPrime
            (liftPrime stage primeIndex)) amount *
        value ⟨liftPrime stage primeIndex,
          exponentSub (liftExponent stage primeIndex localExponent) amount,
          dualIndex⟩) =
    ∑ amount ∈ Finset.range (localExponent.1 + 1),
      localPolynomialCoefficient
          ((stageFactorization stage).actualPrime primeIndex) amount *
        value ⟨liftPrime stage primeIndex,
          liftExponent stage primeIndex
            (exponentSub localExponent amount), dualIndex⟩
  apply Finset.sum_congr rfl
  intro amount _membership
  rw [liftPrime_actualPrime, exponentSub_liftExponent]

theorem restriction_reversal_square (stage : Nat) :
    (restriction stage).comp (reversal (stage + 1)) =
      (reversal stage).comp (restriction stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rfl

theorem restriction_action_square (stage : Nat) :
    (restriction stage).comp (eulerReversalAction (stage + 1)) =
      (eulerReversalAction stage).comp (restriction stage) := by
  apply LinearMap.ext
  intro value
  have eulerSquare := LinearMap.congr_fun
    (restriction_euler_square stage) (reversal (stage + 1) value)
  have reversalSquare := LinearMap.congr_fun
    (restriction_reversal_square stage) value
  change
    restriction stage
        (localEulerOperator (stage + 1) (reversal (stage + 1) value)) =
      localEulerOperator stage (reversal stage (restriction stage value))
  calc
    restriction stage
        (localEulerOperator (stage + 1) (reversal (stage + 1) value)) =
      localEulerOperator stage
        (restriction stage (reversal (stage + 1) value)) := eulerSquare
    _ = localEulerOperator stage
        (reversal stage (restriction stage value)) := by
      exact congrArg (fun current => localEulerOperator stage current)
        reversalSquare

theorem restriction_boundary_square (stage : Nat) :
    (restriction stage).comp (boundary (stage + 1)) =
      (boundary stage).comp (restriction stage) := by
  unfold boundary
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    restriction_action_square]

/-- The action's type contains the exact factorization payload from which
its prime and exponent axes were generated. -/
theorem action_reads_factorization_occurrence (stage : Nat) :
    Nonempty
      (GeneratedUnitFactorizationAt (StageHistory stage)) ∧
      (factorizationOccurrence stage).map Sigma.fst =
        runtimeOccurrence stage :=
  ⟨⟨stageFactorization stage⟩,
    factorizationOccurrence_projects_to_runtime stage⟩

/-! ## Finite presentation and generic quotient evaluator -/

abbrev ZeroRelationLattice := Fin 0 → ℤ

def relationOccurrences (_stage : Nat) (value : ZeroRelationLattice) :
    RootedAccountedUnfolding ZeroRelationLattice :=
  RootedAccountedUnfolding.zero value

def generatorOccurrences (stage : Nat) (value : EulerLattice stage) :
    RootedAccountedUnfolding (EulerLattice stage) :=
  RootedAccountedUnfolding.zero value

def zeroRelationMap (stage : Nat) :
    ZeroRelationLattice →ₗ[ℤ] EulerLattice stage :=
  0

def relationMapOccurrence (stage : Nat) : RootedAccountedUnfolding
    (ZeroRelationLattice →ₗ[ℤ] EulerLattice stage) :=
  (factorizationOccurrence stage).map fun _root => zeroRelationMap stage

def presentation (stage : Nat) : RootGeneratedFiniteDefectPresentationAt
    (factorizationOccurrence stage) (relationOccurrences stage)
      (generatorOccurrences stage) (relationMapOccurrence stage) :=
  RootGeneratedFiniteDefectPresentationAt.generate

abbrev StageCarrier (stage : Nat) := (presentation stage).cokernel

theorem presentation_range_eq_bot (stage : Nat) :
    (presentation stage).range = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  rfl

noncomputable def carrierEquiv (stage : Nat) :
    StageCarrier stage ≃ₗ[ℤ] EulerLattice stage :=
  (presentation stage).range.quotEquivOfEqBot
    (presentation_range_eq_bot stage)

theorem stageCarrierFG (stage : Nat) : AddGroup.FG (StageCarrier stage) := by
  apply Module.Finite.iff_addGroup_fg.mp
  unfold StageCarrier
  exact Module.Finite.quotient ℤ
    (LinearMap.range (zeroRelationMap stage))

def carrierEulerAction (stage : Nat) :
    StageCarrier stage →ₗ[ℤ] StageCarrier stage :=
  (carrierEquiv stage).symm.toLinearMap.comp
    ((eulerReversalAction stage).comp (carrierEquiv stage).toLinearMap)

def carrierReversal (stage : Nat) :
    StageCarrier stage →ₗ[ℤ] StageCarrier stage :=
  (carrierEquiv stage).symm.toLinearMap.comp
    ((reversal stage).comp (carrierEquiv stage).toLinearMap)

theorem carrierReversal_involutive (stage : Nat) :
    Function.Involutive (carrierReversal stage) := by
  intro value
  apply (carrierEquiv stage).injective
  change reversal stage (reversal stage (carrierEquiv stage value)) =
    carrierEquiv stage value
  exact reversal_involutive stage _

abbrev PrimePowerState (stage : Nat) :=
  PrimePowerQuotientEvaluation.State (StageCarrier stage)

def quotientFace (stage : Nat) :
    RootGeneratedPrimePowerQuotientEvaluationAt (StageCarrier stage)
      (factorizationOccurrence stage) (stageCarrierFG stage) :=
  RootGeneratedPrimePowerQuotientEvaluationAt.generate (StageCarrier stage)

def quotientEvaluator (stage : Nat) :
    StageCarrier stage → PrimePowerState stage :=
  (quotientFace stage).accountedEvaluator

def dependentOccurrence (stage : Nat) :=
  (quotientFace stage).dependentOccurrence

def rigidityFace (stage : Nat) :
    RootGeneratedPrimePowerKernelIncidenceRigidityAt
      (dependentOccurrence stage) :=
  RootGeneratedPrimePowerKernelIncidenceRigidityAt.generate

theorem rigidity_projects_to_factorization_occurrence (stage : Nat) :
    (rigidityFace stage).root = factorizationOccurrence stage :=
  (quotientFace stage).dependentOccurrence_projects_to_root

end
end CanonicalUnitArithmeticFactorizationEulerOperator
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
