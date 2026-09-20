import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial
import H0mework.Arithmetic.UnitArithmetic.Root

/-!
# Unit-history-generated arithmetic factorization occurrence

Prime authority is recovered from an actual dependent fold of the unit
history.  For a history of size `n`, `factorialHistory` is the joint fold
whose cardinal shadow is `n!`; its `Nat.factorization` support therefore
contains exactly actual prime factors, with their actual multiplicities.

Every supported `(p,k)` produces a concrete unit-history landing

`factorialHistory h = history(p^k) joint quotientHistory`.

The runtime occurrence computes this material from the exact activated
root's whole history.  It never calls a canonical prime enumerator, accepts a prime table, or
stores a completed future factorization.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationOccurrence

open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open RootArithmeticIncidence

noncomputable section

/-! ## Dependent factorial fold -/

/-- The factorial of a unit history is generated only with the dependent
`joint` fold.  The successor factor is the same actual prefix ending at the
newest unit. -/
def factorialHistory : UnitHistory → UnitHistory
  | .empty => unitHistory
  | .next prior => (factorialHistory prior).joint (.next prior)

@[simp] theorem factorialHistory_cardinalShadow (history : UnitHistory) :
    (factorialHistory history).cardinalShadow =
      history.cardinalShadow.factorial := by
  induction history with
  | empty => rfl
  | next prior inductionHypothesis =>
      simp only [factorialHistory, UnitHistory.cardinalShadow_joint,
        UnitHistory.cardinalShadow]
      rw [inductionHypothesis, Nat.factorial_succ]
      exact Nat.mul_comm _ _

/-- Actual prime multiplicity vector of the dependent factorial fold. -/
def factorization (history : UnitHistory) : ℕ →₀ ℕ :=
  (factorialHistory history).cardinalShadow.factorization

theorem factorization_eq_cardinal_factorization (history : UnitHistory) :
    factorization history = history.cardinalShadow.factorial.factorization := by
  rw [factorization, factorialHistory_cardinalShadow]

abbrev PrimeIndex (history : UnitHistory) : Type :=
  { prime : ℕ // prime ∈ (factorization history).support }

def prime (history : UnitHistory) (index : PrimeIndex history) : Nat.Primes :=
  ⟨index.1, by
    have nonzero : factorization history index.1 ≠ 0 :=
      Finsupp.mem_support_iff.mp index.2
    by_contra notPrime
    exact nonzero (Nat.factorization_eq_zero_of_not_prime _ notPrime)⟩

def multiplicity (history : UnitHistory) (index : PrimeIndex history) : Nat :=
  factorization history index.1

theorem multiplicity_pos (history : UnitHistory)
    (index : PrimeIndex history) :
    0 < multiplicity history index :=
  Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp index.2)

/-- Positive prime-power exponents actually present in the dependent fold. -/
abbrev ExponentIndex (history : UnitHistory) (index : PrimeIndex history) :=
  Fin (multiplicity history index)

def exponent {history : UnitHistory} {index : PrimeIndex history}
    (power : ExponentIndex history index) : Nat :=
  power.1 + 1

theorem exponent_le_multiplicity
    {history : UnitHistory} {index : PrimeIndex history}
    (power : ExponentIndex history index) :
    exponent power ≤ multiplicity history index := by
  exact power.2

def primePowerHistory {history : UnitHistory}
    (index : PrimeIndex history) (power : ExponentIndex history index) :
    UnitHistory :=
  UnitHistory.generate ((prime history index : Nat) ^ exponent power)

def quotientHistory {history : UnitHistory}
    (index : PrimeIndex history) (power : ExponentIndex history index) :
    UnitHistory :=
  UnitHistory.generate
    ((factorialHistory history).cardinalShadow /
      (prime history index : Nat) ^ exponent power)

theorem primePower_dvd_factorialHistory
    {history : UnitHistory} (index : PrimeIndex history)
    (power : ExponentIndex history index) :
    (prime history index : Nat) ^ exponent power ∣
      (factorialHistory history).cardinalShadow := by
  apply ((prime history index).property.pow_dvd_iff_le_factorization
    (by
      rw [factorialHistory_cardinalShadow]
      exact Nat.factorial_ne_zero history.cardinalShadow)).2
  change exponent power ≤
    (factorialHistory history).cardinalShadow.factorization index.1
  exact exponent_le_multiplicity power

/-- The actual factorization landing is an equality of unit histories, not
only a numerical divisibility statement. -/
theorem primePower_joint_landing
    {history : UnitHistory} (index : PrimeIndex history)
    (power : ExponentIndex history index) :
    factorialHistory history =
      (primePowerHistory index power).joint
        (quotientHistory index power) := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [UnitHistory.cardinalShadow_joint]
  simp only [primePowerHistory, quotientHistory,
    UnitHistory.cardinalShadow_generate]
  exact (Nat.mul_div_cancel'
    (primePower_dvd_factorialHistory index power)).symm

/-- Generated source material.  Its constructor is private; prime support,
multiplicity and every joint landing are calculated from `history`. -/
structure GeneratedUnitFactorizationAt (history : UnitHistory) : Type where
  private mk ::

namespace GeneratedUnitFactorizationAt

variable {history : UnitHistory}

def generate (history : UnitHistory) : GeneratedUnitFactorizationAt history :=
  ⟨⟩

def primeSupport
    (_generated : GeneratedUnitFactorizationAt history) : Finset Nat :=
  (factorization history).support

def actualPrime
    (_generated : GeneratedUnitFactorizationAt history)
    (index : PrimeIndex history) : Nat.Primes :=
  prime history index

def actualMultiplicity
    (_generated : GeneratedUnitFactorizationAt history)
    (index : PrimeIndex history) : Nat :=
  multiplicity history index

def actualPrimePowerHistory
    (_generated : GeneratedUnitFactorizationAt history)
    (index : PrimeIndex history) (power : ExponentIndex history index) :
    UnitHistory :=
  primePowerHistory index power

def actualQuotientHistory
    (_generated : GeneratedUnitFactorizationAt history)
    (index : PrimeIndex history) (power : ExponentIndex history index) :
    UnitHistory :=
  quotientHistory index power

theorem actualPrimePower_joint_landing
    (_generated : GeneratedUnitFactorizationAt history)
    (index : PrimeIndex history) (power : ExponentIndex history index) :
    factorialHistory history =
      (_generated.actualPrimePowerHistory index power).joint
        (_generated.actualQuotientHistory index power) :=
  primePower_joint_landing index power

end GeneratedUnitFactorizationAt

/-! ## Exact runtime installation -/

abbrev Runtime := LivingRuntimeState runtimeFacade.process

def runtimeAt (stage : Nat) : Runtime :=
  runtimeSeed.advance stage

abbrev RuntimeAuthority :=
  Σ runtime : Runtime, ExactActivatedRootOccurrenceAt runtime

def runtimeAuthorityAt (stage : Nat) : RuntimeAuthority :=
  ⟨runtimeAt stage, (runtimeAt stage).tick⟩

def authorityStep (authority : RuntimeAuthority) :
    RootArithmeticIncidenceStepAt recognition authority.1.current.visit :=
  recognition.generateStepAt authority.1.current.visit

def authorityWholeHistory (authority : RuntimeAuthority) : UnitHistory :=
  (authorityStep authority).material.whole

def runtimeWholeHistory (stage : Nat) : UnitHistory :=
  authorityWholeHistory (runtimeAuthorityAt stage)

@[simp] theorem runtimeWholeHistory_zero :
    runtimeWholeHistory 0 = initialStep.material.whole :=
  rfl

@[simp] theorem runtimeWholeHistory_succ (stage : Nat) :
    runtimeWholeHistory (stage + 1) = next (runtimeWholeHistory stage) :=
  rfl

theorem runtimeWholeHistory_cardinalShadow (stage : Nat) :
    (runtimeWholeHistory stage).cardinalShadow = stage + 2 := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [runtimeWholeHistory_succ, next_eq_next]
      change Nat.succ (runtimeWholeHistory stage).cardinalShadow =
        Nat.succ stage + 2
      omega

def runtimeOccurrence (stage : Nat) :
    RootedAccountedUnfolding RuntimeAuthority :=
  RootedAccountedUnfolding.zero (runtimeAuthorityAt stage)

/-- Factorization material is computed from the exact authority carried by
the same occurrence. -/
def factorizationOccurrence (stage : Nat) : RootedAccountedUnfolding
    (Σ authority : RuntimeAuthority,
      GeneratedUnitFactorizationAt (authorityWholeHistory authority)) :=
  (runtimeOccurrence stage).map fun authority =>
    ⟨authority, GeneratedUnitFactorizationAt.generate
      (authorityWholeHistory authority)⟩

theorem factorizationOccurrence_projects_to_runtime (stage : Nat) :
    (factorizationOccurrence stage).map Sigma.fst =
      runtimeOccurrence stage := by
  rw [factorizationOccurrence, RootedAccountedUnfolding.map_map]
  change (runtimeOccurrence stage).map id = runtimeOccurrence stage
  exact RootedAccountedUnfolding.map_id _

/-! ## Cofinal production of every actual prime power -/

/-- One prime power recovered from one finite runtime factorization
occurrence.  The indices are actual support/multiplicity indices, not an
external enumeration. -/
structure RuntimePrimePowerFactorAt
    (requestedPrime : Nat.Primes) (requestedExponent : Nat) : Type where
  private mk ::
  stage : Nat
  primeIndex : PrimeIndex (runtimeWholeHistory stage)
  exponentIndex : ExponentIndex (runtimeWholeHistory stage) primeIndex
  prime_eq : prime (runtimeWholeHistory stage) primeIndex = requestedPrime
  exponent_eq : exponent exponentIndex = requestedExponent

namespace RuntimePrimePowerFactorAt

variable {requestedPrime : Nat.Primes} {requestedExponent : Nat}

theorem runtimeFactorization_mono_succ (stage : Nat) :
    factorization (runtimeWholeHistory stage) ≤
      factorization (runtimeWholeHistory (stage + 1)) := by
  rw [factorization_eq_cardinal_factorization,
    factorization_eq_cardinal_factorization]
  apply (Nat.factorization_le_iff_dvd
    (Nat.factorial_ne_zero (runtimeWholeHistory stage).cardinalShadow)
    (Nat.factorial_ne_zero
      (runtimeWholeHistory (stage + 1)).cardinalShadow)).2
  apply Nat.factorial_dvd_factorial
  rw [runtimeWholeHistory_cardinalShadow,
    runtimeWholeHistory_cardinalShadow]
  omega

def liftPrimeIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    PrimeIndex (runtimeWholeHistory (factor.stage + 1)) := by
  refine ⟨factor.primeIndex.1, Finsupp.mem_support_iff.mpr ?_⟩
  have oldNonzero :
      factorization (runtimeWholeHistory factor.stage)
          factor.primeIndex.1 ≠ 0 :=
    Finsupp.mem_support_iff.mp factor.primeIndex.2
  have order := runtimeFactorization_mono_succ factor.stage
    factor.primeIndex.1
  omega

def liftExponentIndex
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    ExponentIndex (runtimeWholeHistory (factor.stage + 1))
      (liftPrimeIndex factor) := by
  refine ⟨factor.exponentIndex.1, ?_⟩
  have order := runtimeFactorization_mono_succ factor.stage
    factor.primeIndex.1
  have oldBound := factor.exponentIndex.2
  change factor.exponentIndex.1 <
    factorization (runtimeWholeHistory (factor.stage + 1))
      factor.primeIndex.1
  change factor.exponentIndex.1 <
    factorization (runtimeWholeHistory factor.stage)
      factor.primeIndex.1 at oldBound
  omega

/-- The next exact runtime occurrence carrying the same actual prime-power
factor.  This is lineage data, not a cofinal schedule. -/
def advance
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    RuntimePrimePowerFactorAt requestedPrime requestedExponent := by
  refine ⟨factor.stage + 1, liftPrimeIndex factor,
    liftExponentIndex factor, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Subtype.val factor.prime_eq
  · exact factor.exponent_eq

@[simp] theorem advance_stage
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    factor.advance.stage = factor.stage + 1 :=
  rfl

@[simp] theorem liftPrimeIndex_value
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (liftPrimeIndex factor).1 = factor.primeIndex.1 :=
  rfl

@[simp] theorem liftExponentIndex_value
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (liftExponentIndex factor).1 = factor.exponentIndex.1 :=
  rfl

def generate (requestedPrime : Nat.Primes) (requestedExponent : Nat)
    (positive : 0 < requestedExponent) :
    RuntimePrimePowerFactorAt requestedPrime requestedExponent := by
  let stage := (requestedPrime : Nat) ^ requestedExponent
  let history := runtimeWholeHistory stage
  have powerPositive : 0 < (requestedPrime : Nat) ^ requestedExponent :=
    pow_pos requestedPrime.property.pos _
  have powerDvd :
      (requestedPrime : Nat) ^ requestedExponent ∣
        (factorialHistory history).cardinalShadow := by
    rw [factorialHistory_cardinalShadow]
    apply Nat.dvd_factorial powerPositive
    change (requestedPrime : Nat) ^ requestedExponent ≤
      (runtimeWholeHistory stage).cardinalShadow
    rw [runtimeWholeHistory_cardinalShadow]
    omega
  have exponentBound : requestedExponent ≤
      (factorization history) (requestedPrime : Nat) := by
    apply (requestedPrime.property.pow_dvd_iff_le_factorization
      (by
        rw [factorialHistory_cardinalShadow]
        exact Nat.factorial_ne_zero history.cardinalShadow)).1
    exact powerDvd
  have multiplicityNonzero :
      factorization history (requestedPrime : Nat) ≠ 0 := by
    omega
  let primeIndex : PrimeIndex history :=
    ⟨requestedPrime, Finsupp.mem_support_iff.mpr multiplicityNonzero⟩
  let exponentIndex : ExponentIndex history primeIndex :=
    ⟨requestedExponent - 1, by
      change requestedExponent - 1 <
        factorization history (requestedPrime : Nat)
      omega⟩
  refine ⟨stage, primeIndex, exponentIndex, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · change requestedExponent - 1 + 1 = requestedExponent
    omega

theorem actual_joint_landing
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    factorialHistory (runtimeWholeHistory factor.stage) =
      (primePowerHistory factor.primeIndex factor.exponentIndex).joint
        (quotientHistory factor.primeIndex factor.exponentIndex) :=
  primePower_joint_landing factor.primeIndex factor.exponentIndex

theorem actual_prime_power_value
    (factor : RuntimePrimePowerFactorAt requestedPrime requestedExponent) :
    (prime (runtimeWholeHistory factor.stage) factor.primeIndex : Nat) ^
        exponent factor.exponentIndex =
      (requestedPrime : Nat) ^ requestedExponent := by
  rw [factor.prime_eq, factor.exponent_eq]

end RuntimePrimePowerFactorAt

theorem runtime_authority_factorizes (stage : Nat) :
    (runtimeAt stage).tick.generated.occurrence =
        (runtimeAt stage).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt stage).current.visit.current ∧
      HEq (runtimeAt stage).tick.generated.wholeLedgerWriteBack
        ((runtimeAt stage).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt stage).current.visit.current) ∧
      (runtimeAt stage).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt stage).state) := by
  have factorized := coversAt_factorizes (runtimeAt stage) FacadeFace.material
  exact ⟨factorized.2.1, factorized.2.2.1, factorized.2.2.2.2⟩

end
end CanonicalUnitArithmeticFactorizationOccurrence
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
