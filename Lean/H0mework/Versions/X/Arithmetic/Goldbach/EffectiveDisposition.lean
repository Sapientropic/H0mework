import H0mework.Foundation.Finite.FibreDisposition
import H0mework.Versions.X.Arithmetic.UnitArithmetic.Factorization

/-!
# Source-generated effective additive disposition

One exact canonical unit occurrence generates a finite arithmetic calculation
trace.  Every even target is a fold of that trace.  Its candidate carrier is
the finite support of the target history's dependent factorial factorization,
so both candidate coordinates are actual factorization-generated primes.

The generic effective-fibre kernel then returns either one actual prime pair
whose parallel fold is the target or the complete finite candidate image and
an explicit faithful residual.  No signed group completion, selected landing,
residual-zero certificate, ledger receipt, or future current is an input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticEffectiveAdditiveProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open RootArithmeticUnfoldingFace
open SourceGeneratedEffectiveFibreDisposition

noncomputable section

/-! ## One rooted finite even-target calculation family -/

abbrev AdditiveCalculationPoint : Type :=
  RootArithmeticDomainPointAt initialStep UnitHistory

def additivePoint (history : UnitHistory) : AdditiveCalculationPoint :=
  RootArithmeticDomainPointAt.generate initialStep history

/-- A finite unary calculation exposure.  Every node is indexed by the same
exact root occurrence; the later nodes are calculation visits, not stored
world futures. -/
def calculationOccurrenceFrom
    (history : UnitHistory) : Nat →
      RootedAccountedUnfolding AdditiveCalculationPoint
  | 0 => RootedAccountedUnfolding.zero (additivePoint history)
  | fuel + 1 =>
      .occur (additivePoint history) <|
        .singleton
          (calculationOccurrenceFrom
            (CanonicalUnitArithmeticRoot.next history) fuel)

def terminalHistoryAlgebra
    (point : AdditiveCalculationPoint) (children : List UnitHistory) :
    UnitHistory :=
  match children with
  | [] => point.payload
  | head :: _tail => head

def generatedTargetFrom (history : UnitHistory) : Nat → UnitHistory
  | 0 => history
  | fuel + 1 =>
      generatedTargetFrom (CanonicalUnitArithmeticRoot.next history) fuel

theorem fold_calculationOccurrenceFrom_eq_generatedTargetFrom
    (history : UnitHistory) (fuel : Nat) :
    (calculationOccurrenceFrom history fuel).fold terminalHistoryAlgebra =
      generatedTargetFrom history fuel := by
  induction fuel generalizing history with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        (calculationOccurrenceFrom
            (CanonicalUnitArithmeticRoot.next history) fuel).fold
              terminalHistoryAlgebra =
          generatedTargetFrom
            (CanonicalUnitArithmeticRoot.next history) fuel
      exact inductionHypothesis _

theorem generatedTargetFrom_cardinalShadow
    (history : UnitHistory) (fuel : Nat) :
    (generatedTargetFrom history fuel).cardinalShadow =
      history.cardinalShadow + fuel := by
  induction fuel generalizing history with
  | zero => simp [generatedTargetFrom]
  | succ fuel inductionHypothesis =>
      rw [generatedTargetFrom, inductionHypothesis]
      simp only [CanonicalUnitArithmeticRoot.next_eq_next,
        UnitHistory.cardinalShadow]
      omega

/-- Index `k` generates the positive even target `2(k+1)`. -/
def evenTargetFuel (index : Nat) : Nat := 2 * index + 1

def evenTargetOccurrence (index : Nat) :
    RootedAccountedUnfolding AdditiveCalculationPoint :=
  calculationOccurrenceFrom unitHistory (evenTargetFuel index)

def evenTargetHistory (index : Nat) : UnitHistory :=
  (evenTargetOccurrence index).fold terminalHistoryAlgebra

theorem evenTargetHistory_eq_generate (index : Nat) :
    evenTargetHistory index =
      UnitHistory.generate (2 * (index + 1)) := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [evenTargetHistory, evenTargetOccurrence,
    fold_calculationOccurrenceFrom_eq_generatedTargetFrom,
    generatedTargetFrom_cardinalShadow,
    UnitHistory.cardinalShadow_generate]
  change 1 + (2 * index + 1) = 2 * (index + 1)
  omega

theorem evenTargetHistory_is_even (index : Nat) :
    Even (evenTargetHistory index).cardinalShadow := by
  refine ⟨index + 1, ?_⟩
  rw [evenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate]
  omega

theorem additiveCalculation_points_share_exact_root
    (point : AdditiveCalculationPoint) :
    point.rootOccurrence = initialStep.generated.occurrence :=
  point.rootOccurrence_eq

theorem evenTargetOccurrence_root_is_exact (index : Nat) :
    (evenTargetOccurrence index).root.rootOccurrence =
      initialStep.generated.occurrence :=
  additiveCalculation_points_share_exact_root _

/-! ## Finite factorization-generated prime-pair candidates -/

/-- Same-occurrence factorization face.  The target is definitionally the
fold of the stored exact calculation occurrence; a caller cannot pair an
unrelated target with an otherwise valid factorization. -/
structure RootGeneratedEvenTargetFactorizationAt (index : Nat) : Type where
  private mk ::
  occurrence : RootedAccountedUnfolding AdditiveCalculationPoint
  occurrence_eq : occurrence = evenTargetOccurrence index
  target : UnitHistory
  target_eq : target = occurrence.fold terminalHistoryAlgebra
  factorization : GeneratedUnitFactorizationAt target

def generatedEvenTargetFactorization (index : Nat) :
    RootGeneratedEvenTargetFactorizationAt index :=
  ⟨evenTargetOccurrence index, rfl, evenTargetHistory index, rfl,
    GeneratedUnitFactorizationAt.generate _⟩

def evenTargetFactorization (index : Nat) :
    GeneratedUnitFactorizationAt (evenTargetHistory index) :=
  (generatedEvenTargetFactorization index).factorization

theorem generatedEvenTargetFactorization_occurrence (index : Nat) :
    (generatedEvenTargetFactorization index).occurrence =
      evenTargetOccurrence index :=
  (generatedEvenTargetFactorization index).occurrence_eq

theorem generatedEvenTargetFactorization_target (index : Nat) :
    (generatedEvenTargetFactorization index).target =
      evenTargetHistory index :=
  rfl

abbrev GeneratedPrimeIndexAt (index : Nat) : Type :=
  PrimeIndex (evenTargetHistory index)

abbrev GeneratedPrimePairCandidateAt (index : Nat) : Type :=
  GeneratedPrimeIndexAt index × GeneratedPrimeIndexAt index

def firstExponentIndex {index : Nat}
    (primeIndex : GeneratedPrimeIndexAt index) :
    ExponentIndex (evenTargetHistory index) primeIndex :=
  ⟨0, multiplicity_pos _ primeIndex⟩

def generatedPrimeHistory {index : Nat}
    (primeIndex : GeneratedPrimeIndexAt index) : UnitHistory :=
  (evenTargetFactorization index).actualPrimePowerHistory primeIndex
    (firstExponentIndex primeIndex)

def generatedPrimeQuotientHistory {index : Nat}
    (primeIndex : GeneratedPrimeIndexAt index) : UnitHistory :=
  (evenTargetFactorization index).actualQuotientHistory primeIndex
    (firstExponentIndex primeIndex)

theorem generatedPrimeHistory_isPrime {index : Nat}
    (primeIndex : GeneratedPrimeIndexAt index) :
    Nat.Prime (generatedPrimeHistory primeIndex).cardinalShadow := by
  simpa [generatedPrimeHistory,
    GeneratedUnitFactorizationAt.actualPrimePowerHistory,
    primePowerHistory, firstExponentIndex, exponent] using
    (prime (evenTargetHistory index) primeIndex).property

@[simp] theorem generatedPrimeHistory_cardinalShadow {index : Nat}
    (primeIndex : GeneratedPrimeIndexAt index) :
    (generatedPrimeHistory primeIndex).cardinalShadow = primeIndex.1 := by
  simp only [generatedPrimeHistory,
    GeneratedUnitFactorizationAt.actualPrimePowerHistory,
    primePowerHistory, firstExponentIndex, exponent,
    UnitHistory.cardinalShadow_generate]
  simp only [zero_add, pow_one]
  rfl

theorem generatedPrimeHistory_joint_lands {index : Nat}
    (primeIndex : GeneratedPrimeIndexAt index) :
    factorialHistory (evenTargetHistory index) =
      (generatedPrimeHistory primeIndex).joint
        (generatedPrimeQuotientHistory primeIndex) :=
  (evenTargetFactorization index).actualPrimePower_joint_landing
    primeIndex (firstExponentIndex primeIndex)

/-- Actual additive evaluation on the finite effective carrier. -/
def additiveEvaluation (index : Nat)
    (candidate : GeneratedPrimePairCandidateAt index) : UnitHistory :=
  (generatedPrimeHistory candidate.1).parallel
    (generatedPrimeHistory candidate.2)

abbrev EffectiveAdditiveFibreAt (index : Nat) : Type :=
  Fibre (additiveEvaluation index) (evenTargetHistory index)

abbrev EffectiveAdditiveResidualAt (index : Nat) : Type :=
  FaithfulResidual (additiveEvaluation index) (evenTargetHistory index)

abbrev EffectiveAdditiveDispositionAt (index : Nat) : Type :=
  Disposition (additiveEvaluation index) (evenTargetHistory index)

/-- Occurrence-indexed total Goldbach disposition.  The framework classifier,
not the domain caller, decides whether the effective fibre is inhabited. -/
noncomputable def generatedAdditiveDisposition (index : Nat) :
    EffectiveAdditiveDispositionAt index :=
  settle (additiveEvaluation index) (evenTargetHistory index)

theorem generatedAdditiveDisposition_total (index : Nat) :
    Nonempty (EffectiveAdditiveDispositionAt index) :=
  ⟨generatedAdditiveDisposition index⟩

/-- The boundary target at index zero is `2`.  Every actual prime
restriction has cardinal at least two, so no effective pair can land there.
This supplies a reachable residual branch without asserting anything about
the classical Goldbach range `4, 6, 8, ...`. -/
theorem evenTargetZero_fibre_empty :
    ¬ Nonempty (EffectiveAdditiveFibreAt 0) := by
  rintro ⟨fibre⟩
  have landing := congrArg UnitHistory.cardinalShadow fibre.2
  have leftLower : 2 ≤
      (generatedPrimeHistory fibre.1.1).cardinalShadow :=
    (generatedPrimeHistory_isPrime fibre.1.1).two_le
  have rightLower : 2 ≤
      (generatedPrimeHistory fibre.1.2).cardinalShadow :=
    (generatedPrimeHistory_isPrime fibre.1.2).two_le
  simp only [additiveEvaluation, UnitHistory.cardinalShadow_parallel,
    evenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate] at landing
  omega

noncomputable def evenTargetZeroResidual :
    EffectiveAdditiveResidualAt 0 :=
  residualOfEmpty (additiveEvaluation 0) (evenTargetHistory 0)
    evenTargetZero_fibre_empty

theorem generatedAdditiveDisposition_zero_eq_residual :
    generatedAdditiveDisposition 0 = .residual evenTargetZeroResidual :=
  settle_eq_residual_of_empty _ _ evenTargetZero_fibre_empty

namespace EffectiveAdditiveFibreAt

variable {index : Nat} (fibre : EffectiveAdditiveFibreAt index)

def leftPrimeIndex : GeneratedPrimeIndexAt index := fibre.1.1
def rightPrimeIndex : GeneratedPrimeIndexAt index := fibre.1.2

def leftHistory : UnitHistory := generatedPrimeHistory fibre.leftPrimeIndex
def rightHistory : UnitHistory := generatedPrimeHistory fibre.rightPrimeIndex

theorem left_isPrime : Nat.Prime fibre.leftHistory.cardinalShadow :=
  generatedPrimeHistory_isPrime fibre.leftPrimeIndex

theorem right_isPrime : Nat.Prime fibre.rightHistory.cardinalShadow :=
  generatedPrimeHistory_isPrime fibre.rightPrimeIndex

theorem left_factorization_lands :
    factorialHistory (evenTargetHistory index) =
      fibre.leftHistory.joint
        (generatedPrimeQuotientHistory fibre.leftPrimeIndex) :=
  generatedPrimeHistory_joint_lands fibre.leftPrimeIndex

theorem right_factorization_lands :
    factorialHistory (evenTargetHistory index) =
      fibre.rightHistory.joint
        (generatedPrimeQuotientHistory fibre.rightPrimeIndex) :=
  generatedPrimeHistory_joint_lands fibre.rightPrimeIndex

theorem membership :
    additiveEvaluation index fibre.1 = evenTargetHistory index :=
  fibre.2

theorem lands :
    evenTargetHistory index =
      fibre.leftHistory.parallel fibre.rightHistory :=
  fibre.2.symm

theorem siblingFold_lands :
    evenTargetHistory index =
      parallelChildren [fibre.leftHistory, fibre.rightHistory] := by
  simpa using fibre.lands

end EffectiveAdditiveFibreAt

/-- Coordinate readout derived from an actual effective fibre. -/
structure EffectiveAdditiveCoordinateReadoutAt
    (index : Nat) (fibre : EffectiveAdditiveFibreAt index) : Type where
  private mk ::
  target : Nat
  left : Nat
  right : Nat
  target_eq : target = (evenTargetHistory index).cardinalShadow
  left_eq : left = fibre.leftHistory.cardinalShadow
  right_eq : right = fibre.rightHistory.cardinalShadow
  target_eq_left_add_right : target = left + right
  leftPrime : Nat.Prime left
  rightPrime : Nat.Prime right

def coordinateReadout {index : Nat}
    (fibre : EffectiveAdditiveFibreAt index) :
    EffectiveAdditiveCoordinateReadoutAt index fibre :=
  ⟨(evenTargetHistory index).cardinalShadow,
    fibre.leftHistory.cardinalShadow,
    fibre.rightHistory.cardinalShadow,
    rfl, rfl, rfl, by
      have landing := congrArg UnitHistory.cardinalShadow fibre.lands
      simpa using landing,
    fibre.left_isPrime, fibre.right_isPrime⟩

/-! ## Positive `4 = 2 + 2` source-generated fixture -/

def fourTwoPrimeIndex :
    PrimeIndex (UnitHistory.generate 4) := by
  refine ⟨2, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  apply Nat.ne_of_gt
  apply Nat.prime_two.factorization_pos_of_dvd
  · rw [factorialHistory_cardinalShadow,
      UnitHistory.cardinalShadow_generate]
    exact Nat.factorial_ne_zero 4
  · rw [factorialHistory_cardinalShadow,
      UnitHistory.cardinalShadow_generate]
    exact Nat.dvd_factorial (by omega) (by omega)

def goldbachPrimeIndex : GeneratedPrimeIndexAt 1 :=
  fourTwoPrimeIndex

def goldbachPrimePairCandidate : GeneratedPrimePairCandidateAt 1 :=
  (goldbachPrimeIndex, goldbachPrimeIndex)

abbrev GoldbachAdditiveFibreAt (index : Nat) : Type :=
  EffectiveAdditiveFibreAt index

def goldbachAdditiveFibre : GoldbachAdditiveFibreAt 1 :=
  ⟨goldbachPrimePairCandidate, rfl⟩

theorem goldbachAdditiveDisposition_is_inhabited :
    generatedAdditiveDisposition 1 =
      .inhabited (Classical.choice
        (show Nonempty (EffectiveAdditiveFibreAt 1) from
          ⟨goldbachAdditiveFibre⟩)) :=
  settle_eq_inhabited_of_nonempty _ _ ⟨goldbachAdditiveFibre⟩

def additiveCalculationOccurrence :
    RootedAccountedUnfolding AdditiveCalculationPoint :=
  evenTargetOccurrence 1

def additiveTargetHistory : UnitHistory := evenTargetHistory 1
def leftPrimeHistory : UnitHistory := goldbachAdditiveFibre.leftHistory
def rightPrimeHistory : UnitHistory := goldbachAdditiveFibre.rightHistory

@[simp] theorem additiveTargetHistory_eq_generate_four :
    additiveTargetHistory = UnitHistory.generate 4 := by
  simpa [additiveTargetHistory] using evenTargetHistory_eq_generate 1

theorem leftPrimeHistory_isPrime :
    Nat.Prime leftPrimeHistory.cardinalShadow :=
  goldbachAdditiveFibre.left_isPrime

theorem rightPrimeHistory_isPrime :
    Nat.Prime rightPrimeHistory.cardinalShadow :=
  goldbachAdditiveFibre.right_isPrime

theorem additivePrimePair_lands :
    additiveTargetHistory =
      leftPrimeHistory.parallel rightPrimeHistory :=
  goldbachAdditiveFibre.lands

theorem additivePrimePair_siblingFold_lands :
    additiveTargetHistory =
      parallelChildren [leftPrimeHistory, rightPrimeHistory] :=
  goldbachAdditiveFibre.siblingFold_lands

end
end CanonicalUnitArithmeticEffectiveAdditiveProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
