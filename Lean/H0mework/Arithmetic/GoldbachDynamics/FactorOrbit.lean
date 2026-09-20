import H0mework.Arithmetic.Goldbach.EffectiveDisposition
import H0mework.Foundation.Finite.EffectiveOrbit

/-!
# Canonical effective Goldbach factor-repair orbit

The prime-pair fibre is a terminal readout, not a carrier large enough for the
arithmetic that may reach it.  This producer therefore works on all effective
positive splits `(x,y)` of the same source-generated even target.  At each
split, finite factorization generates exactly one of:

* two primes, which materialize an `EffectiveAdditiveFibreAt`; or
* a composite endpoint, its proper least-factor decomposition, and the exact
  effective repair `(x-s,y+s)` or `(x+s,y-s)` with `s = minFac - 1`.

The generic finite-orbit kernel retains the complete ordered repair trace and
returns either an actual prime-pair terminal or an explicit faithful cycle
residual.  It does not infer termination from finiteness.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open SourceGeneratedFiniteEffectiveOrbitDisposition

noncomputable section

def repairTargetValue (index : Nat) : Nat :=
  (evenTargetHistory index).cardinalShadow

/-- All positive effective coordinate splits of the generated target.  Unlike
the terminal carrier, neither coordinate is assumed prime. -/
abbrev EffectiveSplitAt (index : Nat) : Type :=
  {left : Fin (repairTargetValue index + 1) //
    2 ≤ left.1 ∧ 2 ≤ repairTargetValue index - left.1}

noncomputable instance effectiveSplitFintype (index : Nat) :
    Fintype (EffectiveSplitAt index) :=
  Fintype.ofFinite _

def splitLeft {index : Nat} (state : EffectiveSplitAt index) : Nat :=
  state.1.1

def splitRight {index : Nat} (state : EffectiveSplitAt index) : Nat :=
  repairTargetValue index - splitLeft state

theorem splitLeft_atLeastTwo {index : Nat}
    (state : EffectiveSplitAt index) :
    2 ≤ splitLeft state :=
  state.2.1

theorem splitRight_atLeastTwo {index : Nat}
    (state : EffectiveSplitAt index) :
    2 ≤ splitRight state :=
  state.2.2

theorem splitLeft_le_target {index : Nat}
    (state : EffectiveSplitAt index) :
    splitLeft state ≤ repairTargetValue index := by
  exact Nat.le_of_lt_succ state.1.2

theorem split_landing {index : Nat}
    (state : EffectiveSplitAt index) :
    splitLeft state + splitRight state = repairTargetValue index := by
  change state.1.1 + (repairTargetValue index - state.1.1) =
    repairTargetValue index
  have leftLe : state.1.1 ≤ repairTargetValue index :=
    Nat.le_of_lt_succ state.1.2
  omega

/-! ## Source-generated endpoint factor disposition -/

/-- A proper factorization selected by the complete natural-number factor
table.  Both factors are nonunits and the first factor is prime. -/
structure ProperFactorizationAt (value : Nat) : Type where
  private mk ::
  factor : Nat
  cofactor : Nat
  factorPrime : Nat.Prime factor
  factorAtLeastTwo : 2 ≤ factor
  cofactorAtLeastTwo : 2 ≤ cofactor
  factorMulCofactor : factor * cofactor = value
  factorProper : factor < value

def factorShift {value : Nat}
    (factorization : ProperFactorizationAt value) : Nat :=
  factorization.factor - 1

theorem factorShift_pos {value : Nat}
    (factorization : ProperFactorizationAt value) :
    0 < factorShift factorization := by
  rw [factorShift]
  have factorFloor := factorization.factorAtLeastTwo
  omega

theorem factorShift_lt_value {value : Nat}
    (factorization : ProperFactorizationAt value) :
    factorShift factorization < value := by
  rw [factorShift]
  have factorFloor := factorization.factorAtLeastTwo
  have factorProper := factorization.factorProper
  omega

theorem endpoint_sub_factorShift_atLeastThree {value : Nat}
    (factorization : ProperFactorizationAt value) :
    3 ≤ value - factorShift factorization := by
  apply Nat.le_sub_of_add_le
  have factorFloor := factorization.factorAtLeastTwo
  calc
    3 + factorShift factorization = factorization.factor + 2 := by
      rw [factorShift]
      omega
    _ ≤ factorization.factor * 2 := by
      omega
    _ ≤ factorization.factor * factorization.cofactor :=
      Nat.mul_le_mul_left _ factorization.cofactorAtLeastTwo
    _ = value := factorization.factorMulCofactor

/-- Any actual proper prime divisor generates the same effective repair
material as the canonical least factor.  This is the full-factor carrier used
to test whether a minFac cycle has an unconsumed source edge. -/
def properFactorizationOfPrimeDivisor (value factor : Nat)
    (factorPrime : Nat.Prime factor) (factorDvd : factor ∣ value)
    (factorProper : factor < value) : ProperFactorizationAt value := by
  let cofactor := value / factor
  have factorMulCofactor : factor * cofactor = value :=
    Nat.mul_div_cancel' factorDvd
  have cofactorAtLeastTwo : 2 ≤ cofactor := by
    by_contra cofactorSmall
    have cofactorLeOne : cofactor ≤ 1 := by omega
    have productLeFactor : factor * cofactor ≤ factor * 1 :=
      Nat.mul_le_mul_left factor cofactorLeOne
    rw [factorMulCofactor, Nat.mul_one] at productLeFactor
    exact (not_le_of_gt factorProper) productLeFactor
  exact
    { factor := factor
      cofactor := cofactor
      factorPrime := factorPrime
      factorAtLeastTwo := factorPrime.two_le
      cofactorAtLeastTwo := cofactorAtLeastTwo
      factorMulCofactor := factorMulCofactor
      factorProper := factorProper }

/-- Data-bearing prime endpoint used by the Type-valued classifier. -/
structure PrimeEndpointAt (value : Nat) : Type where
  isPrime : Nat.Prime value

/-- Complete endpoint decision above the nonunit floor.  The composite branch
is generated from `Nat.minFac`; no factor witness is accepted from a caller. -/
noncomputable def generatedPrimeOrFactor (value : Nat) (floor : 2 ≤ value) :
    PrimeEndpointAt value ⊕ ProperFactorizationAt value := by
  by_cases primeValue : Nat.Prime value
  · exact .inl ⟨primeValue⟩
  · let factor := Nat.minFac value
    let cofactor := value / factor
    have factorPrime : Nat.Prime factor := by
      exact Nat.minFac_prime (by omega)
    have factorDvd : factor ∣ value := Nat.minFac_dvd value
    have factorMulCofactor : factor * cofactor = value := by
      exact Nat.mul_div_cancel' factorDvd
    have factorLeCofactor : factor ≤ cofactor := by
      exact Nat.minFac_le_div (by omega) primeValue
    exact .inr
      { factor := factor
        cofactor := cofactor
        factorPrime := factorPrime
        factorAtLeastTwo := factorPrime.two_le
        cofactorAtLeastTwo := factorPrime.two_le.trans factorLeCofactor
        factorMulCofactor := factorMulCofactor
        factorProper :=
          (Nat.not_prime_iff_minFac_lt floor).mp primeValue }

theorem generatedPrimeOrFactor_eq_prime (value : Nat) (floor : 2 ≤ value)
    (primeValue : Nat.Prime value) :
    generatedPrimeOrFactor value floor = .inl ⟨primeValue⟩ := by
  simp [generatedPrimeOrFactor, primeValue]

theorem generatedPrimeOrFactor_eq_factor (value : Nat) (floor : 2 ≤ value)
    (notPrime : ¬ Nat.Prime value) :
    ∃ factorization : ProperFactorizationAt value,
      generatedPrimeOrFactor value floor = .inr factorization ∧
        factorization.factor = Nat.minFac value := by
  unfold generatedPrimeOrFactor
  split
  · contradiction
  · exact ⟨_, rfl, rfl⟩

/-! ## Exact effective repairs -/

def leftRepairTarget {index : Nat} (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitLeft source)) :
    EffectiveSplitAt index := by
  let targetLeft := splitLeft source - factorShift factorization
  have targetLeftFloor : 2 ≤ targetLeft := by
    exact (endpoint_sub_factorShift_atLeastThree factorization).trans' (by omega)
  have targetLeftLe : targetLeft ≤ repairTargetValue index := by
    exact (Nat.sub_le _ _).trans (splitLeft_le_target source)
  refine ⟨⟨targetLeft, by omega⟩, targetLeftFloor, ?_⟩
  have sourceRightFloor := splitRight_atLeastTwo source
  have targetLeftLeSource : targetLeft ≤ splitLeft source := Nat.sub_le _ _
  exact sourceRightFloor.trans
    (Nat.sub_le_sub_left targetLeftLeSource (repairTargetValue index))

def rightRepairTarget {index : Nat} (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitRight source)) :
    EffectiveSplitAt index := by
  let targetLeft := splitLeft source + factorShift factorization
  have targetRightFloor :
      3 ≤ splitRight source - factorShift factorization :=
    endpoint_sub_factorShift_atLeastThree factorization
  have sourceLanding := split_landing source
  have shiftLeRight :
      factorShift factorization ≤ splitRight source :=
    (factorShift_lt_value factorization).le
  have targetLeftLe : targetLeft ≤ repairTargetValue index := by
    unfold targetLeft
    calc
      splitLeft source + factorShift factorization ≤
          splitLeft source + splitRight source :=
        Nat.add_le_add_left shiftLeRight _
      _ = repairTargetValue index := sourceLanding
  refine ⟨⟨targetLeft, by omega⟩, ?_, ?_⟩
  · exact (splitLeft_atLeastTwo source).trans (Nat.le_add_right _ _)
  · change 2 ≤ repairTargetValue index -
      (splitLeft source + factorShift factorization)
    omega

@[simp] theorem leftRepairTarget_left {index : Nat}
    (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitLeft source)) :
    splitLeft (leftRepairTarget source factorization) =
      splitLeft source - factorShift factorization := by
  rfl

theorem leftRepairTarget_right {index : Nat}
    (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitLeft source)) :
    splitRight (leftRepairTarget source factorization) =
      splitRight source + factorShift factorization := by
  change repairTargetValue index -
      (splitLeft source - factorShift factorization) =
    splitRight source + factorShift factorization
  have sourceLanding := split_landing source
  have shiftLe := (factorShift_lt_value factorization).le
  omega

@[simp] theorem rightRepairTarget_left {index : Nat}
    (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitRight source)) :
    splitLeft (rightRepairTarget source factorization) =
      splitLeft source + factorShift factorization := by
  rfl

theorem rightRepairTarget_right {index : Nat}
    (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitRight source)) :
    splitRight (rightRepairTarget source factorization) =
      splitRight source - factorShift factorization := by
  change repairTargetValue index -
      (splitLeft source + factorShift factorization) =
    splitRight source - factorShift factorization
  have sourceLanding := split_landing source
  have shiftLe := (factorShift_lt_value factorization).le
  omega

structure LeftFactorRepairAt {index : Nat}
    (source : EffectiveSplitAt index) : Type where
  private mk ::
  factorization : ProperFactorizationAt (splitLeft source)
  shift : Nat
  shift_eq : shift = factorShift factorization
  shiftPositive : 0 < shift
  target : EffectiveSplitAt index
  target_eq : target = leftRepairTarget source factorization
  leftReadout : splitLeft target = splitLeft source - shift
  rightReadout : splitRight target = splitRight source + shift
  leftFloor : 3 ≤ splitLeft target
  leftStrict : splitLeft target < splitLeft source
  landingPreserved :
    splitLeft target + splitRight target = repairTargetValue index

structure RightFactorRepairAt {index : Nat}
    (source : EffectiveSplitAt index) : Type where
  private mk ::
  factorization : ProperFactorizationAt (splitRight source)
  shift : Nat
  shift_eq : shift = factorShift factorization
  shiftPositive : 0 < shift
  target : EffectiveSplitAt index
  target_eq : target = rightRepairTarget source factorization
  leftReadout : splitLeft target = splitLeft source + shift
  rightReadout : splitRight target = splitRight source - shift
  rightFloor : 3 ≤ splitRight target
  rightStrict : splitRight target < splitRight source
  landingPreserved :
    splitLeft target + splitRight target = repairTargetValue index

def generateLeftFactorRepair {index : Nat}
    (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitLeft source)) :
    LeftFactorRepairAt source := by
  let shift := factorShift factorization
  let target := leftRepairTarget source factorization
  have shiftLe : shift ≤ splitLeft source :=
    (factorShift_lt_value factorization).le
  exact
    { factorization := factorization
      shift := shift
      shift_eq := rfl
      shiftPositive := factorShift_pos factorization
      target := target
      target_eq := rfl
      leftReadout := leftRepairTarget_left source factorization
      rightReadout := leftRepairTarget_right source factorization
      leftFloor := by
        simpa [target, shift] using
          endpoint_sub_factorShift_atLeastThree factorization
      leftStrict := by
        rw [show splitLeft target =
          splitLeft source - factorShift factorization by
            exact leftRepairTarget_left source factorization]
        have shiftPositive := factorShift_pos factorization
        have shiftLe := (factorShift_lt_value factorization).le
        omega
      landingPreserved := split_landing target }

def generateRightFactorRepair {index : Nat}
    (source : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitRight source)) :
    RightFactorRepairAt source := by
  let shift := factorShift factorization
  let target := rightRepairTarget source factorization
  have targetRightFloor :=
    endpoint_sub_factorShift_atLeastThree factorization
  exact
    { factorization := factorization
      shift := shift
      shift_eq := rfl
      shiftPositive := factorShift_pos factorization
      target := target
      target_eq := rfl
      leftReadout := rightRepairTarget_left source factorization
      rightReadout := rightRepairTarget_right source factorization
      rightFloor := by
        rw [show splitRight target =
          splitRight source - factorShift factorization by
            exact rightRepairTarget_right source factorization]
        exact targetRightFloor
      rightStrict := by
        rw [show splitRight target =
          splitRight source - factorShift factorization by
            exact rightRepairTarget_right source factorization]
        have shiftPositive := factorShift_pos factorization
        have shiftLe := (factorShift_lt_value factorization).le
        omega
      landingPreserved := split_landing target }

/-- Terminal prime pair at an effective split. -/
structure PrimePairTerminalAt {index : Nat}
    (state : EffectiveSplitAt index) : Type where
  leftPrime : Nat.Prime (splitLeft state)
  rightPrime : Nat.Prime (splitRight state)

inductive FactorRepairStepAt {index : Nat}
    (source : EffectiveSplitAt index) : Type
  | left (repair : LeftFactorRepairAt source)
  | right (repair : RightFactorRepairAt source)

def FactorRepairStepAt.target {index : Nat}
    {source : EffectiveSplitAt index} :
    FactorRepairStepAt source → EffectiveSplitAt index
  | .left repair => repair.target
  | .right repair => repair.target

/-- Left-first source classifier, matching the branch's exact arithmetic
repair semantics without importing its historical root. -/
noncomputable def generatedSplitDisposition {index : Nat}
    (state : EffectiveSplitAt index) :
    PrimePairTerminalAt state ⊕ FactorRepairStepAt state :=
  match generatedPrimeOrFactor (splitLeft state)
      (splitLeft_atLeastTwo state) with
  | .inr factorization =>
      .inr (.left (generateLeftFactorRepair state factorization))
  | .inl leftPrime =>
      match generatedPrimeOrFactor (splitRight state)
          (splitRight_atLeastTwo state) with
      | .inr factorization =>
          .inr (.right (generateRightFactorRepair state factorization))
      | .inl rightPrime =>
          .inl ⟨leftPrime.isPrime, rightPrime.isPrime⟩

theorem generatedSplitDisposition_eq_leftRepair {index : Nat}
    (state : EffectiveSplitAt index)
    (factorization : ProperFactorizationAt (splitLeft state))
    (decision : generatedPrimeOrFactor (splitLeft state)
      (splitLeft_atLeastTwo state) = .inr factorization) :
    generatedSplitDisposition state =
      .inr (.left (generateLeftFactorRepair state factorization)) := by
  simp only [generatedSplitDisposition, decision]

theorem generatedSplitDisposition_eq_rightRepair {index : Nat}
    (state : EffectiveSplitAt index)
    (leftPrime : PrimeEndpointAt (splitLeft state))
    (leftDecision : generatedPrimeOrFactor (splitLeft state)
      (splitLeft_atLeastTwo state) = .inl leftPrime)
    (factorization : ProperFactorizationAt (splitRight state))
    (rightDecision : generatedPrimeOrFactor (splitRight state)
      (splitRight_atLeastTwo state) = .inr factorization) :
    generatedSplitDisposition state =
      .inr (.right (generateRightFactorRepair state factorization)) := by
  simp only [generatedSplitDisposition, leftDecision, rightDecision]

noncomputable def factorRepairLaw (index : Nat) :
    Law (EffectiveSplitAt index) where
  TerminalAt := PrimePairTerminalAt
  StepAt := FactorRepairStepAt
  target := FactorRepairStepAt.target
  classify := generatedSplitDisposition

theorem repairTarget_atLeastFour (index : Nat) (indexInRange : 1 ≤ index) :
    4 ≤ repairTargetValue index := by
  rw [repairTargetValue, evenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate]
  omega

/-- Canonical source start `2 + (N-2)`. -/
def canonicalSplit (index : Nat) (indexInRange : 1 ≤ index) :
    EffectiveSplitAt index := by
  have targetFloor := repairTarget_atLeastFour index indexInRange
  refine ⟨⟨2, by omega⟩, ?_, ?_⟩
  · change 2 ≤ 2
    omega
  · change 2 ≤ repairTargetValue index - 2
    omega

@[simp] theorem canonicalSplit_left (index : Nat) (indexInRange : 1 ≤ index) :
    splitLeft (canonicalSplit index indexInRange) = 2 := by
  rfl

@[simp] theorem canonicalSplit_right (index : Nat) (indexInRange : 1 ≤ index) :
    splitRight (canonicalSplit index indexInRange) =
      repairTargetValue index - 2 := by
  rfl

/-! ## Terminal readback and rooted total disposition -/

/-- Install a terminal prime value into the actual factorial support of the
same generated target. -/
def terminalPrimeIndex {index : Nat} (value : Nat)
    (isPrime : Nat.Prime value)
    (leTarget : value ≤ (evenTargetHistory index).cardinalShadow) :
    GeneratedPrimeIndexAt index := by
  refine ⟨value, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  apply Nat.ne_of_gt
  apply isPrime.factorization_pos_of_dvd
  · rw [factorialHistory_cardinalShadow]
    exact Nat.factorial_ne_zero _
  · rw [factorialHistory_cardinalShadow]
    exact Nat.dvd_factorial isPrime.pos leTarget

@[simp] theorem terminalPrimeIndex_value {index : Nat} (value : Nat)
    (isPrime : Nat.Prime value)
    (leTarget : value ≤ (evenTargetHistory index).cardinalShadow) :
    (terminalPrimeIndex value isPrime leTarget).1 = value :=
  rfl

/-- A terminal split materializes both coordinates from the exact target's
factorization support and lands in the existing effective additive fibre. -/
def fibreOfTerminal {index : Nat} {state : EffectiveSplitAt index}
    (terminal : PrimePairTerminalAt state) :
    EffectiveAdditiveFibreAt index := by
  let leftIndex : GeneratedPrimeIndexAt index :=
    terminalPrimeIndex (splitLeft state) terminal.leftPrime
      (splitLeft_le_target state)
  let rightIndex : GeneratedPrimeIndexAt index :=
    terminalPrimeIndex (splitRight state) terminal.rightPrime
      (by
        unfold splitRight
        exact Nat.sub_le _ _)
  refine ⟨(leftIndex, rightIndex), ?_⟩
  apply UnitHistory.eq_of_cardinalShadow_eq
  simp only [additiveEvaluation, UnitHistory.cardinalShadow_parallel]
  have leftValue :
      (generatedPrimeHistory leftIndex).cardinalShadow = splitLeft state := by
    rw [generatedPrimeHistory_cardinalShadow]
    rfl
  have rightValue :
      (generatedPrimeHistory rightIndex).cardinalShadow = splitRight state := by
    rw [generatedPrimeHistory_cardinalShadow]
    rfl
  rw [leftValue, rightValue]
  exact split_landing state

abbrev FactorRepairTerminalTraceAt (index : Nat) (indexInRange : 1 ≤ index) :=
  TerminalTraceAt (factorRepairLaw index) (canonicalSplit index indexInRange)

abbrev FactorRepairCycleResidualAt (index : Nat) (indexInRange : 1 ≤ index) :=
  CycleResidualAt (factorRepairLaw index) (canonicalSplit index indexInRange)

inductive EffectiveFactorRepairDispositionAt
    (index : Nat) (indexInRange : 1 ≤ index) : Type
  | inhabited
      (trace : FactorRepairTerminalTraceAt index indexInRange)
      (fibre : EffectiveAdditiveFibreAt index)
      (fibre_eq : fibre = fibreOfTerminal trace.terminal)
  | cycle
      (residual : FactorRepairCycleResidualAt index indexInRange)

noncomputable def generatedFactorRepairDisposition
    (index : Nat) (indexInRange : 1 ≤ index) :
    EffectiveFactorRepairDispositionAt index indexInRange := by
  cases SourceGeneratedFiniteEffectiveOrbitDisposition.settle
      (factorRepairLaw index) (canonicalSplit index indexInRange) with
  | inl trace =>
      exact .inhabited trace (fibreOfTerminal trace.terminal) rfl
  | inr residual =>
      exact .cycle residual

/-- Same-occurrence producer face.  The occurrence, target factorization,
canonical start and total orbit disposition are all fixed by `index`. -/
structure RootGeneratedEffectiveFactorRepairOrbitAt
    (index : Nat) (indexInRange : 1 ≤ index) : Type 7 where
  private mk ::
  occurrence : RootedAccountedUnfolding AdditiveCalculationPoint
  occurrence_eq : occurrence = evenTargetOccurrence index
  occurrenceRoot :
    occurrence.root.rootOccurrence = initialStep.generated.occurrence
  factorization : RootGeneratedEvenTargetFactorizationAt index
  factorization_eq : factorization = generatedEvenTargetFactorization index
  target : UnitHistory
  target_eq : target = evenTargetHistory index
  source : EffectiveSplitAt index
  source_eq : source = canonicalSplit index indexInRange
  sourceLanding :
    splitLeft source + splitRight source = target.cardinalShadow
  disposition : EffectiveFactorRepairDispositionAt index indexInRange
  disposition_eq :
    disposition = generatedFactorRepairDisposition index indexInRange

noncomputable def generatedFactorRepairOrbitFace
    (index : Nat) (indexInRange : 1 ≤ index) :
    RootGeneratedEffectiveFactorRepairOrbitAt index indexInRange :=
  ⟨evenTargetOccurrence index, rfl,
    evenTargetOccurrence_root_is_exact index,
    generatedEvenTargetFactorization index, rfl,
    evenTargetHistory index, rfl,
    canonicalSplit index indexInRange, rfl,
    split_landing (canonicalSplit index indexInRange),
    generatedFactorRepairDisposition index indexInRange, rfl⟩

end
end CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
