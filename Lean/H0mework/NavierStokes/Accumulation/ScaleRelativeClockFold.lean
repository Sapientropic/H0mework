import H0mework.NavierStokes.Accumulation.TemporalEnstrophyLedger

/-!
# Variable-exponent scale-relative native clock fold

The seventh-order source barrier does not require the special work exponent
`3 / 2`.  Any same-edge mass production law of order `M^(1 + ε)`, with
`ε > 0`, closes the clock.  Written in debit form, this is

```text
charge / (M + 1)^(p - 1) ≤ M_next - M,
1 < p < 7.
```

The physical debit generates `M + 1 ≳ n^(1/p)` and hence a reciprocal
barrier majorant `n^(-7/p)`.  Since `7/p > 1`, the actual contact clock is
summable.  Recurrence and summability remain conclusions of the fold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartScaleRelativeClockFold

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork

noncomputable section

private theorem variablePotential_step
    {base debit charge exponent : Real}
    (basePos : 0 < base)
    (debitNonneg : 0 ≤ debit)
    (oneLeExponent : 1 ≤ exponent)
    (charged : charge ≤ base ^ (exponent - 1) * debit) :
    base ^ exponent + charge ≤ (base + debit) ^ exponent := by
  let ratio : Real := debit / base
  have ratioNonneg : 0 ≤ ratio :=
    div_nonneg debitNonneg basePos.le
  have bernoulli := one_add_mul_self_le_rpow_one_add
    (p := exponent) (s := ratio) (by linarith) oneLeExponent
  have basePowerNonneg : 0 ≤ base ^ exponent :=
    Real.rpow_nonneg basePos.le _
  have scaledBernoulli :=
    mul_le_mul_of_nonneg_left bernoulli basePowerNonneg
  have powerDiv :
      base ^ exponent / base = base ^ (exponent - 1) := by
    rw [← Real.rpow_sub_one basePos.ne' exponent]
  have leftEq :
      base ^ exponent * (1 + exponent * ratio) =
        base ^ exponent +
          exponent * base ^ (exponent - 1) * debit := by
    dsimp only [ratio]
    rw [show base ^ exponent *
          (1 + exponent * (debit / base)) =
        base ^ exponent +
          exponent * (base ^ exponent / base) * debit by ring,
      powerDiv]
  have onePlusRatioNonneg : 0 ≤ 1 + ratio := by linarith
  have rightEq :
      base ^ exponent * (1 + ratio) ^ exponent =
        (base + debit) ^ exponent := by
    rw [← Real.mul_rpow basePos.le onePlusRatioNonneg]
    congr 1
    dsimp only [ratio]
    field_simp [basePos.ne']
  have potentialStep :
      base ^ exponent +
          exponent * base ^ (exponent - 1) * debit ≤
        (base + debit) ^ exponent := by
    rw [← leftEq, ← rightEq]
    exact scaledBernoulli
  have weightedNonneg :
      0 ≤ base ^ (exponent - 1) * debit :=
    mul_nonneg (Real.rpow_nonneg basePos.le _) debitNonneg
  have chargedByScaled :
      charge ≤ exponent * base ^ (exponent - 1) * debit := by
    calc
      charge ≤ base ^ (exponent - 1) * debit := charged
      _ ≤ exponent * base ^ (exponent - 1) * debit := by
        nlinarith
  linarith

/-- Abstract source-base fold.  The base may be whole mass, a moving finite
inventory mass, or another source-generated positive scale row; the only
required commuting law is that it lies below the actual restart ceiling. -/
theorem scaled_inverseExponent_scale_growth_of_baseDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (base : Nat → Real)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (chargePos : 0 < charge)
    (basePos : ∀ index, 0 < base index)
    (baseLeCeiling : ∀ index,
      base index ≤ restartCoefficientCeiling initial index)
    (debit : ∀ index : Nat,
      charge / base index ^ (exponent - 1) ≤
        base (index + 1) - base index) :
    ∃ amplitude : Real, 0 < amplitude ∧
      ∀ index : Nat,
        amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
          restartCoefficientCeiling initial index := by
  have exponentPos : 0 < exponent := lt_trans (by norm_num) oneLtExponent
  have potentialGrowth : ∀ index : Nat,
      base 0 ^ exponent + (index : Real) * charge ≤
        base index ^ exponent := by
    intro index
    induction index with
    | zero => simp
    | succ index inductionHypothesis =>
        let edgeDebit := base (index + 1) - base index
        have denominatorPos :
            0 < base index ^ (exponent - 1) :=
          Real.rpow_pos_of_pos (basePos index) _
        have debitLower :
            charge / base index ^ (exponent - 1) ≤ edgeDebit := by
          simpa only [edgeDebit] using debit index
        have edgeDebitPos : 0 < edgeDebit :=
          (div_pos chargePos denominatorPos).trans_le debitLower
        have charged :
            charge ≤ base index ^ (exponent - 1) * edgeDebit := by
          simpa only [mul_comm] using
            (div_le_iff₀ denominatorPos).1 debitLower
        have step := variablePotential_step
          (basePos index) edgeDebitPos.le oneLtExponent.le charged
        have nextBase : base (index + 1) = base index + edgeDebit := by
          dsimp only [edgeDebit]
          ring
        rw [nextBase]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
  let initialPotential := base 0 ^ exponent
  let commonCharge := min charge initialPotential
  have initialPotentialPos : 0 < initialPotential :=
    Real.rpow_pos_of_pos (basePos 0) _
  have commonChargePos : 0 < commonCharge :=
    lt_min chargePos initialPotentialPos
  let amplitude := commonCharge ^ (1 / exponent)
  have inverseExponentPos : 0 < 1 / exponent := by positivity
  have amplitudePos : 0 < amplitude :=
    Real.rpow_pos_of_pos commonChargePos _
  refine ⟨amplitude, amplitudePos, ?_⟩
  intro index
  have commonLeCharge : commonCharge ≤ charge := min_le_left _ _
  have commonLeInitial : commonCharge ≤ initialPotential := min_le_right _ _
  have sourcePowerLower :
      (((index + 1 : Nat) : Real) * commonCharge) ≤
        base index ^ exponent := by
    have growth := potentialGrowth index
    have indexNonneg : 0 ≤ (index : Real) := Nat.cast_nonneg index
    have indexScaled : (index : Real) * commonCharge ≤
        (index : Real) * charge :=
      mul_le_mul_of_nonneg_left commonLeCharge indexNonneg
    norm_num [Nat.cast_add, Nat.cast_one]
    dsimp only [initialPotential] at commonLeInitial
    linarith
  have sourcePowerNonneg :
      0 ≤ ((index + 1 : Nat) : Real) * commonCharge := by positivity
  have rootLower := Real.rpow_le_rpow sourcePowerNonneg sourcePowerLower
    inverseExponentPos.le
  have cancelPower :
      (base index ^ exponent) ^ (1 / exponent) = base index := by
    rw [← Real.rpow_mul (basePos index).le]
    field_simp [exponentPos.ne']
    rw [Real.rpow_one]
  have baseScaleLower :
      amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
        base index := by
    rw [show amplitude *
          (((index + 1 : Nat) : Real) ^ (1 / exponent)) =
        (((index + 1 : Nat) : Real) * commonCharge) ^
          (1 / exponent) by
      dsimp only [amplitude]
      rw [Real.mul_rpow (by positivity) commonChargePos.le]
      ring]
    exact rootLower.trans_eq cancelPower
  exact baseScaleLower.trans (baseLeCeiling index)

/-- A same-edge debit with any exponent strictly below the seventh-order
barrier generates its own polynomial scale lineage. -/
theorem scaled_inverseExponent_scale_growth_of_massDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (chargePos : 0 < charge)
    (debit : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (exponent - 1) ≤
        restartPhysicalVorticityMass initial (index + 1) -
          restartPhysicalVorticityMass initial index) :
    ∃ amplitude : Real, 0 < amplitude ∧
      ∀ index : Nat,
        amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
          restartCoefficientCeiling initial index := by
  have exponentPos : 0 < exponent := lt_trans (by norm_num) oneLtExponent
  let massBase : Nat → Real := fun index =>
    restartPhysicalVorticityMass initial index + 1
  have massBasePos : ∀ index, 0 < massBase index := by
    intro index
    have massNonneg :
        0 ≤ restartPhysicalVorticityMass initial index := by
      unfold restartPhysicalVorticityMass
      exact wholeVorticityEuclideanMass_nonneg _
    dsimp only [massBase]
    linarith
  have potentialGrowth : ∀ index : Nat,
      massBase 0 ^ exponent + (index : Real) * charge ≤
        massBase index ^ exponent := by
    intro index
    induction index with
    | zero => simp
    | succ index inductionHypothesis =>
        let edgeDebit :=
          restartPhysicalVorticityMass initial (index + 1) -
            restartPhysicalVorticityMass initial index
        have denominatorPos :
            0 < massBase index ^ (exponent - 1) :=
          Real.rpow_pos_of_pos (massBasePos index) _
        have debitLower :
            charge / massBase index ^ (exponent - 1) ≤ edgeDebit := by
          simpa only [massBase, edgeDebit] using debit index
        have edgeDebitPos : 0 < edgeDebit :=
          (div_pos chargePos denominatorPos).trans_le debitLower
        have charged :
            charge ≤ massBase index ^ (exponent - 1) * edgeDebit :=
          by
            simpa only [mul_comm] using
              (div_le_iff₀ denominatorPos).1 debitLower
        have step := variablePotential_step
          (massBasePos index) edgeDebitPos.le oneLtExponent.le charged
        have nextBase :
            massBase (index + 1) = massBase index + edgeDebit := by
          dsimp only [massBase, edgeDebit]
          ring
        rw [nextBase]
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
  let initialPotential := massBase 0 ^ exponent
  let commonCharge := min charge initialPotential
  have initialPotentialPos : 0 < initialPotential :=
    Real.rpow_pos_of_pos (massBasePos 0) _
  have commonChargePos : 0 < commonCharge :=
    lt_min chargePos initialPotentialPos
  let amplitude := commonCharge ^ (1 / exponent)
  have inverseExponentPos : 0 < 1 / exponent := by positivity
  have amplitudePos : 0 < amplitude :=
    Real.rpow_pos_of_pos commonChargePos _
  refine ⟨amplitude, amplitudePos, ?_⟩
  intro index
  have commonLeCharge : commonCharge ≤ charge := min_le_left _ _
  have commonLeInitial : commonCharge ≤ initialPotential := min_le_right _ _
  have sourcePowerLower :
      (((index + 1 : Nat) : Real) * commonCharge) ≤
        massBase index ^ exponent := by
    have growth := potentialGrowth index
    have indexNonneg : 0 ≤ (index : Real) := Nat.cast_nonneg index
    have indexScaled : (index : Real) * commonCharge ≤
        (index : Real) * charge :=
      mul_le_mul_of_nonneg_left commonLeCharge indexNonneg
    norm_num [Nat.cast_add, Nat.cast_one]
    dsimp only [initialPotential] at commonLeInitial
    linarith
  have sourcePowerNonneg :
      0 ≤ ((index + 1 : Nat) : Real) * commonCharge := by positivity
  have rootLower := Real.rpow_le_rpow sourcePowerNonneg sourcePowerLower
    inverseExponentPos.le
  have cancelPower :
      (massBase index ^ exponent) ^ (1 / exponent) =
        massBase index := by
    rw [← Real.rpow_mul (massBasePos index).le]
    have exponentNe : exponent ≠ 0 := exponentPos.ne'
    field_simp [exponentNe]
    rw [Real.rpow_one]
  have baseScaleLower :
      amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
        massBase index := by
    rw [show amplitude *
          (((index + 1 : Nat) : Real) ^ (1 / exponent)) =
        (((index + 1 : Nat) : Real) * commonCharge) ^
          (1 / exponent) by
      dsimp only [amplitude]
      rw [Real.mul_rpow (by positivity) commonChargePos.le]
      ring]
    exact rootLower.trans_eq cancelPower
  have massBaseLeCeiling :
      massBase index ≤ restartCoefficientCeiling initial index := by
    unfold massBase restartPhysicalVorticityMass restartCoefficientCeiling
    change
      wholeVorticityEuclideanMass
            (run initial index).contact.physicalState + 1 ≤
        (wholeRestartCoefficientLevel (run initial index).contact : Real)
    unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    exact Nat.le_ceil _
  exact baseScaleLower.trans massBaseLeCeiling

/-- Hybrid source-terminal fold.  A fixed-terminal scale-relative debit is
transported by the choice-eliminated emitter as either one exact level step
or a same-level physical mass payment retaining half the terminal debit.
The single potential `level + (mass + 1)^p` therefore grows linearly. -/
theorem hybrid_terminalDebit_scale_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (chargePos : 0 < charge)
    (terminalDebit : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (exponent - 1) ≤
        generatedWholeRestartTerminalNetEnstrophyDebit
          (generatedWholeRestartCanonicalReplay
            (run initial index).contact)) :
    ∃ amplitude : Real, 0 < amplitude ∧
      ∀ index : Nat,
        amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
          restartCoefficientCeiling initial index := by
  have exponentPos : 0 < exponent := lt_trans (by norm_num) oneLtExponent
  let massBase : Nat → Real := fun index =>
    restartPhysicalVorticityMass initial index + 1
  let level : Nat → Nat := fun index =>
    restartCoefficientLevelNat initial index
  let terminalDebitAt : Nat → Real := fun index =>
    generatedWholeRestartTerminalNetEnstrophyDebit
      (generatedWholeRestartCanonicalReplay (run initial index).contact)
  let halfCharge : Real := charge / 2
  let stepCharge : Real := min 1 halfCharge
  let potential : Nat → Real := fun index =>
    (level index : Real) + massBase index ^ exponent
  have massBasePos : ∀ index, 0 < massBase index := by
    intro index
    have massNonneg : 0 ≤ restartPhysicalVorticityMass initial index := by
      unfold restartPhysicalVorticityMass
      exact wholeVorticityEuclideanMass_nonneg _
    dsimp only [massBase]
    linarith
  have halfChargePos : 0 < halfCharge := by
    dsimp only [halfCharge]
    positivity
  have stepChargePos : 0 < stepCharge := by
    dsimp only [stepCharge]
    exact lt_min (by norm_num) halfChargePos
  have massBaseLeLevel : ∀ index,
      massBase index ≤ (level index : Real) := by
    intro index
    have wall := restartPhysicalVorticityMass_le_levelNat_sub_one
      initial index
    dsimp only [massBase, level]
    linarith
  have levelOneLe : ∀ index, (1 : Real) ≤ (level index : Real) := by
    intro index
    have levelPosReal :
        0 < (level index : Real) := by
      simpa only [level, ← restartCoefficientCeiling_eq_levelNat_cast] using
        restartCoefficientCeiling_pos initial index
    have levelPosNat : 0 < level index := by exact_mod_cast levelPosReal
    exact_mod_cast levelPosNat
  have edgeProgress : ∀ index : Nat,
      (level (index + 1) = level index + 1 ∧
          massBase index ≤ massBase (index + 1)) ∨
        (level (index + 1) = level index ∧
          halfCharge / massBase index ^ (exponent - 1) ≤
            massBase (index + 1) - massBase index) := by
    intro index
    have denominatorPos :
        0 < massBase index ^ (exponent - 1) :=
      Real.rpow_pos_of_pos (massBasePos index) _
    have sourceLower :
        charge / massBase index ^ (exponent - 1) ≤
          terminalDebitAt index := by
      simpa only [massBase, terminalDebitAt] using terminalDebit index
    have terminalPositive : 0 < terminalDebitAt index :=
      (div_pos chargePos denominatorPos).trans_le sourceLower
    have emitted :=
      run_levelAdvance_or_retainedPayment_of_terminalDebit_pos
        initial index (by simpa only [terminalDebitAt] using terminalPositive)
    have debitEq := runCellEffect_debit_eq_physicalMassChange initial index
    rcases emitted with advanced | retained
    · left
      refine ⟨advanced, ?_⟩
      have selectedDebitPos :
          0 < (runCellEffect initial index).debit.netEnstrophyDebit := by
        change 0 <
          (run initial index).nextKineticContact.cellEffect.debit.netEnstrophyDebit
        exact
          (run initial index).nextKineticContact
            |>.cellEffect_debit_pos_of_terminalDebit_pos
              (by simpa only [terminalDebitAt] using terminalPositive)
      rw [debitEq] at selectedDebitPos
      dsimp only [massBase]
      linarith
    · right
      refine ⟨retained.1, ?_⟩
      have sourceHalfLe :
          (charge / massBase index ^ (exponent - 1)) / 2 ≤
            terminalDebitAt index / 2 := by
        exact div_le_div_of_nonneg_right sourceLower (by norm_num)
      have retainedDebit :
          terminalDebitAt index / 2 <
            (runCellEffect initial index).debit.netEnstrophyDebit := by
        simpa only [terminalDebitAt] using retained.2
      rw [debitEq] at retainedDebit
      have normalized :
          halfCharge / massBase index ^ (exponent - 1) =
            (charge / massBase index ^ (exponent - 1)) / 2 := by
        dsimp only [halfCharge]
        ring
      rw [normalized]
      have retainedBase :
          terminalDebitAt index / 2 ≤
            massBase (index + 1) - massBase index := by
        dsimp only [massBase]
        linarith
      exact sourceHalfLe.trans retainedBase
  have potentialStep : ∀ index : Nat,
      potential index + stepCharge ≤ potential (index + 1) := by
    intro index
    rcases edgeProgress index with advanced | retained
    · have massPowerLe :
          massBase index ^ exponent ≤
            massBase (index + 1) ^ exponent :=
        Real.rpow_le_rpow (massBasePos index).le advanced.2 exponentPos.le
      have stepLeOne : stepCharge ≤ 1 := by
        exact min_le_left _ _
      dsimp only [potential]
      rw [advanced.1]
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith
    · let edgeDebit := massBase (index + 1) - massBase index
      have denominatorPos :
          0 < massBase index ^ (exponent - 1) :=
        Real.rpow_pos_of_pos (massBasePos index) _
      have debitLower :
          halfCharge / massBase index ^ (exponent - 1) ≤
            edgeDebit := by
        simpa only [edgeDebit] using retained.2
      have edgeDebitPos : 0 < edgeDebit :=
        (div_pos halfChargePos denominatorPos).trans_le debitLower
      have charged :
          halfCharge ≤
            massBase index ^ (exponent - 1) * edgeDebit := by
        simpa only [mul_comm] using
          (div_le_iff₀ denominatorPos).1 debitLower
      have massStep := variablePotential_step
        (massBasePos index) edgeDebitPos.le oneLtExponent.le charged
      have nextBase :
          massBase (index + 1) = massBase index + edgeDebit := by
        dsimp only [edgeDebit]
        ring
      have stepLeHalf : stepCharge ≤ halfCharge := min_le_right _ _
      dsimp only [potential]
      rw [retained.1, nextBase]
      linarith
  have potentialGrowth : ∀ index : Nat,
      potential 0 + (index : Real) * stepCharge ≤ potential index := by
    intro index
    induction index with
    | zero => simp
    | succ index inductionHypothesis =>
        have step := potentialStep index
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
  have potentialUpper : ∀ index : Nat,
      potential index ≤ 2 * (level index : Real) ^ exponent := by
    intro index
    have massPowerLe :
        massBase index ^ exponent ≤ (level index : Real) ^ exponent :=
      Real.rpow_le_rpow (massBasePos index).le
        (massBaseLeLevel index) exponentPos.le
    have levelLePower :
        (level index : Real) ≤ (level index : Real) ^ exponent :=
      Real.self_le_rpow_of_one_le (levelOneLe index) oneLtExponent.le
    dsimp only [potential]
    linarith
  let initialPotential := potential 0
  let commonCharge := min stepCharge initialPotential
  have initialPotentialPos : 0 < initialPotential := by
    dsimp only [initialPotential, potential]
    have massPowerPos : 0 < massBase 0 ^ exponent :=
      Real.rpow_pos_of_pos (massBasePos 0) _
    have levelNonneg : 0 ≤ (level 0 : Real) := by positivity
    linarith
  have commonChargePos : 0 < commonCharge :=
    lt_min stepChargePos initialPotentialPos
  let amplitude := (commonCharge / 2) ^ (1 / exponent)
  have amplitudePos : 0 < amplitude :=
    Real.rpow_pos_of_pos (div_pos commonChargePos (by norm_num)) _
  refine ⟨amplitude, amplitudePos, ?_⟩
  intro index
  have commonLeStep : commonCharge ≤ stepCharge := min_le_left _ _
  have commonLeInitial : commonCharge ≤ initialPotential := min_le_right _ _
  have sourcePowerLower :
      (((index + 1 : Nat) : Real) * commonCharge) ≤
        2 * (level index : Real) ^ exponent := by
    have growth := potentialGrowth index
    have upper := potentialUpper index
    have indexNonneg : 0 ≤ (index : Real) := Nat.cast_nonneg index
    have scaled : (index : Real) * commonCharge ≤
        (index : Real) * stepCharge :=
      mul_le_mul_of_nonneg_left commonLeStep indexNonneg
    norm_num [Nat.cast_add, Nat.cast_one]
    dsimp only [initialPotential] at commonLeInitial
    linarith
  have dividedPowerLower :
      (((index + 1 : Nat) : Real) * commonCharge / 2) ≤
        (level index : Real) ^ exponent := by
    linarith
  have sourceNonneg :
      0 ≤ (((index + 1 : Nat) : Real) * commonCharge / 2) := by
    positivity
  have inverseExponentPos : 0 < 1 / exponent := by positivity
  have rootLower := Real.rpow_le_rpow sourceNonneg dividedPowerLower
    inverseExponentPos.le
  have cancelPower :
      ((level index : Real) ^ exponent) ^ (1 / exponent) =
        (level index : Real) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ (level index : Real))]
    field_simp [exponentPos.ne']
    rw [Real.rpow_one]
  have scaleLower :
      amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
        (level index : Real) := by
    rw [show amplitude *
          (((index + 1 : Nat) : Real) ^ (1 / exponent)) =
        (((index + 1 : Nat) : Real) * commonCharge / 2) ^
          (1 / exponent) by
      dsimp only [amplitude]
      rw [show ((index + 1 : Nat) : Real) * commonCharge / 2 =
          ((index + 1 : Nat) : Real) * (commonCharge / 2) by ring]
      rw [Real.mul_rpow (by positivity)
        (div_nonneg commonChargePos.le (by norm_num))]
      ring]
    exact rootLower.trans_eq cancelPower
  simpa only [level, restartCoefficientCeiling_eq_levelNat_cast] using
    scaleLower

/-- Any `n^(1/p)` scale lower bound with `p < 7` makes the seventh-order
reciprocal barrier summable. -/
theorem summable_reciprocalBarrier_of_scaled_inverseExponent_growth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (exponent amplitude : Real)
    (exponentPos : 0 < exponent)
    (exponentLtSeven : exponent < 7)
    (amplitudePos : 0 < amplitude)
    (growth : ∀ index : Nat,
      amplitude * (((index + 1 : Nat) : Real) ^ (1 / exponent)) ≤
        restartCoefficientCeiling initial index) :
    Summable fun index => (restartBarrierSlope initial index)⁻¹ := by
  let coefficient :=
    sourceOwnedWholeStateBarrierSeventhCoefficient nu * amplitude ^ 7
  have coefficientPos : 0 < coefficient :=
    mul_pos (sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu)
      (pow_pos amplitudePos 7)
  have seriesExponentPos : 0 < 7 / exponent := div_pos (by norm_num) exponentPos
  have seriesExponentGtOne : 1 < 7 / exponent := by
    apply (lt_div_iff₀ exponentPos).2
    linarith
  have majorant : ∀ index : Nat,
      (restartBarrierSlope initial index)⁻¹ ≤
        coefficient⁻¹ *
          (1 / (((index + 1 : Nat) : Real) ^ (7 / exponent))) := by
    intro index
    let base : Real := ((index + 1 : Nat) : Real)
    have basePos : 0 < base := by
      dsimp only [base]
      positivity
    have scalePos :
        0 < restartCoefficientCeiling initial index :=
      restartCoefficientCeiling_pos initial index
    have rootNonneg : 0 ≤ base ^ (1 / exponent) :=
      Real.rpow_nonneg basePos.le _
    have basePowerEq :
        base ^ (7 / exponent) =
          (base ^ (1 / exponent)) ^ (7 : Nat) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul basePos.le]
      congr 1
      field_simp [exponentPos.ne']
      norm_num
    have seventhLe :
        amplitude ^ 7 * base ^ (7 / exponent) ≤
          restartCoefficientCeiling initial index ^ 7 := by
      calc
        amplitude ^ 7 * base ^ (7 / exponent) =
            (amplitude * base ^ (1 / exponent)) ^ 7 := by
          rw [basePowerEq, mul_pow]
        _ ≤ restartCoefficientCeiling initial index ^ 7 :=
          pow_le_pow_left₀
            (mul_nonneg amplitudePos.le rootNonneg) (growth index) 7
    have barrierLower := sourceOwnedWholeStateBarrierSeventh_le
      nu (restartCoefficientCeiling initial index) scalePos.le
    change
      sourceOwnedWholeStateBarrierSeventhCoefficient nu *
          restartCoefficientCeiling initial index ^ 7 + 1 ≤
        restartBarrierSlope initial index at barrierLower
    have modelLeBarrier :
        coefficient * base ^ (7 / exponent) ≤
          restartBarrierSlope initial index := by
      have scaled := mul_le_mul_of_nonneg_left seventhLe
        (sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu).le
      dsimp only [coefficient]
      calc
        sourceOwnedWholeStateBarrierSeventhCoefficient nu * amplitude ^ 7 *
              base ^ (7 / exponent) =
            sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              (amplitude ^ 7 * base ^ (7 / exponent)) := by ring
        _ ≤ sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              restartCoefficientCeiling initial index ^ 7 := scaled
        _ ≤ restartBarrierSlope initial index := by linarith [barrierLower]
    have modelPos :
        0 < coefficient * base ^ (7 / exponent) :=
      mul_pos coefficientPos (Real.rpow_pos_of_pos basePos _)
    have reciprocalLe :
        (restartBarrierSlope initial index)⁻¹ ≤
          (coefficient * base ^ (7 / exponent))⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le modelPos modelLeBarrier)
    calc
      (restartBarrierSlope initial index)⁻¹ ≤
          (coefficient * base ^ (7 / exponent))⁻¹ := reciprocalLe
      _ = coefficient⁻¹ *
          (1 / (((index + 1 : Nat) : Real) ^ (7 / exponent))) := by
        rw [mul_inv_rev]
        simp only [one_div, base, mul_comm]
  have pSeries : Summable fun index : Nat =>
      1 / (((index + 1 : Nat) : Real) ^ (7 / exponent)) := by
    have baseSeries : Summable fun index : Nat =>
        1 / ((index : Real) ^ (7 / exponent)) :=
      Real.summable_one_div_nat_rpow.mpr seriesExponentGtOne
    exact (baseSeries.comp_injective Nat.succ_injective).congr fun index => by
      simp only [Function.comp_apply, Nat.cast_succ]
  exact (pSeries.mul_left coefficient⁻¹).of_nonneg_of_le
    (fun index => inv_nonneg.mpr
      (restartBarrierSlope_pos initial index).le)
    majorant

/-- Complete choice-eliminated clock fold.  The only domain obligation is a
same-current lower bound on the fixed full-replay terminal debit; arithmetic
branch, selected endpoint payment, scale growth and summability are outputs. -/
theorem contactTime_summable_of_fullTerminalScaleRelativeDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (exponentLtSeven : exponent < 7)
    (chargePos : 0 < charge)
    (terminalDebit : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (exponent - 1) ≤
        generatedWholeRestartTerminalNetEnstrophyDebit
          (generatedWholeRestartCanonicalReplay
            (run initial index).contact)) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  obtain ⟨amplitude, amplitudePos, growth⟩ :=
    hybrid_terminalDebit_scale_growth
      initial exponent charge oneLtExponent chargePos terminalDebit
  apply (summable_contactTime_iff_reciprocalBarrier initial).2
  exact summable_reciprocalBarrier_of_scaled_inverseExponent_growth
    initial exponent amplitude (lt_trans (by norm_num) oneLtExponent)
      exponentLtSeven amplitudePos growth

/-- Action-language mouth for the same choice-eliminated fold.  The source
may prove its lower law directly on the complete whole-row action of each
fixed replay; the exact terminal ledger performs the only conversion. -/
theorem contactTime_summable_of_fullReplayScaleRelativeAction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (exponentLtSeven : exponent < 7)
    (chargePos : 0 < charge)
    (action : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (exponent - 1) ≤
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            (generatedWholeRestartWholeContinuousMildSerrinReceipt
              (generatedWholeRestartCanonicalReplay
                (run initial index).contact)) wave) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  apply contactTime_summable_of_fullTerminalScaleRelativeDebit
    initial exponent charge oneLtExponent exponentLtSeven chargePos
  intro index
  rw [generatedWholeRestartTerminalNetEnstrophyDebit_eq_tsum_action]
  exact action index

/-- Complete variable-exponent physical residence fold. -/
theorem contactTime_summable_of_variableScaleRelativeMassDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (exponent charge : Real)
    (oneLtExponent : 1 < exponent)
    (exponentLtSeven : exponent < 7)
    (chargePos : 0 < charge)
    (debit : ∀ index : Nat,
      charge /
          (restartPhysicalVorticityMass initial index + 1) ^
            (exponent - 1) ≤
        restartPhysicalVorticityMass initial (index + 1) -
          restartPhysicalVorticityMass initial index) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  obtain ⟨amplitude, amplitudePos, growth⟩ :=
    scaled_inverseExponent_scale_growth_of_massDebit
      initial exponent charge oneLtExponent chargePos debit
  apply (summable_contactTime_iff_reciprocalBarrier initial).2
  exact summable_reciprocalBarrier_of_scaled_inverseExponent_growth
    initial exponent amplitude (lt_trans (by norm_num) oneLtExponent)
      exponentLtSeven amplitudePos growth

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartScaleRelativeClockFold
end NavierStokes
end SaturationMonoid
