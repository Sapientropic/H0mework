import H0mework.NavierStokes.Restart.NativeRecursion

/-!
# Cumulative half-critical dissipation on the native whole restart run

Every actual native current now decides one of two alternatives without a
caller-supplied branch: its whole coefficient mass has crossed the fixed
half-critical threshold, or its actual successor endpoint pays a positive
whole-gradient quantum.  This module telescopes the second alternative.

Consequently the complete generated run itself satisfies the global
exhaustion needed by the regularity attack:

```text
some actual current crosses the fixed critical threshold
or
the complete same-run whole-gradient payment is summable.
```

No cutoff, critical-margin certificate, restart horizon, or target path is
accepted by the theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation

open scoped BigOperators

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-- The actual whole-state half-critical crossing at one generated current. -/
def wholeRestartHalfCriticalCrossed
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : Prop :=
  (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
    criticalEnstrophyLatticeConstant *
      wholeVorticityEuclideanMass
        (run initial index).contact.physicalState

/-- The whole-gradient dissipation paid by the actual successor receipt at
one native current. -/
def wholeRestartNextCriticalGradientPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
    wholePrefixVorticityGradientMass
      (run initial index).nextContact.time
      (run initial index).nextReceipt.stateLimit

theorem wholeRestartNextCriticalGradientPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartNextCriticalGradientPayment initial index := by
  unfold wholeRestartNextCriticalGradientPayment
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (criticalEnstrophyAbsorptionCoefficient_pos
        (1 / 2 : ℝ) (by norm_num) ν).le)
    (wholePrefixVorticityGradientMass_nonneg
      (run initial index).nextContact.time
      (run initial index).nextReceipt.stateLimit)

/-- If the current actual whole state has not crossed, its very next native
endpoint and its gradient payment satisfy one coupled step ledger. -/
theorem run_contact_coefficientMass_add_criticalGradientPayment_succ_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (notCrossed : ¬ wholeRestartHalfCriticalCrossed initial index) :
    wholeVorticityEuclideanMass
          (run initial (index + 1)).contact.physicalState +
        wholeRestartNextCriticalGradientPayment initial index ≤
      wholeVorticityEuclideanMass
        (run initial index).contact.physicalState := by
  rcases
      run_nextContact_halfCriticalAbsorption_disposition initial index with
    crossed | payment
  · exact False.elim (notCrossed crossed)
  · rw [run_succ]
    exact payment

/-- Total half-critical whole-gradient payment of the first `length` actual
native successor edges. -/
def wholeRestartAccumulatedCriticalGradientPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartNextCriticalGradientPayment initial index

theorem wholeRestartAccumulatedCriticalGradientPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    0 ≤ wholeRestartAccumulatedCriticalGradientPayment initial length := by
  unfold wholeRestartAccumulatedCriticalGradientPayment
  exact Finset.sum_nonneg fun index _indexMem =>
    wholeRestartNextCriticalGradientPayment_nonneg initial index

/-- Exact no-double-payment telescope up to any prefix containing no actual
half-critical crossing. -/
theorem run_contact_coefficientMass_add_accumulatedCriticalGradientPayment_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : ℕ,
      (∀ index : ℕ, index < length →
        ¬ wholeRestartHalfCriticalCrossed initial index) →
      wholeVorticityEuclideanMass
            (run initial length).contact.physicalState +
          wholeRestartAccumulatedCriticalGradientPayment initial length ≤
        wholeVorticityEuclideanMass initial.contact.physicalState
  | 0 => by
      intro _noCrossing
      simp [wholeRestartAccumulatedCriticalGradientPayment]
  | length + 1 => by
      intro noCrossing
      have step :=
        run_contact_coefficientMass_add_criticalGradientPayment_succ_le
          initial length (noCrossing length (Nat.lt_succ_self length))
      have prefixBound :=
        run_contact_coefficientMass_add_accumulatedCriticalGradientPayment_le
          initial length
          (fun index indexLt =>
            noCrossing index (indexLt.trans (Nat.lt_succ_self length)))
      unfold wholeRestartAccumulatedCriticalGradientPayment at prefixBound ⊢
      rw [Finset.sum_range_succ]
      calc
        wholeVorticityEuclideanMass
              (run initial (length + 1)).contact.physicalState +
            ((∑ index ∈ Finset.range length,
                wholeRestartNextCriticalGradientPayment initial index) +
              wholeRestartNextCriticalGradientPayment initial length) =
            (wholeVorticityEuclideanMass
                (run initial (length + 1)).contact.physicalState +
              wholeRestartNextCriticalGradientPayment initial length) +
              ∑ index ∈ Finset.range length,
                wholeRestartNextCriticalGradientPayment initial index := by
          ring
        _ ≤
            wholeVorticityEuclideanMass
                (run initial length).contact.physicalState +
              ∑ index ∈ Finset.range length,
                wholeRestartNextCriticalGradientPayment initial index :=
          add_le_add step le_rfl
        _ ≤ wholeVorticityEuclideanMass initial.contact.physicalState :=
          prefixBound

/-- Every crossing-free finite prefix is paid by the initial actual whole
coefficient mass. -/
theorem wholeRestartAccumulatedCriticalGradientPayment_le_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ)
    (noCrossing :
      ∀ index : ℕ, index < length →
        ¬ wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartAccumulatedCriticalGradientPayment initial length ≤
      wholeVorticityEuclideanMass initial.contact.physicalState := by
  have ledger :=
    run_contact_coefficientMass_add_accumulatedCriticalGradientPayment_le
      initial length noCrossing
  have terminalNonneg :
      0 ≤ wholeVorticityEuclideanMass
        (run initial length).contact.physicalState := by
    unfold wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  linarith

/-- The source-generated run itself exhausts the fixed critical alternative:
either an actual current crosses, or the complete actual whole-gradient
payment is summable with the initial whole mass as its sharp ceiling. -/
theorem exists_halfCriticalCrossing_or_summableCriticalGradientPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    (∃ index : ℕ, wholeRestartHalfCriticalCrossed initial index) ∨
      (Summable (wholeRestartNextCriticalGradientPayment initial) ∧
        (∑' index : ℕ,
            wholeRestartNextCriticalGradientPayment initial index) ≤
          wholeVorticityEuclideanMass initial.contact.physicalState) := by
  classical
  by_cases crossing :
      ∃ index : ℕ, wholeRestartHalfCriticalCrossed initial index
  · exact Or.inl crossing
  · right
    have noCrossing :
        ∀ index : ℕ, ¬ wholeRestartHalfCriticalCrossed initial index := by
      intro index crossed
      exact crossing ⟨index, crossed⟩
    have finiteBound :
        ∀ length : ℕ,
          wholeRestartAccumulatedCriticalGradientPayment initial length ≤
            wholeVorticityEuclideanMass initial.contact.physicalState := by
      intro length
      exact
        wholeRestartAccumulatedCriticalGradientPayment_le_initial
          initial length (fun index _indexLt => noCrossing index)
    have summable :
        Summable (wholeRestartNextCriticalGradientPayment initial) := by
      apply summable_of_sum_range_le
      · exact wholeRestartNextCriticalGradientPayment_nonneg initial
      · exact finiteBound
    exact
      ⟨summable, summable.tsum_le_of_sum_range_le finiteBound⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
end NavierStokes
end SaturationMonoid
