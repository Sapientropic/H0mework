import H0mework.NavierStokes.WholeSpace.WholeSerrinEnstrophyExponential
import H0mework.NavierStokes.Restart.EnstrophyWork

/-!
# Critical Serrin-action exhaustion on the native whole restart chain

Every chronological edge is the actual positive-time prefix written by the
source-generated whole-flow recursion.  The exponential whole-receipt bound
therefore glues on the exact adjacent physical state and telescopes over every
finite native prefix.

Consequently, finite accumulation of the generated physical clock forces the
accumulated critical Serrin action of those same receipts to be unbounded.
No future tail, cutoff, coefficient ceiling, restart branch, or continuation
certificate occurs in the theorem mouth.
-/

open Set Filter MeasureTheory
open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSerrinActionExhaustion

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyExponential
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact

noncomputable section

/-- Critical Serrin action paid by one actual source-generated restart edge. -/
def wholeRestartSegmentSerrinAction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  ∫ time,
    (run initial index).contact.prefixReceipt.serrinDensity time
    ∂(commonTimeMeasure (run initial index).contact.time.1)

/-- Critical Serrin action of the exact finite prefix of the native chain. -/
def wholeRestartAccumulatedSerrinAction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentSerrinAction initial index

theorem wholeRestartSegmentSerrinAction_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartSegmentSerrinAction initial index := by
  unfold wholeRestartSegmentSerrinAction
  apply MeasureTheory.integral_nonneg
  intro time
  exact sq_nonneg _

@[simp] theorem wholeRestartAccumulatedSerrinAction_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    wholeRestartAccumulatedSerrinAction initial 0 = 0 := by
  simp [wholeRestartAccumulatedSerrinAction]

@[simp] theorem wholeRestartAccumulatedSerrinAction_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    wholeRestartAccumulatedSerrinAction initial (length + 1) =
      wholeRestartAccumulatedSerrinAction initial length +
        wholeRestartSegmentSerrinAction initial length := by
  simp [wholeRestartAccumulatedSerrinAction,
    Finset.sum_range_succ]

theorem wholeRestartAccumulatedSerrinAction_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    0 ≤ wholeRestartAccumulatedSerrinAction initial length := by
  unfold wholeRestartAccumulatedSerrinAction
  exact Finset.sum_nonneg fun index _ =>
    wholeRestartSegmentSerrinAction_nonneg initial index

/-- One native restart edge transports whole enstrophy with a multiplier
generated solely by that edge's actual critical Serrin action. -/
theorem wholeRestartBoundaryMass_succ_le_mul_exp_segmentSerrinAction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartBoundaryMass initial (index + 1) ≤
      wholeRestartBoundaryMass initial index *
        Real.exp
          ((72 * ν.coeff⁻¹) *
            wholeRestartSegmentSerrinAction initial index) := by
  let receipt := (run initial index).contact.prefixReceipt
  have edgeBound :=
    WholeContinuousMildSerrinReceipt.terminal_vorticityMass_le_initial_mul_exp_serrinAction
      receipt
  rw [(run initial index).contact.prefixReceipt_terminal] at edgeBound
  unfold wholeRestartBoundaryMass
  rw [wholeRestartBoundaryState_succ,
    wholeRestartBoundaryState_eq_run_initialState]
  simpa only [wholeRestartSegmentSerrinAction, receipt] using edgeBound

/-- The exact finite native prefix has the classical exponential envelope,
but its exponent is the sum of the source-generated edge actions rather than
a caller-supplied coefficient ceiling. -/
theorem wholeRestartBoundaryMass_le_initial_mul_exp_accumulatedSerrinAction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : ℕ,
      wholeRestartBoundaryMass initial length ≤
        wholeRestartBoundaryMass initial 0 *
          Real.exp
            ((72 * ν.coeff⁻¹) *
              wholeRestartAccumulatedSerrinAction initial length)
  | 0 => by simp
  | length + 1 => by
      have edgeBound :=
        wholeRestartBoundaryMass_succ_le_mul_exp_segmentSerrinAction
          initial length
      have prefixBound :=
        wholeRestartBoundaryMass_le_initial_mul_exp_accumulatedSerrinAction
          initial length
      calc
        wholeRestartBoundaryMass initial (length + 1) ≤
            wholeRestartBoundaryMass initial length *
              Real.exp
                ((72 * ν.coeff⁻¹) *
                  wholeRestartSegmentSerrinAction initial length) :=
          edgeBound
        _ ≤
            (wholeRestartBoundaryMass initial 0 *
                Real.exp
                  ((72 * ν.coeff⁻¹) *
                    wholeRestartAccumulatedSerrinAction initial length)) *
              Real.exp
                ((72 * ν.coeff⁻¹) *
                  wholeRestartSegmentSerrinAction initial length) := by
          exact mul_le_mul_of_nonneg_right prefixBound
            (Real.exp_pos _).le
        _ = wholeRestartBoundaryMass initial 0 *
              Real.exp
                ((72 * ν.coeff⁻¹) *
                  wholeRestartAccumulatedSerrinAction initial (length + 1)) := by
          rw [wholeRestartAccumulatedSerrinAction_succ,
            mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- Finite accumulation of the actual restart clock forces divergence of
the critical Serrin action on the same source-generated write-chain. -/
theorem elapsedTime_bddAbove_forces_accumulatedSerrinAction_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range (wholeRestartAccumulatedSerrinAction initial)) := by
  intro actionBounded
  apply elapsedTime_bddAbove_forces_boundaryMass_unbounded
    initial elapsedBounded
  rcases actionBounded with ⟨actionBound, actionBoundSpec⟩
  refine
    ⟨wholeRestartBoundaryMass initial 0 *
        Real.exp ((72 * ν.coeff⁻¹) * actionBound), ?_⟩
  intro mass massMem
  rcases massMem with ⟨length, rfl⟩
  have actionLe :
      wholeRestartAccumulatedSerrinAction initial length ≤
        actionBound :=
    actionBoundSpec ⟨length, rfl⟩
  have coefficientNonneg : 0 ≤ 72 * ν.coeff⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.2 ν.coeff_pos.le)
  have exponentLe :
      Real.exp
          ((72 * ν.coeff⁻¹) *
            wholeRestartAccumulatedSerrinAction initial length) ≤
        Real.exp ((72 * ν.coeff⁻¹) * actionBound) :=
    Real.exp_le_exp.mpr <|
      mul_le_mul_of_nonneg_left actionLe coefficientNonneg
  exact
    (wholeRestartBoundaryMass_le_initial_mul_exp_accumulatedSerrinAction
      initial length).trans <|
      mul_le_mul_of_nonneg_left exponentLe <| by
        unfold wholeRestartBoundaryMass
        unfold wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSerrinActionExhaustion
end NavierStokes
end SaturationMonoid
