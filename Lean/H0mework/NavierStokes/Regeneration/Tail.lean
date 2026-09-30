import H0mework.NavierStokes.ClockAccount.DensityAccount

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceDensityRegeneration

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedKineticAdvance

noncomputable section

theorem barrierTail_antitone (nu : Viscosity) : Antitone (standingActionBarrierTail nu) := by
  apply antitone_nat_of_succ_le
  intro level
  have step := standingActionBarrierTail_step nu level
  have positive : 0 ≤ standingActionBarrierModel nu level := by
    unfold standingActionBarrierModel
    exact inv_nonneg.mpr (mul_nonneg (sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu).le
      (pow_nonneg (Nat.cast_nonneg _) _))
  linarith

private theorem source_model_le_telescoping (offset : Nat) :
    standingActionBarrierModel butterflyGainViscosity (1 + offset) ≤
      ((offset : Real) + 1)⁻¹ - ((offset : Real) + 1 + 1)⁻¹ := by
  let n : Real := (offset : Real) + 1
  have nOne : 1 ≤ n := by dsimp only [n]; linarith [Nat.cast_nonneg (α := Real) offset]
  have nPos : 0 < n := lt_of_lt_of_le zero_lt_one nOne
  have coefficient : 2 ≤ sourceOwnedWholeStateBarrierSeventhCoefficient butterflyGainViscosity := by
    rw [butterflyGainSeventhCoefficient_eq]
    norm_num
  have powers : n ^ 2 ≤ n ^ 7 := pow_le_pow_right₀ nOne (by norm_num)
  have denominator : n * (n + 1) ≤
      sourceOwnedWholeStateBarrierSeventhCoefficient butterflyGainViscosity * n ^ 7 := by
    have scaled := mul_le_mul_of_nonneg_right coefficient (pow_nonneg nPos.le 7)
    nlinarith [mul_le_mul_of_nonneg_left nOne nPos.le]
  calc
    _ = (sourceOwnedWholeStateBarrierSeventhCoefficient butterflyGainViscosity * n ^ 7)⁻¹ := by
      simp [standingActionBarrierModel, n, add_comm]
    _ ≤ (n * (n + 1))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) denominator
    _ = n⁻¹ - (n + 1)⁻¹ := by field_simp; ring

private theorem source_tail_one_le_one : standingActionBarrierTail butterflyGainViscosity 1 ≤ 1 := by
  unfold standingActionBarrierTail
  apply Real.tsum_le_of_sum_range_le
  · intro offset
    unfold standingActionBarrierModel
    exact inv_nonneg.mpr (mul_nonneg (sourceOwnedWholeStateBarrierSeventhCoefficient_pos _).le
      (pow_nonneg (Nat.cast_nonneg _) _))
  · intro length
    have bound := Finset.sum_le_sum fun offset (_ : offset ∈ Finset.range length) =>
      source_model_le_telescoping offset
    have telescopes : (∑ offset ∈ Finset.range length,
        (((offset : Real) + 1)⁻¹ - ((offset : Real) + 1 + 1)⁻¹)) =
      1 - ((length : Real) + 1)⁻¹ := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, inv_one] using
        Finset.sum_range_sub' (fun offset : Nat => ((offset : Real) + 1)⁻¹) length
    rw [telescopes] at bound
    exact bound.trans (sub_le_self _ (by positivity))

theorem source_tail_le_one (stage : Nat) : standingActionBarrierTail butterflyGainViscosity
    (source.stateAfter stage).1.standing.anchorLevel ≤ 1 := by
  have anchor := standingActionAnchorLevel_ge_eightyEight stage
  exact (barrierTail_antitone butterflyGainViscosity (by omega : 1 ≤
    (source.stateAfter stage).1.standing.anchorLevel)).trans source_tail_one_le_one

theorem source_tail_next_le (stage : Nat) : standingActionBarrierTail butterflyGainViscosity
    (source.stateAfter (stage + 1)).1.standing.anchorLevel ≤ standingActionBarrierTail butterflyGainViscosity
      (source.stateAfter stage).1.standing.anchorLevel := by
  apply barrierTail_antitone
  have current := congrArg
    (fun runtime : GeneratedWholeRestartCurrent.GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity =>
      runtime.standing.anchorLevel)
    (standingActionWholeRestartMediumSource_stateAfter_current stackedInitialActionMaterialInstruction stage)
  have successor := congrArg
    (fun runtime : GeneratedWholeRestartCurrent.GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity =>
      runtime.standing.anchorLevel)
    (standingActionWholeRestartMediumSource_stateAfter_current stackedInitialActionMaterialInstruction (stage + 1))
  calc
    _ = (runCellStanding stackedShortCurrent stage).anchorLevel := current
    _ ≤ (runCellStanding stackedShortCurrent (stage + 1)).anchorLevel := by
      exact (Nat.le_add_right _ _).trans_eq
        (cellStanding_anchorLevel_next (runCellStanding stackedShortCurrent stage)).symm
    _ = _ := successor.symm

end
end SaturationMonoid.NavierStokes.SourceDensityRegeneration
