import H0mework.NavierStokes.Regeneration.LateTerminal

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set MeasureTheory
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open RationalVorticityEvaluator

noncomputable section

private theorem fifty_window_numeric : (50945 / 68 : Real) * Real.exp (-14) < 50 / 79500 := by
  have one : (2718 : Real) / 1000 < Real.exp 1 :=
    (by norm_num : (2718 : Real) / 1000 < 2.7182818283).trans Real.exp_one_gt_d9
  have power := pow_lt_pow_left₀ one (by norm_num : (0 : Real) ≤ 2718 / 1000)
    (by norm_num : (14 : Nat) ≠ 0)
  rw [← Real.exp_nat_mul] at power
  norm_num at power
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos 14)).mpr
  linarith

variable {stage : Nat} {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
  (reachable : ButterflyCreditClockFaceReachableAt stage face)
  (shortfall : ButterflyCreditClockFaceResidualAt stage face
    (sourceGeneratedStandingActionRunClockDisposition stackedInitialActionMaterialInstruction stage))

include reachable shortfall

theorem lastFifty_integral_lt :
    let T := WholePrefixState.duration concreteCounterexampleInitial (stage + 1)
    let receipt := WholePrefixReceipt.receipt concreteCounterexampleInitial (stage + 1)
    (∫ actual in (T - 50)..T, WholeKineticDecay.massField receipt actual) < 50 / 79500 := by
  dsimp only
  let T := WholePrefixState.duration concreteCounterexampleInitial (stage + 1)
  let receipt := WholePrefixReceipt.receipt concreteCounterexampleInitial (stage + 1)
  have late : 750 < T := residual_terminal_gt_750 reachable shortfall
  let start : Icc (0 : Real) T := ⟨T - 50, by constructor <;> linarith⟩
  let finish : Icc (0 : Real) T := ⟨T, by constructor <;> linarith⟩
  have initialEnergy := WholeKineticDecay.kineticPrimitive_eq receipt start
  have finalEnergy := WholeKineticDecay.kineticPrimitive_eq receipt finish
  have continuous := WholeKineticDecay.massField_continuous receipt
  have split := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous.intervalIntegrable 0 (T - 50)) (continuous.intervalIntegrable (T - 50) T)
  unfold WholeKineticDecay.kineticPrimitive at initialEnergy finalEnergy
  change _ - 2 * butterflyGainViscosity.coeff *
    (∫ actual in (0 : Real)..(T - 50), WholeKineticDecay.massField receipt actual) = _ at initialEnergy
  change _ - 2 * butterflyGainViscosity.coeff *
    (∫ actual in (0 : Real)..T, WholeKineticDecay.massField receipt actual) = _ at finalEnergy
  rw [← split] at finalEnergy
  have dissipation : (∫ actual in (T - 50)..T, WholeKineticDecay.massField receipt actual) ≤
      puncturedWholeVorticityKineticMass (receipt.wholePath start) / (2 * butterflyGainViscosity.coeff) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos)).mpr
    nlinarith [puncturedWholeVorticityKineticMass_nonneg (receipt.wholePath finish)]
  have decay := WholeKineticDecay.fixed_prefix_kinetic_le_exp (stage + 1) start
  have scaled := div_le_div_of_nonneg_right decay
    (show 0 ≤ 2 * butterflyGainViscosity.coeff from
      (mul_pos (by norm_num) butterflyGainViscosity.coeff_pos).le)
  have normalized : puncturedWholeVorticityKineticMass (receipt.wholePath start) /
      (2 * butterflyGainViscosity.coeff) ≤ (50945 / 68 : Real) * Real.exp (-(T - 50) / 50) := by
    calc
      _ ≤ (KineticSelectionHorizon.rawKinetic * Real.exp
          (-2 * concreteCounterexampleViscosity.coeff * (2 * Real.pi) ^ 2 * start.1)) /
          (2 * butterflyGainViscosity.coeff) := scaled
      _ = _ := by
        rw [show (KineticSelectionHorizon.rawKinetic * Real.exp
        (-2 * concreteCounterexampleViscosity.coeff * (2 * Real.pi) ^ 2 * start.1)) /
        (2 * butterflyGainViscosity.coeff) =
        (KineticSelectionHorizon.rawKinetic / (2 * butterflyGainViscosity.coeff)) * Real.exp
          (-2 * concreteCounterexampleViscosity.coeff * (2 * Real.pi) ^ 2 * start.1) by ring,
          SourceTerminalSelection.rawKineticAccount_eq]
        congr 2
        change -2 * butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 * (T - 50) = -(T - 50) / 50
        rw [show -2 * butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 =
          -2 * (butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) by ring, butterflyGainViscosity_scaled]
        ring
  have exponent : -(T - 50) / 50 < (-14 : Real) := by linarith
  have expLe := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr exponent)
    (by norm_num : (0 : Real) < 50945 / 68)
  exact ((dissipation.trans normalized).trans_lt expLe).trans fifty_window_numeric

/-- The low point belongs to the same original cumulative prefix and its
last fifty physical time units; no receipt or low point is supplied. -/
theorem residual_source_late_lowPoint :
    ∃ actual : Icc (0 : Real) (WholePrefixState.duration concreteCounterexampleInitial (stage + 1)),
      WholePrefixState.duration concreteCounterexampleInitial (stage + 1) - 50 ≤ actual.1 ∧
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeVorticityEuclideanMass
          ((WholePrefixReceipt.receipt concreteCounterexampleInitial (stage + 1)).wholePath actual) < 1 / 79500 := by
  let T := WholePrefixState.duration concreteCounterexampleInitial (stage + 1)
  let receipt := WholePrefixReceipt.receipt concreteCounterexampleInitial (stage + 1)
  have late : 750 < T := residual_terminal_gt_750 reachable shortfall
  have paid := lastFifty_integral_lt reachable shortfall
  by_contra noLow
  have lower : ∀ actual ∈ Icc (T - 50) T, (1 : Real) / 79500 ≤ WholeKineticDecay.massField receipt actual := by
    intro actual inside
    let point : Icc (0 : Real) T := ⟨actual, by constructor <;> linarith [inside.1, inside.2]⟩
    have atPoint : (1 : Real) / 79500 ≤
        ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeVorticityEuclideanMass
          (receipt.wholePath point) := le_of_not_gt (fun low => noLow ⟨point, inside.1, low⟩)
    simpa only [← WholeKineticDecay.massField_at receipt point] using atPoint
  have compare := intervalIntegral.integral_mono_on (μ := volume) (show T - 50 ≤ T by linarith)
    (continuous_const.intervalIntegrable (T - 50) T)
    ((WholeKineticDecay.massField_continuous receipt).intervalIntegrable (T - 50) T) lower
  rw [intervalIntegral.integral_const, smul_eq_mul] at compare
  dsimp only at paid
  change (∫ actual in (T - 50)..T, WholeKineticDecay.massField receipt actual) < _ at paid
  linarith

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
