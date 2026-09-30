import H0mework.NavierStokes.KineticRestart.ActualKineticViscousExhaustion
import H0mework.NavierStokes.Crossing.MassPersistence

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedPrefixPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticViscousExhaustion
noncomputable section
variable {nu : Viscosity}

theorem mass_continuous : Continuous (wholeVorticityEuclideanMass : ComplexVorticityHilbertState → ℝ) := by
  have same : wholeVorticityEuclideanMass = fun state : ComplexVorticityHilbertState =>
      ∑ coordinate : Coordinate, ‖pointwiseMassCoordinateSliceCLM coordinate state‖ ^ 2 :=
    funext wholeVorticityEuclideanMass_eq_pointwiseMassCoordinateSlices
  rw [same]
  exact continuous_finsetSum _ fun coordinate _ => (pointwiseMassCoordinateSliceCLM coordinate).continuous.norm.pow 2

def payment (seed : GeneratedWholeRestartCurrent nu) (index : ℕ) : ℝ :=
  wholePrefixVorticityMass (run seed index).contact.time (run seed index).receipt.stateLimit

theorem payment_nonnegative (seed : GeneratedWholeRestartCurrent nu) (index : ℕ) : 0 ≤ payment seed index :=
  wholePrefixVorticityMass_nonneg _ _

theorem payment_succ (seed : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    2 * nu.coeff * payment seed (index + 1) = wholeRestartNextKineticDissipationPayment seed index := rfl

theorem payment_integral (seed : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    payment seed index = ∫ time in 0..(run seed index).contact.time.1,
      wholeVorticityEuclideanMass (wholeRestartReceiptPhysicalTrajectory (run seed index).contact.prefixReceipt time) := by
  rw [payment, ← prefixReceipt_terminal_wholePrefixVorticityMass_eq]
  exact wholePrefixVorticityMass_receipt_eq_intervalIntegral _ _

theorem prefix_integrable (seed : GeneratedWholeRestartCurrent nu) (length : ℕ) :
    IntervalIntegrable (fun time => wholeVorticityEuclideanMass (wholeRestartPrefixPhysicalTrajectory seed length time))
      volume 0 (elapsedTime seed length) :=
  (mass_continuous.comp_continuousOn (wholeRestartPrefixPhysicalTrajectory_continuousOn seed length)).intervalIntegrable_of_Icc
    (elapsedTime_nonneg seed length)

theorem prefix_integral (seed : GeneratedWholeRestartCurrent nu) (length : ℕ) :
    (∫ time in 0..elapsedTime seed length,
      wholeVorticityEuclideanMass (wholeRestartPrefixPhysicalTrajectory seed length time)) =
      ∑ index ∈ Finset.range length, payment seed index := by
  have integrable := prefix_integrable seed length
  have each (index : ℕ) (inside : index < length) :
      IntervalIntegrable (fun time => wholeVorticityEuclideanMass (wholeRestartPrefixPhysicalTrajectory seed length time))
        volume (elapsedTime seed index) (elapsedTime seed (index + 1)) := by
    apply integrable.mono_set
    rw [uIcc_of_le (elapsedTime_nonneg seed length), uIcc_of_le ((elapsedTime_strictMono seed).monotone (Nat.le_succ index))]
    exact Icc_subset_Icc (elapsedTime_nonneg seed index) ((elapsedTime_strictMono seed).monotone (Nat.succ_le_of_lt inside))
  have split := intervalIntegral.sum_integral_adjacent_intervals each
  rw [elapsedTime_zero] at split
  rw [← split]
  apply Finset.sum_congr rfl
  intro index inside
  rw [Finset.mem_range] at inside
  calc
    _ = ∫ time in elapsedTime seed index..elapsedTime seed (index + 1),
        wholeVorticityEuclideanMass (wholeRestartReceiptPhysicalTrajectory (run seed index).contact.prefixReceipt
          (time - elapsedTime seed index)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with time member
      rw [uIoc_of_le ((elapsedTime_strictMono seed).monotone (Nat.le_succ index))] at member
      rw [wholeRestartPrefixPhysicalTrajectory_eq_receipt seed inside member]
    _ = payment seed index := by
      rw [intervalIntegral.integral_comp_sub_right (f := fun sample => wholeVorticityEuclideanMass
        (wholeRestartReceiptPhysicalTrajectory (run seed index).contact.prefixReceipt sample)),
        sub_self, elapsedTime_succ, add_sub_cancel_left]
      exact (payment_integral seed index).symm

def budget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  payment seed 0 + puncturedWholeVorticityKineticMass seed.contact.physicalState / (2 * nu.coeff)

theorem payment_sum_bound (seed : GeneratedWholeRestartCurrent nu) (length : ℕ) :
    (∑ index ∈ Finset.range length, payment seed index) ≤ budget seed := by
  cases length with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact add_nonneg (payment_nonnegative seed 0) (div_nonneg (puncturedWholeVorticityKineticMass_nonneg _) (by positivity [nu.coeff_pos]))
  | succ length =>
      rw [Finset.sum_range_succ']
      rw [budget, add_comm (payment seed 0)]
      apply add_le_add_left
      apply (le_div_iff₀ (by positivity [nu.coeff_pos] : 0 < 2 * nu.coeff)).mpr
      rw [Finset.sum_mul]
      have same : (∑ index ∈ Finset.range length, payment seed (index + 1) * (2 * nu.coeff)) =
          ∑ index ∈ Finset.range length, wholeRestartNextKineticDissipationPayment seed index := by
        apply Finset.sum_congr rfl
        intro index _
        rw [mul_comm, payment_succ]
      rw [same]
      exact (summable_wholeRestartNextKineticDissipationPayment seed).sum_le_tsum _
        (fun index _ => wholeRestartNextKineticDissipationPayment_nonneg seed index) |>.trans
          (tsum_wholeRestartNextKineticDissipationPayment_le_initial seed)

theorem prefix_integral_bound (seed : GeneratedWholeRestartCurrent nu) (length : ℕ) :
    (∫ time in 0..elapsedTime seed length,
      wholeVorticityEuclideanMass (wholeRestartPrefixPhysicalTrajectory seed length time)) ≤ budget seed := by
  rw [prefix_integral]
  exact payment_sum_bound seed length

end
end SaturationMonoid.NavierStokes.NativeUnheatedPrefixPayment
