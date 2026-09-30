import H0mework.NavierStokes.SourceAction.Limit
import H0mework.NavierStokes.SourceAction.Convolution
import H0mework.NavierStokes.Butterfly.StackedSourceCurrent

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeFullOrderInitial

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderLimit

noncomputable section

/-- The budget is evaluated on the original finite rational Fourier table. -/
def initialMomentBudget (order : ℕ) : ℝ :=
  ∑ wave ∈ butterflyFirstStackModes, frequencySize wave ^ (2 * order) *
    complexCoordinateVectorNormSq (biotSavartVelocityCoefficient wave
      (GaussianRatVector.toComplex (butterflyFirstStackRow (-1) wave)))

theorem stacked_initial_energy_eq_budget (order : ℕ) :
    weightedVelocityEnergy butterflyFirstStackModes
      (fun wave => frequencySize wave ^ order) stackedSeedState = initialMomentBudget order := by
  unfold weightedVelocityEnergy initialMomentBudget
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [← pow_mul, Nat.mul_comm order 2]
  simp only [finiteStateVelocityCoefficient, stackedSeedState, butterflyFirstStackPhysicalState,
    finiteComplexVorticityState_apply, if_pos waveMem]

theorem stacked_initial_finite_moment_le (order : ℕ) (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed, frequencySize wave ^ (2 * order) * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient stackedSeedState wave)) ≤ initialMomentBudget order := by
  have sourceSupport : ∀ wave, wave ∉ butterflyFirstStackModes → stackedSeedState wave = 0 :=
    butterflyFirstStackPhysicalState_supported (-1)
  have bound := weightedVelocityEnergy_le_of_support observed butterflyFirstStackModes
    (fun wave => frequencySize wave ^ order) stackedSeedState sourceSupport
  rw [stacked_initial_energy_eq_budget] at bound
  simpa only [weightedVelocityEnergy, ← pow_mul, Nat.mul_comm order 2] using bound

theorem stacked_initial_moment_summable (order : ℕ) :
    Summable (fun wave => frequencySize wave ^ (2 * order) * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient stackedSeedState wave)) := by
  apply summable_of_sum_le (c := initialMomentBudget order)
  · intro wave
    apply mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _)
    unfold complexCoordinateVectorNormSq
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · exact stacked_initial_finite_moment_le order

theorem stacked_initial_moment_eq_budget (order : ℕ) :
    (∑' wave, frequencySize wave ^ (2 * order) * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient stackedSeedState wave)) = initialMomentBudget order := by
  rw [tsum_eq_sum (s := butterflyFirstStackModes)]
  · simpa only [weightedVelocityEnergy, ← pow_mul, Nat.mul_comm order 2] using
      stacked_initial_energy_eq_budget order
  · intro wave outside
    have zeroRow : stackedSeedState wave = 0 := butterflyFirstStackPhysicalState_supported (-1) wave outside
    simp [finiteStateVelocityCoefficient, zeroRow, complexCoordinateVectorNormSq]

theorem stacked_initial_capped_energy_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (observed : Finset IntegerWavevector) :
    weightedVelocityEnergy observed (wordWeight order ceiling) stackedSeedState ≤ initialMomentBudget order := by
  apply le_trans _ (stacked_initial_finite_moment_le order observed)
  unfold weightedVelocityEnergy
  apply Finset.sum_le_sum
  intro wave _
  have weightLe : wordWeight order ceiling wave ≤ frequencySize wave ^ order :=
    pow_le_pow_left₀ (le_min (frequencySize_nonneg wave) nonnegative) (min_le_left _ _) order
  have squareLe := pow_le_pow_left₀ (wordWeight_nonneg order ceiling nonnegative wave) weightLe 2
  rw [← pow_mul, Nat.mul_comm order 2] at squareLe
  apply mul_le_mul_of_nonneg_right squareLe
  unfold complexCoordinateVectorNormSq
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Every original Galerkin initial projection consumes this same finite
material budget, uniformly in its radius and in the weight truncation. -/
theorem stacked_replay_initial_capped_energy_le
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling) (radius : ℕ) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling)
      ((stackedReplay.current radius).trajectory 0) ≤ initialMomentBudget order := by
  rw [(stackedReplay.current radius).initial]
  change weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling)
    (complexSharpSupportProjection (wholeRestartModes radius) stackedSeedState) ≤ _
  have projectionRead :
      weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling)
        (complexSharpSupportProjection (wholeRestartModes radius) stackedSeedState) =
      weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) stackedSeedState := by
    unfold weightedVelocityEnergy
    apply Finset.sum_congr rfl
    intro wave waveMem
    simp only [finiteStateVelocityCoefficient, complexSharpSupportProjection_apply, if_pos waveMem]
  rw [projectionRead]
  exact stacked_initial_capped_energy_le order ceiling nonnegative (wholeRestartModes radius)

end
end SaturationMonoid.NavierStokes.NativeFullOrderInitial
