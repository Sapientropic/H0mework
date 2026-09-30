import H0mework.NavierStokes.WindowSourcePreparation.Write
import H0mework.NavierStokes.SourcePairing.PhysicalHistoryInitialAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowPreparationForce
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeFullOrderSynthesis
open NativePhysicalHistoryInitialAction NativeReceiptTimeProfile NativeFullOrderFlux
noncomputable section

theorem initial_velocity : NativeOriginalMomentumIntegral.receiptVelocity (NativeWholeHistoryField.receipt 0) 0 =
    puncturedWholeVelocityEuclideanState stackedShortCurrent.initialState := by
  rw [NativeOriginalMomentumIntegral.receiptVelocity,
    projIcc_of_mem (NativeWholeHistoryField.receipt 0).requestedTimePos.le
      (show (0 : ℝ) ∈ Icc 0 (NativeWholeHistoryClock.duration 0) from
        ⟨le_rfl, (NativeWholeHistoryClock.duration_pos 0).le⟩),
    (NativeWholeHistoryField.receipt 0).wholePath_initial]

theorem momentum_original (wave : IntegerWavevector) :
    momentum wave = NativeOriginalMomentumIntegral.momentumAt butterflyGainViscosity
      (puncturedWholeVelocityEuclideanState stackedShortCurrent.initialState) wave := by
  rw [momentum_row]
  have actual := NativeOriginalMomentumIntegral.receipt_action (NativeWholeHistoryField.receipt 0) wave
    ⟨0, le_rfl, (NativeWholeHistoryClock.duration_pos 0).le⟩
  change NativeOriginalMomentumIntegral.momentumAt _
    (NativeOriginalMomentumIntegral.receiptVelocity (NativeWholeHistoryField.receipt 0) 0) wave = _ at actual
  rw [initial_velocity] at actual
  exact actual.symm

theorem full_initial_action (wave : NonzeroIntegerWavevector) :
    momentumCLM butterflyGainViscosity (NativeUnifiedCompleteSource.source stackedShortCurrent 0) wave =
      NativeNegativeFourMomentum.weightedRowCLM wave.1 (momentum wave.1) := by
  change momentumCLM butterflyGainViscosity (WithLp.toLp 2
    ((NativeUnifiedGlobalStressSource.source stackedShortCurrent 0).1,
      NativeCompleteStressCarrier.ofBound _ _ _)) wave = _
  rw [momentumCLM_source, NativeUnifiedGlobalStressSource.source_zero, momentum_original]
  rw [NativeUnifiedGlobalStressSource.stress, NativeUnifiedGlobalStressSource.source_zero]
  rfl

theorem square_moments (order : ℕ) : Summable (fun wave => NativeFullOrderAction.frequencySize wave ^ (2*order) *
    complexCoordinateAmplitudeSq (momentum wave)) := by
  convert (NativeReceiptSpacetime.timeJet_moment_control (NativeWholeHistoryField.window 0) 1 order 0).1 using 1
  funext wave
  simp only [momentum, velocityMomentDensity, ← pow_mul, Nat.mul_comm,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

def squareBudget (order : ℕ) : ℝ := ((factor (NativeWholeHistoryField.window 0))⁻¹) ^ 2 *
  (jets (NativeWholeHistoryField.window 0) 1).budget order

theorem square_bound (order : ℕ) :
    (∑' wave, NativeFullOrderAction.frequencySize wave ^ (2*order) * complexCoordinateAmplitudeSq (momentum wave)) ≤
      squareBudget order := by
  simpa only [momentum, velocityMomentDensity, squareBudget, pow_one, ← pow_mul, Nat.mul_comm,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
    (NativeReceiptSpacetime.timeJet_moment_control (NativeWholeHistoryField.window 0) 1 order 0).2

def field : PhysicalSpace → PhysicalSpace := spatialField momentum

theorem field_smooth : ContDiff ℝ ∞ field := spatialField_smooth_of_square momentum square_moments

def budget (order : ℕ) : ℝ := (2*Real.pi)^order * ((squareBudget (order+2)+∑' wave, decay wave)/2)

theorem derivative_bound (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order field point‖ ≤ budget order := by
  apply (spatialField_bound_of_square momentum square_moments order point).trans
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (add_le_add (square_bound (order+2)) le_rfl) (by norm_num)) (by positivity)

theorem field_actual_derivative (point : PhysicalSpace) :
    HasDerivWithinAt (fun time => NativePhysicalHistory.field
      (NativeFluidSpatialOperators.slice time point))
      (field point) (Ici (0 : ℝ)) 0 := field_hasDerivWithinAt point

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationForce
