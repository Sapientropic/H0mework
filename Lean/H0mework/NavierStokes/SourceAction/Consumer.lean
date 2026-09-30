import H0mework.NavierStokes.SourceAction.Synthesis
import H0mework.NavierStokes.SourceAction.Next
import H0mework.NavierStokes.PhysicalJets.Curl

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeFullOrderConsumer

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderNext NativeFullOrderCurl NativeFullOrderSynthesis
open NativePhysicalFourier NativePhysicalSource NativePhysicalContinuous

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def velocityJetBudget (order index : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ((runMomentBudget (order + 2) index + ∑' wave, decay wave) / 2)

def vorticityJetBudget (order index : ℕ) : ℝ :=
  (2 * Real.pi) ^ order *
    (((2 * Real.pi) ^ 2 * runMomentBudget (order + 3) index + ∑' wave, decay wave) / 2)

private theorem velocity_density_eq (state : ComplexVorticityHilbertState) (order : ℕ) :
    momentDensity order state = fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (wholeBiotSavartVelocityState state wave) := by
  funext wave
  simp only [momentDensity, wholeBiotSavartVelocityState_apply,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, ← pow_mul, Nat.mul_comm order 2]

private theorem velocity_square_regular (state : ComplexVorticityHilbertState) (paid : MomentRegular state) :
    ∀ order : ℕ, Summable fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (wholeBiotSavartVelocityState state wave) := by
  intro order
  rw [← velocity_density_eq]
  exact paid order

private theorem source_velocity_control (state : ComplexVorticityHilbertState) (index : ℕ)
    (paid : MomentRegular state) (budget : ∀ order, moment order state ≤ runMomentBudget order index) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (wholeBiotSavartVelocityState state)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (spatialField (wholeBiotSavartVelocityState state)) point‖ ≤
        velocityJetBudget order index := by
  have moments := velocity_square_regular state paid
  refine ⟨spatialField_smooth_of_square _ moments, ?_⟩
  intro order point
  apply (spatialField_bound_of_square _ moments order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply add_le_add _ le_rfl
  rw [← velocity_density_eq]
  exact budget (order + 2)

private theorem source_vorticity_moment (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (paid : MomentRegular state)
    (order : ℕ) :
    (Summable fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (state wave)) ∧
      (∑' wave, frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (state wave)) ≤
        (2 * Real.pi) ^ 2 * moment (order + 1) state := by
  have actual := vorticity_moments_of_velocity state zero transverse order (paid (order + 1))
  simpa only [moment, momentDensity, ← pow_mul, Nat.mul_comm order 2,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using actual

private theorem source_vorticity_control (state : ComplexVorticityHilbertState) (index : ℕ)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state)
    (paid : MomentRegular state) (budget : ∀ order, moment order state ≤ runMomentBudget order index) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField state) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (spatialField state) point‖ ≤ vorticityJetBudget order index := by
  have moments order := (source_vorticity_moment state zero transverse paid order).1
  refine ⟨spatialField_smooth_of_square state moments, ?_⟩
  intro order point
  apply (spatialField_bound_of_square state moments order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply add_le_add _ le_rfl
  apply (source_vorticity_moment state zero transverse paid (order + 2)).2.trans
  exact mul_le_mul_of_nonneg_left (budget (order + 3)) (sq_nonneg _)

theorem run_receipt_spatial_control (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    (ContDiff ℝ (↑(⊤ : ℕ∞))
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time))) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time))) point‖ ≤
          velocityJetBudget order index) ∧
    (ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField ((run stackedShortCurrent index).receipt.wholePath time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (spatialField ((run stackedShortCurrent index).receipt.wholePath time)) point‖ ≤
          vorticityJetBudget order index) := by
  have paid := run_receipt_momentRegular index time
  have budget order := (run_receipt_moment_control order index time).2
  refine ⟨source_velocity_control _ index paid budget, ?_⟩
  exact source_vorticity_control _ index
    ((run stackedShortCurrent index).receipt.wholePath_zero_row time)
    (wholePath_transverse _ time) paid budget

theorem run_nextReceipt_spatial_control (index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration (run stackedShortCurrent index).contact)) :
    (ContDiff ℝ (↑(⊤ : ℕ∞))
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).nextReceipt.wholePath time))) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).nextReceipt.wholePath time))) point‖ ≤
          velocityJetBudget order (index + 1)) ∧
    (ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField ((run stackedShortCurrent index).nextReceipt.wholePath time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (spatialField ((run stackedShortCurrent index).nextReceipt.wholePath time)) point‖ ≤
          vorticityJetBudget order (index + 1)) :=
  run_receipt_spatial_control (index + 1) time

private theorem compact_jet_Lp {field : PhysicalSpace → PhysicalSpace}
    (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) field) (order : ℕ) (bound : ℝ)
    (bounded : ∀ point, ‖iteratedFDeriv ℝ order field point‖ ≤ bound)
    (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuous : Continuous (iteratedFDeriv ℝ order field) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) smooth
  have aeBound : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order field point‖ ≤ bound :=
    Eventually.of_forall bounded
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable bound aeBound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) aeBound⟩

theorem run_receipt_spatial_Lp (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    (MemLp (iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time))))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time))))
        exponent (volume.restrict domain) ≤
          ENNReal.ofReal (velocityJetBudget order index) * volume domain ^ (1 / exponent.toReal)) ∧
    (MemLp (iteratedFDeriv ℝ order (spatialField ((run stackedShortCurrent index).receipt.wholePath time)))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (spatialField ((run stackedShortCurrent index).receipt.wholePath time)))
        exponent (volume.restrict domain) ≤
          ENNReal.ofReal (vorticityJetBudget order index) * volume domain ^ (1 / exponent.toReal)) := by
  have actual := run_receipt_spatial_control index time
  exact ⟨compact_jet_Lp actual.1.1 order _ (actual.1.2 order) exponent compact,
    compact_jet_Lp actual.2.1 order _ (actual.2.2 order) exponent compact⟩

theorem run_nextReceipt_spatial_Lp (index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration (run stackedShortCurrent index).contact))
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    (MemLp (iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).nextReceipt.wholePath time))))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order
        (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).nextReceipt.wholePath time))))
        exponent (volume.restrict domain) ≤
          ENNReal.ofReal (velocityJetBudget order (index + 1)) * volume domain ^ (1 / exponent.toReal)) ∧
    (MemLp (iteratedFDeriv ℝ order (spatialField ((run stackedShortCurrent index).nextReceipt.wholePath time)))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (spatialField ((run stackedShortCurrent index).nextReceipt.wholePath time)))
        exponent (volume.restrict domain) ≤
          ENNReal.ofReal (vorticityJetBudget order (index + 1)) * volume domain ^ (1 / exponent.toReal)) :=
  run_receipt_spatial_Lp (index + 1) time order exponent compact

theorem run_receipt_source_identity (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    (receiptField (run stackedShortCurrent index).receipt time =ᵐ[volume]
      continuousReceipt (run stackedShortCurrent index).receipt time) ∧
    (realField ((run stackedShortCurrent index).receipt.wholePath time) =ᵐ[volume]
      continuousField ((run stackedShortCurrent index).receipt.wholePath time)) ∧
    (∀ coordinate wave, UnitAddTorus.mFourierCoeff
      (fun point => (continuousReceipt (run stackedShortCurrent index).receipt time point coordinate : ℂ)) wave =
        biotSavartVelocityCoefficient wave ((run stackedShortCurrent index).receipt.wholePath time wave) coordinate) ∧
    (∀ coordinate wave, UnitAddTorus.mFourierCoeff
      (fun point => (continuousField ((run stackedShortCurrent index).receipt.wholePath time) point coordinate : ℂ)) wave =
        (run stackedShortCurrent index).receipt.wholePath time wave coordinate) := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have regular := run_receipt_momentRegular index time
  have velocityPaid : Summable (amplitude (wholeBiotSavartVelocityState state)) := by
    simpa only [pow_zero, one_mul] using summable_moment_of_square (wholeBiotSavartVelocityState state) 0
      (velocity_square_regular state regular 2)
  have vorticityPaid : Summable (amplitude state) := by
    simpa only [pow_zero, one_mul] using summable_moment_of_square state 0
      (source_vorticity_moment state ((run stackedShortCurrent index).receipt.wholePath_zero_row time)
        (wholePath_transverse _ time) regular 2).1
  refine ⟨continuousField_ae _ velocityPaid, continuousField_ae _ vorticityPaid, ?_, ?_⟩
  · intro coordinate wave
    exact continuousField_fourier _ velocityPaid
      (velocity_reality state (receipt_reality _ time)) coordinate wave
  · intro coordinate wave
    exact continuousField_fourier state vorticityPaid (receipt_reality _ time) coordinate wave

end
end SaturationMonoid.NavierStokes.NativeFullOrderConsumer
