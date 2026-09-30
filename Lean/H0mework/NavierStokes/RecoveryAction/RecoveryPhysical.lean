import H0mework.NavierStokes.RecoveryAction.Recovery
import H0mework.NavierStokes.SourceAction.Synthesis
import H0mework.NavierStokes.SourceAction.ActionMoments
import H0mework.NavierStokes.VelocityEndpoint.PhysicalRightTrace

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryPhysical

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open NativeRecoveryControlProducer NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis
open NativePhysicalFourier NativePhysicalContinuous NativePhysicalSource NativeEndpointVelocityCarrier

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu : Viscosity}

theorem wholeMild_zero
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) : receipt.wholePath time 0 = 0 := by
  rw [receipt.wholePath_apply, velocityEndpointWholeMildState_apply,
    velocityEndpointWholeMildCoefficient_zero]

theorem wholeMild_transverse
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) : WholeStateTransverse (receipt.wholePath time) := by
  intro wave
  rw [receipt.wholePath_apply]
  have continuousDot : Continuous (fun row : ComplexCoordinateVector => complexWavevector wave ⬝ᵥ row) := by
    exact continuous_finsetSum _ fun coordinate _ => continuous_const.mul (continuous_apply coordinate)
  have source := continuousDot.tendsto _ |>.comp (endpoint_velocity_row_tendsto ledger receipt.core time wave)
  have generated index : complexWavevector wave ⬝ᵥ
      finiteStateVelocityCoefficient ((ledger.family.stage (receipt.core.subsequence index)).trajectory time.1) wave = 0 :=
    complexWavevector_dot_biotSavartVelocityCoefficient wave _
  exact tendsto_nhds_unique source
    (by simpa only [Function.comp_def, generated] using tendsto_const_nhds (x := (0 : ℂ)))

theorem wholeMild_reality
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) : FiniteStateFourierReality (receipt.wholePath time) := by
  intro wave
  rw [receipt.wholePath_apply]
  funext coordinate
  have source (frequency : IntegerWavevector) :=
    (continuous_apply coordinate).tendsto _ |>.comp
      (endpoint_velocity_row_tendsto ledger receipt.core time frequency)
  have generated index :
      finiteStateVelocityCoefficient ((ledger.family.stage (receipt.core.subsequence index)).trajectory time.1)
        (waveNeg wave) coordinate = star (finiteStateVelocityCoefficient
          ((ledger.family.stage (receipt.core.subsequence index)).trajectory time.1) wave coordinate) := by
    have reality := ((ledger.family.stage (receipt.core.subsequence index)).physical time.1 time.2).2.2.2
    change biotSavartVelocityCoefficient (waveNeg wave)
      ((ledger.family.stage (receipt.core.subsequence index)).trajectory time.1 (waveNeg wave)) coordinate = _
    rw [reality wave, biotSavartVelocityCoefficient_waveNeg_vectorConj]
    rfl
  exact tendsto_nhds_unique (source (waveNeg wave))
    ((source wave).star.congr' (Eventually.of_forall fun index => (generated index).symm))

theorem wholeVelocity_puncturedEuclideanize (velocity : ComplexVorticityHilbertState)
    (zero : velocity 0 = 0) : wholeVelocity (puncturedEuclideanize velocity) = velocity := by
  apply lp.ext
  funext wave
  by_cases atZero : wave = 0
  · subst wave
    simpa only [wholeVelocity_zero] using zero.symm
  · funext coordinate
    rw [wholeVelocity_nonzero _ ⟨wave, atZero⟩, puncturedEuclideanize_apply]
    rfl

theorem wholeMild_physical_identity
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    physicalCLM (puncturedEuclideanize (receipt.wholePath time)) = realField (receipt.wholePath time) ∧
      ‖realField (receipt.wholePath time)‖ ^ 2 = ‖puncturedEuclideanize (receipt.wholePath time)‖ ^ 2 ∧
      ‖realField (receipt.wholePath time)‖ ^ 2 ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 ∧
      ∀ coordinate wave, UnitAddTorus.mFourierCoeff
        (fun point => (realField (receipt.wholePath time) point coordinate : ℂ)) wave =
          receipt.wholePath time wave coordinate := by
  have actual := wholeVelocity_puncturedEuclideanize _ (wholeMild_zero ledger receipt time)
  have normSame := (realField_norm_sq _ (wholeMild_reality ledger receipt time)).trans
    ((congrArg wholeVorticityEuclideanMass actual).symm.trans (wholeVelocity_mass _))
  refine ⟨?_, normSame, ?_, realField_fourier _ (wholeMild_reality ledger receipt time)⟩
  · change realField (wholeVelocity (puncturedEuclideanize (receipt.wholePath time))) = _
    rw [actual]
  · rw [normSame, receipt.wholePath_apply]
    exact velocityEndpointWholeMildState_physical_norm_sq_le_endpoint receipt.core time

theorem velocityMomentDensity_eq_square (order : ℕ) (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : velocityMomentDensity order velocity wave =
      frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (velocity wave) := by
  simp only [velocityMomentDensity, ← pow_mul, Nat.mul_comm order 2,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

theorem square_moments (velocity : ComplexVorticityHilbertState)
    (paid : ∀ order, Summable (velocityMomentDensity order velocity)) (order : ℕ) :
    Summable fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (velocity wave) := by
  simpa only [← velocityMomentDensity_eq_square] using paid order

theorem amplitude_summable (velocity : ComplexVorticityHilbertState)
    (paid : ∀ order, Summable (velocityMomentDensity order velocity)) :
    Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave)) := by
  simpa only [pow_zero, one_mul, NativeFullOrderAction.amplitude, vorticityRowAmplitude,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
    summable_moment_of_square velocity 0 (square_moments velocity paid 2)

def spatialBudget (budget : ℕ → ℝ) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ((budget (order + 2) + ∑' wave, decay wave) / 2)

theorem spatial_control_of_moments (velocity : ComplexVorticityHilbertState)
    (paid : ∀ order, Summable (velocityMomentDensity order velocity))
    (budget : ℕ → ℝ) (bounded : ∀ order, (∑' wave, velocityMomentDensity order velocity wave) ≤ budget order) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField velocity) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (spatialField velocity) point‖ ≤ spatialBudget budget order := by
  refine ⟨spatialField_smooth_of_square velocity (square_moments velocity paid), ?_⟩
  intro order point
  apply (spatialField_bound_of_square velocity (square_moments velocity paid) order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2 * Real.pi) ^ order)
  apply div_le_div_of_nonneg_right _ (by norm_num : 0 ≤ (2 : ℝ))
  apply add_le_add _ le_rfl
  simpa only [velocityMomentDensity_eq_square] using bounded (order + 2)

theorem spatial_Lp_of_moments (velocity : ComplexVorticityHilbertState)
    (paid : ∀ order, Summable (velocityMomentDensity order velocity))
    (budget : ℕ → ℝ) (bounded : ∀ order, (∑' wave, velocityMomentDensity order velocity wave) ≤ budget order)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (spatialField velocity)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (spatialField velocity)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (spatialBudget budget order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have source := spatial_control_of_moments velocity paid budget bounded
  have continuous : Continuous (iteratedFDeriv ℝ order (spatialField velocity)) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) source.1
  have bound : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (spatialField velocity) point‖ ≤ spatialBudget budget order :=
    Eventually.of_forall (source.2 order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ bound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bound⟩

theorem spatial_word_eq_of_moments (velocity : ComplexVorticityHilbertState)
    (paid : ∀ order, Summable (velocityMomentDensity order velocity))
    (order : ℕ) (point : PhysicalSpace) (directions : Fin order → PhysicalSpace) :
    iteratedFDeriv ℝ order (spatialField velocity) point directions =
      ∑' wave, value velocity wave ((∏ index, phase wave (directions index)) •
        (Complex.I ^ order * UnitAddTorus.mFourier wave (circlePoint point))) :=
  spatialField_word_eq velocity
    (fun order => summable_moment_of_square velocity order (square_moments velocity paid (order + 2)))
    order point directions

theorem wholeMild_physical_controlled_subinterval
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLe : right ≤ 1) :
    ∃ first last : ℝ, ∃ budget : ℕ → ℝ,
      left < first ∧ first < last ∧ last < right ∧ ∀ time : Icc (0 : ℝ) 1,
        first ≤ time.1 → time.1 ≤ last →
        realField (receipt.wholePath time) =ᵐ[volume] continuousField (receipt.wholePath time) ∧
        (∀ coordinate wave, UnitAddTorus.mFourierCoeff
          (fun point => (continuousField (receipt.wholePath time) point coordinate : ℂ)) wave =
            receipt.wholePath time wave coordinate) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (receipt.wholePath time)) ∧
        ∀ order : ℕ,
          (∀ point, ‖iteratedFDeriv ℝ order (spatialField (receipt.wholePath time)) point‖ ≤ budget order) ∧
          (∀ exponent : ℝ≥0∞, ∀ domain : Set PhysicalSpace, IsCompact domain →
            MemLp (iteratedFDeriv ℝ order (spatialField (receipt.wholePath time))) exponent (volume.restrict domain) ∧
            eLpNorm (iteratedFDeriv ℝ order (spatialField (receipt.wholePath time))) exponent (volume.restrict domain) ≤
              ENNReal.ofReal (budget order) * volume domain ^ (1 / exponent.toReal)) ∧
          ∀ point directions, iteratedFDeriv ℝ order (spatialField (receipt.wholePath time)) point directions =
            ∑' wave, value (receipt.wholePath time) wave ((∏ index, phase wave (directions index)) •
              (Complex.I ^ order * UnitAddTorus.mFourier wave (circlePoint point))) := by
  obtain ⟨first, last, firstAfter, orderedWindow, lastBefore, controls⟩ :=
    wholeMild_controlled_subinterval ledger receipt left right leftNonnegative ordered rightLe
  choose budget controls using controls
  refine ⟨first, last, spatialBudget budget, firstAfter, orderedWindow, lastBefore, ?_⟩
  intro time afterFirst beforeLast
  have paid order := (controls order time afterFirst beforeLast).1
  have bound order := (controls order time afterFirst beforeLast).2
  have source := spatial_control_of_moments (receipt.wholePath time) paid budget bound
  refine ⟨continuousField_ae _ (amplitude_summable _ paid),
    continuousField_fourier _ (amplitude_summable _ paid) (wholeMild_reality ledger receipt time), source.1, ?_⟩
  intro order
  exact ⟨source.2 order,
    fun exponent _ compact => spatial_Lp_of_moments _ paid budget bound order exponent compact,
    spatial_word_eq_of_moments _ paid order⟩

theorem gradient_summable_of_moments (velocity : ComplexVorticityHilbertState)
    (paid : ∀ order, Summable (velocityMomentDensity order velocity)) :
    Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (velocity wave) := by
  apply (square_moments velocity paid 1).of_nonneg_of_le
  · intro wave
    exact mul_nonneg (integerWaveNormSq_nonneg wave) (complexCoordinateAmplitudeSq_nonneg _)
  · intro wave
    exact mul_le_mul_of_nonneg_right (normSq_le_frequencySize_sq wave) (complexCoordinateAmplitudeSq_nonneg _)

theorem curl_moment_density_le (velocity : ComplexVorticityHilbertState)
    (gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (velocity wave))
    (order : ℕ) (wave : IntegerWavevector) :
    velocityMomentDensity order (wholeVelocityCurlState velocity gradient) wave ≤
      (2 * Real.pi) ^ 2 * velocityMomentDensity (order + 1) velocity wave := by
  have bound := NativeFullOrderActionMoments.curl_amplitude_le wave (velocity wave)
  have frequencyBound := mul_le_mul_of_nonneg_left (normSq_le_frequencySize_sq wave) (sq_nonneg (2 * Real.pi))
  have amplitudeBound := bound.trans (mul_le_mul_of_nonneg_right frequencyBound (complexCoordinateAmplitudeSq_nonneg _))
  rw [velocityMomentDensity_eq_square, wholeVelocityCurlState_apply]
  apply (mul_le_mul_of_nonneg_left amplitudeBound (pow_nonneg (frequencySize_nonneg wave) _)).trans_eq
  rw [velocityMomentDensity_eq_square, Nat.mul_add, Nat.mul_one, pow_add]
  ring

theorem curl_moment_control (velocity : ComplexVorticityHilbertState)
    (gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (velocity wave))
    (paid : ∀ order, Summable (velocityMomentDensity order velocity))
    (budget : ℕ → ℝ) (bounded : ∀ order, (∑' wave, velocityMomentDensity order velocity wave) ≤ budget order)
    (order : ℕ) :
    Summable (velocityMomentDensity order (wholeVelocityCurlState velocity gradient)) ∧
      (∑' wave, velocityMomentDensity order (wholeVelocityCurlState velocity gradient) wave) ≤
        (2 * Real.pi) ^ 2 * budget (order + 1) := by
  have upper := (paid (order + 1)).mul_left ((2 * Real.pi) ^ 2)
  have generated := upper.of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg (frequencySize wave ^ order)) (complexCoordinateVectorNormSq_nonneg _))
    (curl_moment_density_le velocity gradient order)
  refine ⟨generated, ?_⟩
  have bound := generated.tsum_le_tsum (curl_moment_density_le velocity gradient order) upper
  rw [tsum_mul_left] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (bounded (order + 1)) (sq_nonneg _))

theorem wholeMild_curl_identity
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (receipt.wholePath time wave)) :
    wholeBiotSavartVelocityState (wholeVelocityCurlState (receipt.wholePath time) gradient) = receipt.wholePath time ∧
      physicalCLM (puncturedWholeVelocityEuclideanState (wholeVelocityCurlState (receipt.wholePath time) gradient)) =
        realField (receipt.wholePath time) := by
  have rows : wholeBiotSavartVelocityState (wholeVelocityCurlState (receipt.wholePath time) gradient) =
      receipt.wholePath time := by
    apply lp.ext
    funext wave
    exact biotSavart_wholeVelocityCurlState _ gradient (wholeMild_zero ledger receipt time)
      (wholeMild_transverse ledger receipt time) wave
  refine ⟨rows, ?_⟩
  change realField (wholeVelocity (puncturedWholeVelocityEuclideanState
    (wholeVelocityCurlState (receipt.wholePath time) gradient))) = _
  rw [wholeVelocity_punctured, rows]

theorem wholeMild_vorticity_controlled_subinterval
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left < right) (rightLe : right ≤ 1) :
    ∃ first last : ℝ, ∃ budget : ℕ → ℝ,
      left < first ∧ first < last ∧ last < right ∧ ∀ time : Icc (0 : ℝ) 1,
        first ≤ time.1 → time.1 ≤ last →
        ∃ gradient : Summable fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (receipt.wholePath time wave),
          let vorticity := wholeVelocityCurlState (receipt.wholePath time) gradient
          wholeBiotSavartVelocityState vorticity = receipt.wholePath time ∧
          realField vorticity =ᵐ[volume] continuousField vorticity ∧
          (∀ coordinate wave, UnitAddTorus.mFourierCoeff
            (fun point => (continuousField vorticity point coordinate : ℂ)) wave =
              fourierCurlCoefficient wave (receipt.wholePath time wave) coordinate) ∧
          ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField vorticity) ∧
          ∀ order : ℕ,
            (∀ point, ‖iteratedFDeriv ℝ order (spatialField vorticity) point‖ ≤ budget order) ∧
            ∀ exponent : ℝ≥0∞, ∀ domain : Set PhysicalSpace, IsCompact domain →
              MemLp (iteratedFDeriv ℝ order (spatialField vorticity)) exponent (volume.restrict domain) ∧
              eLpNorm (iteratedFDeriv ℝ order (spatialField vorticity)) exponent (volume.restrict domain) ≤
                ENNReal.ofReal (budget order) * volume domain ^ (1 / exponent.toReal) := by
  obtain ⟨first, last, firstAfter, orderedWindow, lastBefore, controls⟩ :=
    wholeMild_controlled_subinterval ledger receipt left right leftNonnegative ordered rightLe
  choose budget controls using controls
  let curlBudget := fun order => (2 * Real.pi) ^ 2 * budget (order + 1)
  refine ⟨first, last, spatialBudget curlBudget, firstAfter, orderedWindow, lastBefore, ?_⟩
  intro time afterFirst beforeLast
  have paid order := (controls order time afterFirst beforeLast).1
  have bound order := (controls order time afterFirst beforeLast).2
  have gradient := gradient_summable_of_moments _ paid
  have curlPaid order := (curl_moment_control _ gradient paid budget bound order).1
  have curlBound order := (curl_moment_control _ gradient paid budget bound order).2
  have source := spatial_control_of_moments _ curlPaid curlBudget curlBound
  have reality := wholeVelocityCurlState_reality _ gradient (wholeMild_reality ledger receipt time)
  refine ⟨gradient, (wholeMild_curl_identity ledger receipt time gradient).1,
    continuousField_ae _ (amplitude_summable _ curlPaid), ?_, source.1, ?_⟩
  · intro coordinate wave
    exact continuousField_fourier _ (amplitude_summable _ curlPaid) reality coordinate wave
  · intro order
    exact ⟨source.2 order,
      fun exponent _ compact => spatial_Lp_of_moments _ curlPaid curlBudget curlBound order exponent compact⟩

end
end SaturationMonoid.NavierStokes.NativeRecoveryPhysical
