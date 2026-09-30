import H0mework.NavierStokes.WindowPhysics.SpacetimeVelocity
import H0mework.NavierStokes.WindowPhysics.SpacetimeFourierProduct

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeViewPhysicalTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium NativeTimeJetCarrier
open NativeEndpointVelocityCarrier NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier
open NativeWindowSpacetimeVelocity
noncomputable section
variable {nu : Viscosity}

def scalarWord (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (coordinate : Coordinate)
    (order : ℕ) (pair : Spacetime) : ℂ :=
  ∑' wave, coefficient seed lag coordinate order wave pair.1 * monomial wave pair.2

theorem scalarWord_mode_bound (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (order : ℕ) (wave : IntegerWavevector) (pair : Spacetime) :
    ‖coefficient seed lag coordinate order wave pair.1 * monomial wave pair.2‖ ≤
      coefficientBudget seed lag order 0 * decay wave := by
  rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) (NativeWindowFourierProduct.monomial_norm_le wave pair.2)).trans
  simpa only [pow_zero, one_mul] using coefficient_decay seed lag positive coordinate order 0 wave pair.1

theorem scalarWord_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (order : ℕ) (pair : Spacetime) :
    Summable (fun wave => coefficient seed lag coordinate order wave pair.1 * monomial wave pair.2) :=
  (decay_summable.mul_left (coefficientBudget seed lag order 0)).of_norm_bounded
    (fun wave => scalarWord_mode_bound seed lag positive coordinate order wave pair)

theorem scalarWord_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (order : ℕ) (time : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => scalarWord seed lag coordinate order (sample, space))
      (scalarWord seed lag coordinate (order + 1) (time, space)) time := by
  exact hasDerivAt_tsum (decay_summable.mul_left (coefficientBudget seed lag (order + 1) 0))
    (fun wave sample => (coefficient_hasDerivAt seed lag coordinate order wave sample).mul_const (monomial wave space))
    (fun wave sample => scalarWord_mode_bound seed lag positive coordinate (order + 1) wave (sample, space))
    (scalarWord_summable seed lag positive coordinate order (0, space)) time

theorem scalarWord_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (order : ℕ) : ContDiff ℝ ∞ (scalarWord seed lag coordinate order) := by
  let shifted := fun rank wave time => NativeWindowSpacetimeVelocity.coefficient seed lag coordinate (order + rank) wave time
  have evolves : ∀ rank wave time, HasDerivAt (shifted rank wave) (shifted (rank + 1) wave time) time := by
    intro rank wave time
    simpa only [shifted, Nat.add_assoc] using
      (NativeWindowSpacetimeVelocity.coefficient_hasDerivAt seed lag coordinate (order + rank) wave time)
  exact NativeWindowSpacetimeFourier.scalarField_smooth shifted evolves
    (fun rank spatial => coefficientBudget seed lag (order + rank) spatial)
    (fun rank spatial wave time => coefficient_decay seed lag positive coordinate (order + rank) spatial wave time)

def velocityWord (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (pair : Spacetime) : PhysicalSpace :=
  spatialField (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order pair.1)) pair.2

theorem velocityWord_zero (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) :
    velocityWord seed lag 0 = NativeWindowSpacetimeVelocity.jointField seed lag := rfl

theorem velocityWord_coordinate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (order : ℕ) (pair : Spacetime) :
    velocityWord seed lag order pair coordinate = (scalarWord seed lag coordinate order pair).re := by
  have paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order pair.1) wave)) := by
    change Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq
      (wholeVelocity (NativeUnifiedHeatAction.heatCLM nu lag (NativeForwardWindowJets.jet seed order pair.1).fst) wave))
    have moments := NativeHeatSpatialSynthesis.velocity_square_summable nu lag positive
      (NativeForwardWindowJets.jet seed order pair.1).fst 2
    simpa only [pow_zero, one_mul, amplitude, vorticityRowAmplitude,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using summable_moment_of_square _ 0 moments
  have written := (ContinuousMap.evalCLM ℂ (circlePoint pair.2)).hasSum
    (NativePhysicalContinuous.scalarSummable
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order pair.1)) coordinate paid).hasSum
  change HasSum (fun wave => coefficient seed lag coordinate order wave pair.1 * monomial wave pair.2)
    (NativePhysicalContinuous.scalarContinuous
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order pair.1)) coordinate (circlePoint pair.2)) at written
  exact (congrArg Complex.re written.tsum_eq).symm

theorem velocityWord_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => velocityWord seed lag order (sample, space))
      (velocityWord seed lag (order + 1) (time, space)) time := by
  have coordinates : HasDerivAt (fun sample => fun coordinate => (scalarWord seed lag coordinate order (sample, space)).re)
      (fun coordinate => (scalarWord seed lag coordinate (order + 1) (time, space)).re) time :=
    hasDerivAt_pi.mpr fun coordinate => Complex.reCLM.hasFDerivAt.comp_hasDerivAt time
      (scalarWord_hasDerivAt seed lag positive coordinate order time space)
  have generated := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    time coordinates
  convert! generated using 1
  · funext sample
    apply PiLp.ext
    exact fun coordinate => velocityWord_coordinate seed lag positive coordinate order (sample, space)
  · apply PiLp.ext
    exact fun coordinate => velocityWord_coordinate seed lag positive coordinate (order + 1) (time, space)

theorem velocityWord_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) : ContDiff ℝ ∞ (velocityWord seed lag order) := by
  have same : velocityWord seed lag order = fun pair => WithLp.toLp 2
      (fun coordinate => (scalarWord seed lag coordinate order pair).re) := by
    funext pair
    apply PiLp.ext
    exact fun coordinate => velocityWord_coordinate seed lag positive coordinate order pair
  rw [same]
  apply PiLp.contDiff_toLp.comp
  exact contDiff_pi.mpr fun coordinate => Complex.reCLM.contDiff.comp (scalarWord_smooth seed lag positive coordinate order)

theorem velocityWord_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (word order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (velocityWord seed lag word)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (velocityWord seed lag word)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (velocityWord_smooth seed lag positive word) order exponent compact

theorem velocity_gradient_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) :
    Summable (fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order time) wave)) := by
  have paid := NativeHeatSpatialSynthesis.velocity_square_summable nu lag positive
    (NativeForwardWindowJets.jet seed order time).fst 1
  apply paid.of_nonneg_of_le
    (fun wave => mul_nonneg (integerWaveNormSq_nonneg wave) (complexCoordinateAmplitudeSq_nonneg _))
  intro wave
  simpa only [mul_one] using! mul_le_mul_of_nonneg_right (normSq_le_frequencySize_sq wave)
    (complexCoordinateAmplitudeSq_nonneg (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order time) wave))

theorem momentum_row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) (valid : -1 < time)
    (wave : IntegerWavevector) :
    wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag 1 time) wave =
      NativeCompleteAction.momentum nu (NativeWindowHeatEvolution.source seed lag time) wave := by
  have original := NativeWindowHeatEvolution.source_physical_word seed lag 0 time valid
  simp only [Nat.zero_add, NativeWindowHeatEvolution.jet_zero] at original
  by_cases zero : wave = 0
  · subst wave
    simp only [NativeCompleteAction.momentum, NativeCompleteAction.velocity, wholeVelocity_zero, smul_zero, sub_zero]
    rw [NativeTimeJetCarrier.projectedDivergenceCLM_apply]
    have vanished : nativeFluidStressDivergenceCoefficient
        (fun _ => NativeCompleteAction.stress (NativeWindowHeatEvolution.source seed lag time) 0) 0 = 0 := by
      funext coordinate
      simp [nativeFluidStressDivergenceCoefficient, complexWavevector]
    rw [vanished]
    simp [transverseProjection]
  · have row := congrArg (fun value => integerWaveNormSq wave ^ 2 • value (⟨wave, zero⟩ : NonzeroIntegerWavevector)) original
    have decoded : NativeWindowHeatEvolution.velocityJet seed lag 1 time ⟨wave, zero⟩ =
        euclideanCoordinateRow (NativeCompleteAction.momentum nu (NativeWindowHeatEvolution.source seed lag time) wave) := by
      have reconstruction := NativeNegativeFourMomentum.embed_reconstruct
        (NativeWindowHeatEvolution.velocityJet seed lag 1 time) ⟨wave, zero⟩
      have forcing := NativeCompleteFilteredWrite.decode_weighted_row ⟨wave, zero⟩
        (NativeCompleteAction.momentum nu (NativeWindowHeatEvolution.source seed lag time) wave)
      have actual := NativeCompleteActionOperator.momentum_complete_row nu
        (NativeWindowHeatEvolution.source seed lag time) ⟨wave, zero⟩
      exact reconstruction.symm.trans (row.trans ((congrArg (fun value : ComplexCoordinateEuclidean =>
        integerWaveNormSq wave ^ 2 • value) actual).trans forcing))
    funext coordinate
    have evaluated := congrArg (fun value : ComplexCoordinateEuclidean => value coordinate) decoded
    rw [wholeVelocity_nonzero _ ⟨wave, zero⟩]
    exact evaluated

end
end SaturationMonoid.NavierStokes.NativeViewPhysicalTime
