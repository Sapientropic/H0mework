import H0mework.Versions.X.NavierStokes.HigherTreeOctic.ThetaGram

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticThetaTrace
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier NativeUnheatedTreeTime
open NativeUnheatedOcticThetaGram
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def diagonal (rest : ℝ) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) : ℝ :=
  kernel nu rest wave wave*vorticityRowAmplitude (wholeVelocity value) wave^2

theorem diagonal_nonnegative (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    0 ≤ diagonal (nu := nu) rest value wave :=
  mul_nonneg (NativeUnheatedOcticThetaGram.diagonal_nonnegative rest nonnegative wave) (sq_nonneg _)

theorem diagonal_bound (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    diagonal (nu := nu) rest value wave ≤ vorticityRowAmplitude (wholeVelocity value) wave^2 := by
  exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (kernel_bound rest nonnegative wave wave)) (sq_nonneg _)).trans_eq (one_mul _)

theorem diagonal_summable (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) :
    Summable (diagonal (nu := nu) rest value) :=
  (summable_vorticityRowAmplitude_sq (wholeVelocity value)).of_nonneg_of_le
    (diagonal_nonnegative rest nonnegative value) (diagonal_bound rest nonnegative value)

def trace (rest : ℝ) (value : WholeRestartVelocityEndpointState) : ℝ := ∑' wave, diagonal (nu := nu) rest value wave

theorem trace_bound (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) :
    trace (nu := nu) rest value ≤ ‖value‖^2 := by
  have paid := (diagonal_summable (nu := nu) rest nonnegative value).tsum_le_tsum (diagonal_bound rest nonnegative value)
    (summable_vorticityRowAmplitude_sq (wholeVelocity value))
  exact paid.trans_eq (wholeVelocity_mass value)

theorem trace_zero (value : WholeRestartVelocityEndpointState) : trace (nu := nu) 0 value = ‖value‖^2 := by
  rw [trace, ← wholeVelocity_mass value]
  apply tsum_congr
  intro wave
  by_cases zero : wave=0
  · simp [diagonal, zero, vorticityRowAmplitude_sq, wholeVelocity_zero,
      ThreeDimensionalVorticityCoefficientStretchingPairTable.complexCoordinateVectorNormSq]
  · have positive : 0 < rate nu wave := by
      have size := integerWaveNormSq_pos zero
      unfold rate integerWaveViscousMultiplier
      positivity [nu.coeff_pos]
    rw [diagonal, diagonal_formula]
    simp only [zero_add, div_self (show 2*rate nu wave ≠ 0 by positivity), one_mul]

def energyRow (rest : ℝ) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) (auxiliary : ℝ) : ℝ :=
  (∑ direction : Coordinate, feature nu rest wave direction auxiliary^2)*vorticityRowAmplitude (wholeVelocity value) wave^2

theorem energyRow_nonnegative (rest : ℝ) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) (auxiliary : ℝ) :
    0 ≤ energyRow (nu := nu) rest value wave auxiliary :=
  mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

theorem energyRow_integrable (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    Integrable (energyRow (nu := nu) rest value wave) (volume.restrict (Ioi 0)) := by
  change Integrable (fun auxiliary => energyRow (nu := nu) rest value wave auxiliary) (volume.restrict (Ioi 0))
  simpa only [energyRow, pow_two] using (gram_integrable (nu := nu) rest nonnegative wave wave).mul_const
    (vorticityRowAmplitude (wholeVelocity value) wave*vorticityRowAmplitude (wholeVelocity value) wave)

theorem energyRow_integral (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    (∫ auxiliary in Ioi (0 : ℝ), energyRow (nu := nu) rest value wave auxiliary) = diagonal (nu := nu) rest value wave := by
  unfold energyRow diagonal
  rw [integral_mul_const]
  congr 1
  simpa only [pow_two] using laplace_gram (nu := nu) rest nonnegative wave wave

theorem energy_norm_integrals (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) :
    Summable (fun wave => ∫ auxiliary in Ioi (0 : ℝ), ‖energyRow (nu := nu) rest value wave auxiliary‖) := by
  simp only [Real.norm_of_nonneg (energyRow_nonnegative rest value _ _), energyRow_integral rest nonnegative value]
  exact diagonal_summable rest nonnegative value

theorem energy_integrable (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) :
    Integrable (fun auxiliary => ∑' wave, energyRow (nu := nu) rest value wave auxiliary) (volume.restrict (Ioi 0)) := by
  refine ⟨(AEMeasurable.tsum fun wave => (energyRow_integrable rest nonnegative value wave).aemeasurable).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun wave => (energyRow_integrable rest nonnegative value wave).aemeasurable.enorm)]
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (energyRow_integrable rest nonnegative value _)]
  exact (energy_norm_integrals rest nonnegative value).tsum_ofReal_lt_top

theorem energy_integral (rest : ℝ) (nonnegative : 0 ≤ rest) (value : WholeRestartVelocityEndpointState) :
    (∫ auxiliary in Ioi (0 : ℝ), ∑' wave, energyRow (nu := nu) rest value wave auxiliary) = trace (nu := nu) rest value := by
  rw [← integral_tsum_of_summable_integral_norm (energyRow_integrable rest nonnegative value) (energy_norm_integrals rest nonnegative value)]
  simp only [energyRow_integral rest nonnegative value, trace]

def source (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (time : ℝ) : ℝ :=
  trace (nu := nu) (damping (nu := nu) nodes leaf) (NativeUnifiedCompleteSource.source seed time).fst

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (time : ℝ) :
    source seed nodes leaf time ≤ NativeUnifiedCompleteSource.budget seed^2 :=
  (trace_bound _ (damping_nonnegative nodes leaf) _).trans
    (pow_le_pow_left₀ (norm_nonneg _) (NativeUnheatedSourceWeightedTail.velocity_bound seed time) 2)

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (time : ℝ) :
    (∫ auxiliary in Ioi (0 : ℝ), ∑' wave, energyRow (nu := nu) (damping (nu := nu) nodes leaf)
      (NativeUnifiedCompleteSource.source seed time).fst wave auxiliary) = source seed nodes leaf time :=
  energy_integral _ (damping_nonnegative nodes leaf) _

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1))
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed nodes leaf (step.2.clockAdvance+time) = source step.1 nodes leaf time := by
  unfold source
  rw [NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticThetaTrace
