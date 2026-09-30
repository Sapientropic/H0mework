import H0mework.NavierStokes.WindowEnergyPreparation.Write
import H0mework.NavierStokes.WindowStressHeat.Balance

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowStressPreparationAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativePhysicalFourier NativeForwardWindowPairingReadout
open NativeWindowStressHeatTime (field jet)
open NativeWindowStressHeatBalance (basis viscousRead heatPair rawHeat)
open NativeWindowStressPreparationField (read fullRate)
open NativeWindowStressPreparationWrite (fullPairRate)
noncomputable section
variable {nu : Viscosity}

private theorem read_sum (F : Finset IntegerWavevector) (coordinate : Coordinate) (state : WholeRestartVelocityEndpointState) :
    read F coordinate state = ∑ wave ∈ F, basis wave (NativeWindowStressPreparationField.row wave coordinate state) := by
  simp only [NativeWindowStressPreparationField.read,basis,ContinuousLinearMap.comp_apply,sum_apply,map_sum]

private theorem row_viscous (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeWindowStressPreparationField.row wave coordinate (viscousCLM nu value) =
      (nu.coeff*integerWaveViscousMultiplier wave) • wholeVelocity value wave coordinate := by
  change integerWaveNormSq wave^2 • wholeVelocity (viscousCLM nu value) wave coordinate = _
  by_cases zero : wave = 0
  · subst wave
    simp only [wholeVelocity_zero,Pi.zero_apply,smul_zero]
  · rw [wholeVelocity_nonzero _ ⟨wave,zero⟩ coordinate,viscousCLM_source nu value ⟨wave,zero⟩]
    change integerWaveNormSq wave^2 • ((integerWaveNormSq wave)⁻¹^2 •
      ((nu.coeff*integerWaveViscousMultiplier wave) • wholeVelocity value wave coordinate)) = _
    rw [smul_smul,← mul_pow,mul_inv_cancel₀ (integerWaveNormSq_pos zero).ne',one_pow,one_smul]

theorem read_viscous (F : Finset IntegerWavevector) (coordinate : Coordinate) (value : FullSpace) :
    read F coordinate (viscousCLM nu value.fst) = -nu.coeff • viscousRead F coordinate value := by
  rw [read_sum]
  simp only [row_viscous,map_smul,viscousRead,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    Finset.smul_sum,smul_smul,neg_mul_neg]
  rfl

def actionRead (F : Finset IntegerWavevector) (coordinate : Coordinate) : FullSpace →L[ℝ] C(Torus,ℝ) :=
  (read F coordinate).comp (divergenceCLM.comp (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space))

theorem fullRate_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) (time : ℝ) : fullRate seed F coordinate time =
      actionRead F coordinate (NativeUnifiedCompleteSource.source seed time)+
        nu.coeff • viscousRead F coordinate (NativeUnifiedCompleteSource.source seed time) := by
  change read F coordinate (divergenceCLM (NativeUnifiedCompleteSource.source seed time).snd-
      viscousCLM nu (NativeUnifiedCompleteSource.source seed time).fst) = _
  rw [map_sub,read_viscous,neg_smul,sub_neg_eq_add]
  rfl

theorem action_original_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate) : ∀ᵐ time : ℝ, 0 < time →
      actionRead F coordinate (NativeUnifiedCompleteSource.source seed time) =
        NativeWindowStressHeatTime.fieldAction seed F coordinate time := by
  filter_upwards [NativeWindowStressPreparationField.fullRate_original_ae seed F coordinate,
    NativeWindowStressHeatBalance.rate_split_ae seed F coordinate] with time first last positive
  have same := (first positive).trans (last positive.le)
  rw [fullRate_split] at same
  exact add_right_cancel same

def nonlinearPair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  actionRead F output (NativeUnifiedCompleteSource.source seed time)*field seed F input time+
    field seed F output time*actionRead F input (NativeUnifiedCompleteSource.source seed time)

theorem fullPairRate_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : fullPairRate seed F output input time =
      nonlinearPair seed F output input time-heatPair seed F output input time := by
  ext point
  simp only [fullPairRate,fullRate_split,nonlinearPair,heatPair,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

theorem nonlinearPair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    Integrable (fun shift => nonlinearPair seed F output input (time-shift)) averageMeasure := by
  unfold nonlinearPair
  convert! Integrable.add (ε' := C(Torus,ℝ)) ?_ ?_ using 1
  · simpa only [NativeWindowStressHeatTime.field_original] using!
      NativeWindowStressHeatSource.product_integrable seed time (actionRead F output) (NativeWindowFiniteGramFourier.read F input)
  · simpa only [NativeWindowStressHeatTime.field_original] using!
      NativeWindowStressHeatSource.product_integrable seed time (NativeWindowFiniteGramFourier.read F output) (actionRead F input)

theorem heatPair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    Integrable (fun shift => heatPair seed F output input (time-shift)) averageMeasure := by
  simp only [heatPair,NativeWindowStressHeatTime.field_original]
  exact ((NativeWindowStressHeatSource.product_integrable seed time (viscousRead F output)
    (NativeWindowFiniteGramFourier.read F input)).add
    (NativeWindowStressHeatSource.product_integrable seed time (NativeWindowFiniteGramFourier.read F output)
      (viscousRead F input))).smul (-nu.coeff)

theorem heat_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) :
    (∫ shift, heatPair seed F output input (time-shift) ∂averageMeasure) = rawHeat seed time F output input := by
  simp only [heatPair,NativeWindowStressHeatTime.field_original]
  rw [integral_smul,integral_add
    (NativeWindowStressHeatSource.product_integrable seed time (viscousRead F output) (NativeWindowFiniteGramFourier.read F input))
    (NativeWindowStressHeatSource.product_integrable seed time (NativeWindowFiniteGramFourier.read F output) (viscousRead F input))]
  rfl

def nonlinearWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  -(∫ shift, nonlinearPair seed F output input (time-shift) ∂averageMeasure)

def correction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  NativeWindowPreparationWrite.fraction time • fullPairRate seed F output input 0

theorem jet_generator (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    -jet seed F output input 1 time = nonlinearWindow seed time F output input+
      NativeWindowStressHeatSource.heat seed time F output input+correction seed time F output input := by
  rw [NativeWindowStressPreparationWrite.jet_writer,← density_integral]
  simp only [fullPairRate_split]
  rw [integral_sub (nonlinearPair_integrable seed time F output input) (heatPair_integrable seed time F output input),
    heat_average,NativeWindowStressHeatBalance.rawHeat_original seed time F closed]
  simp only [nonlinearWindow,correction,fullPairRate_split]
  abel

theorem nonlinearWindow_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    nonlinearWindow seed time F output input = NativeWindowStressHeatBalance.nonlinearWindow seed time F output input := by
  have original := NativeWindowStressHeatBalance.jet_generator seed time nonnegative F closed output input
  rw [jet_generator seed time F closed,correction,NativeWindowPreparationWrite.fraction_after time (by linarith),
    zero_smul,add_zero] at original
  exact add_right_cancel original

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem action_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (coordinate : Coordinate)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    actionRead F coordinate (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance+time)) =
      actionRead F coordinate (NativeUnifiedCompleteSource.source response.1 time) := by
  rw [NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowStressPreparationAction
