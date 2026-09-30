import H0mework.Versions.X.NavierStokes.WindowSourceGreen.CompleteDensityCoefficient
import H0mework.Versions.X.NavierStokes.WindowStressHeat.Fourier
import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Window

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowFiniteDensityCoefficient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressCarrier NativePhysicalFourier NativePhysicalGradient
open NativeForwardWindowPairingReadout NativeWindowFiniteStressConvergence NativeWindowFiniteStressUniform
open NativeWindowSobolevStress (quarter quarter_positive)
noncomputable section
variable {nu : Viscosity}

def coefficient (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ)
    (direction : Coordinate) : ScalarSequence :=
  NativeWindowCompleteDensityCoefficient.coefficientMap direction (window seed radius order time)

theorem finite_integrable (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    Integrable (fun shift => NativeUnheatedWindowStress.finiteStress seed F (time-shift)) averageMeasure := by
  exact Integrable.of_bound ((NativeUnheatedWindowStress.finiteStress_continuous seed F).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable _
      (Eventually.of_forall fun shift => NativeUnheatedWindowStress.finiteStress_bound seed F (time-shift))

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem window_zero_row (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    window seed radius 0 time wave (output,input) = -(quarter wave : ℂ)*UnitAddTorus.mFourierCoeff
      (fun point => (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) output input point : ℂ)) wave := by
  let F := integerWaveFrequencyCube radius
  let observed := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate × Coordinate => ℂ) (output,input)
  have original (shift : ℝ) : quarter wave • tensor (read (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) wave) =
      weightedRead wave (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) := by
    ext entry
    change quarter wave • ((weight wave)⁻¹ • NativeUnheatedWindowStress.finiteStress seed F (time-shift) wave entry) =
      (quarter wave*(weight wave)⁻¹) • NativeUnheatedWindowStress.finiteStress seed F (time-shift) wave entry
    exact (mul_smul _ _ _).symm
  have paid : Integrable (fun shift => quarter wave • tensor
      (read (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) wave)) averageMeasure := by
    simpa only [original] using (weightedRead wave).integrable_comp (finite_integrable seed F time)
  change observed (window seed radius 0 time wave) = _
  rw [window_row seed radius 0 time nonnegative wave]
  simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero]
  rw [← density_integral,← observed.integral_comp_comm paid]
  change (∫ shift, quarter wave • read (NativeUnheatedWindowStress.finiteStress seed F (time-shift)) wave output input ∂averageMeasure) = _
  rw [integral_smul,NativeWindowFiniteGramFourier.stress_fourier seed time F
    (NativeWindowFiniteGramFourier.cube_closed radius) output input wave]
  simp only [Complex.real_smul,neg_mul_neg]

theorem physical_row (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (direction : Coordinate) (wave : IntegerWavevector) :
    (quarter wave : ℂ)*coefficient seed radius 0 time direction wave = multiplier wave direction*
      (NativePairedCurrentFourier.baseline wave+(∑ i : Coordinate, UnitAddTorus.mFourierCoeff
        (fun point => (NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube radius) i i point : ℂ)) wave)/8) := by
  rw [coefficient,NativeWindowCompleteDensityCoefficient.coefficientMap_row]
  simp only [window_zero_row seed radius time nonnegative wave,← Finset.mul_sum]
  rw [mul_add,NativeWindowCompleteDensityCoefficient.baseline_derivative,zero_add]
  have positive : (quarter wave : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (quarter_positive wave).ne'
  unfold NativeWindowCompleteDensityCoefficient.factor
  field_simp

end
end SaturationMonoid.NavierStokes.NativeWindowFiniteDensityCoefficient
