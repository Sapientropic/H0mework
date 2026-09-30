import H0mework.NavierStokes.UnheatedWriterTriad.PrimitiveSource
import H0mework.NavierStokes.UnheatedWriterTriad.Window
import H0mework.NavierStokes.UnheatedWriterTriad.CubicRaw

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadChannelWrite
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTriadKernel NativeUnheatedTriadChannels NativeUnheatedStressPairEvolution
open NativeUnheatedTriadTime NativeUnheatedPairGlobalWindow
noncomputable section
variable {nu : Viscosity}

def normalizer (nu : Viscosity) (a b c : IntegerWavevector) (i j response : Coordinate) : ℂ :=
  ((decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹) • pressure (a+b) i j response

theorem zero_rate_pressure (a b c : IntegerWavevector) (i j response : Coordinate)
    (zero : triadDecay nu a b c = 0) : pressure (a+b) i j response = 0 := by
  have total : integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c = 0 :=
    (mul_eq_zero.mp zero).resolve_left nu.coeff_pos.ne'
  have outputZero : integerWaveViscousMultiplier (a+b) = 0 := by
    apply le_antisymm _ (multiplier_nonnegative (a+b))
    linarith [output_multiplier a b, multiplier_nonnegative c]
  have paid := pressure_bound (a+b) i j response
  rw [outputZero, Real.sqrt_zero] at paid
  exact norm_eq_zero.mp (le_antisymm paid (norm_nonneg _))

theorem normalizer_rate (a b c : IntegerWavevector) (i j response : Coordinate) :
    triadDecay nu a b c • normalizer nu a b c i j response =
      (decay nu (a+b) c)⁻¹ • pressure (a+b) i j response := by
  by_cases zero : triadDecay nu a b c = 0
  · simp only [normalizer, zero_rate_pressure a b c i j response zero, smul_zero]
  · rw [normalizer, smul_smul]
    congr 1
    field_simp

theorem primitive_normalizer (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    NativeUnheatedTriadPrimitiveSource.row seed wave i j response outside indices time =
      normalizer nu indices.2 (wave-indices.1-indices.2) indices.1 i j response *
        product seed (indices.2,i) (wave-indices.1-indices.2,j) (indices.1,outside) time := by
  rw [NativeUnheatedTriadPrimitiveSource.row_original]
  simp only [normalizer, Complex.real_smul]
  ring

theorem joint_normalizer (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    NativeUnheatedTriadSource.jointRow seed wave i j response outside indices time =
      normalizer nu indices.2 (wave-indices.1-indices.2) indices.1 i j response *
        forcing seed (indices.2,i) (wave-indices.1-indices.2,j) (indices.1,outside) time := by
  rw [NativeUnheatedTriadSource.jointRow_original]
  simp only [normalizer, Complex.real_smul]
  ring

theorem cubic_normalizer (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) :
    NativeUnheatedCubicRaw.rawRow seed wave i j response outside indices time =
      (triadDecay nu indices.2 (wave-indices.1-indices.2) indices.1 •
        normalizer nu indices.2 (wave-indices.1-indices.2) indices.1 i j response) *
        product seed (indices.2,i) (wave-indices.1-indices.2,j) (indices.1,outside) time := by
  rw [normalizer_rate]
  simp only [NativeUnheatedCubicRaw.rawRow, Complex.real_smul]
  ring

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (order : ℕ)
    (observation clockOrigin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    (∫ time in start..finish, kernelWeight order observation clockOrigin time •
      NativeUnheatedCubicRaw.rawRow seed wave i j response outside indices time) =
    (∫ time in start..finish, kernelWeight order observation clockOrigin time •
      NativeUnheatedTriadSource.jointRow seed wave i j response outside indices time) -
    (∫ time in start..finish, kernelWeight (order+1) observation clockOrigin time •
      NativeUnheatedTriadPrimitiveSource.row seed wave i j response outside indices time) -
    (kernelWeight order observation clockOrigin finish •
        NativeUnheatedTriadPrimitiveSource.row seed wave i j response outside indices finish -
      kernelWeight order observation clockOrigin start •
        NativeUnheatedTriadPrimitiveSource.row seed wave i j response outside indices start) := by
  have commute (scalar : ℂ) (f : ℝ → ℂ) (n : ℕ) :
      (∫ time in start..finish, kernelWeight n observation clockOrigin time • (scalar * f time)) =
        scalar * (∫ time in start..finish, kernelWeight n observation clockOrigin time • f time) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    simp only [Complex.real_smul]
    ring
  have written := NativeUnheatedTriadWindow.weighted_write seed (indices.2,i)
    (wave-indices.1-indices.2,j) (indices.1,outside) order observation clockOrigin start finish start0 finish0
  have scaled := congrArg (fun value : ℂ =>
    normalizer nu indices.2 (wave-indices.1-indices.2) indices.1 i j response * value) written
  simp_rw [cubic_normalizer, primitive_normalizer, joint_normalizer, commute]
  simp only [Complex.real_smul, sumRate, triadDecay, mul_sub] at scaled ⊢
  linear_combination scaled

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadChannelWrite
