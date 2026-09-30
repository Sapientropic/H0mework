import H0mework.NavierStokes.WholeReceipt.PrefixRows
import H0mework.NavierStokes.WholeReceipt.PrefixTangent

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholePrefixReceipt

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open WholePrefixState WholePrefixTangent

noncomputable section

variable {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (length : Nat)

def rawNonlinear (wave : IntegerWavevector) (actual : Real) : ComplexCoordinateVector :=
  wholeStateVorticityNonlinearCoefficientAt
    (wholeRestartPrefixPhysicalTrajectory initial (length + 1) actual) wave

theorem rawNonlinear_integrable (wave : IntegerWavevector) :
    IntervalIntegrable (rawNonlinear initial length wave) volume 0 (duration initial length) := by
  have source := wholeRestartPrefix_physicalWeakRows_intervalIntegrable initial (length + 1)
    (show (0 : Real) ≤ 0 from le_rfl) (duration_pos initial length).le le_rfl
    wave (fun _ => 1) contDiff_const
  change IntervalIntegrable (fun actual => wholeStateVorticityNonlinearCoefficientAt
    (wholeRestartPrefixPhysicalTrajectory initial (length + 1) actual) wave)
    volume 0 (duration initial length)
  simpa only [one_smul] using source.2.1

def extension (wave : IntegerWavevector) : Real → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath (initial.initialState wave) (rawNonlinear initial length wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0

theorem extension_on_interval (wave : IntegerWavevector) (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) (duration initial length)) :
    extension initial length wave time.1 = wholePath initial length time wave :=
  WholePrefixRows.heatPath_eq initial (length + 1) wave waveNe time.2.1 time.2.2

theorem extension_absolutelyContinuous (wave : IntegerWavevector) :
    AbsolutelyContinuousOnInterval (extension initial length wave) 0 (duration initial length) :=
  heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval (initial.initialState wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0
    (rawNonlinear_integrable initial length wave) (by simp)

theorem extension_ae_hasDerivAt (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    ∀ᵐ actual : Real, actual ∈ uIcc (0 : Real) (duration initial length) →
      HasDerivAt (extension initial length wave)
        (commonTimeZeroExtension (duration initial length)
          (rowTangent initial length wave) actual) actual := by
  have source := heatDuhamelComplexCoordinatePath_ae_hasDerivAt (initial.initialState wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0
    (rawNonlinear_integrable initial length wave) (by simp)
  filter_upwards [source] with actual derivative
  intro mem
  have inInterval : actual ∈ Icc (0 : Real) (duration initial length) := by
    simpa only [uIcc_of_le (duration_pos initial length).le] using mem
  have actualDerivative := derivative mem
  change HasDerivAt (extension initial length wave)
    (rawNonlinear initial length wave actual -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        extension initial length wave actual) actual at actualDerivative
  rw [extension_on_interval initial length wave waveNe ⟨actual, inInterval⟩] at actualDerivative
  rw [commonTimeZeroExtension_of_mem (duration initial length)
    (rowTangent initial length wave) actual inInterval]
  exact actualDerivative

theorem wave_mild (wave : IntegerWavevector) (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) (duration initial length)) :
    wholePath initial length time wave =
      fixedWaveHeatDuhamelValue (duration initial length) nu.coeff wave
        (initial.initialState wave) (transverseSpaceTimeNonlinearRow
          (transverseLimit initial length) wave) time := by
  have converted := commonTime_integral_Iic_eq_intervalIntegral (duration initial length)
    (duration_pos initial length).le time
    (fun earlier => finiteStateVorticityHeatMultiplier nu.coeff (time.1 - earlier) wave •
      rawNonlinear initial length wave earlier)
  have integralEq :
      (∫ earlier in (0 : Real)..time.1,
        finiteStateVorticityHeatMultiplier nu.coeff (time.1 - earlier) wave •
          rawNonlinear initial length wave earlier) =
      ∫ earlier in Iic time,
        finiteStateVorticityHeatMultiplier nu.coeff (time.1 - earlier.1) wave •
          transverseSpaceTimeNonlinearRow (transverseLimit initial length) wave earlier
          ∂(commonTimeMeasure (duration initial length)) := by
    rw [← converted]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (transverseSpaceTimeNonlinearRow_coeFn (transverseLimit initial length) wave),
      ae_restrict_of_ae (transverse_eq_wholePath_ae initial length)] with earlier row same
    rw [row]
    unfold transverseSpaceTimeNonlinearRowFunction
    rw [same]
    rfl
  calc
    _ = extension initial length wave time.1 :=
      (extension_on_interval initial length wave waveNe time).symm
    _ = _ := by
      unfold extension
      rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral, fixedWaveHeatDuhamelValue]
      simpa only [finiteStateVorticityHeatMultiplier, sub_zero] using
        congrArg (fun value => finiteStateVorticityHeatMultiplier nu.coeff time.1 wave •
          initial.initialState wave + value) integralEq

/-- Compile the original finite source prefix on its cumulative physical interval. -/
def receipt : WholeContinuousMildSerrinReceipt nu initial.initialState (duration initial length) where
  requestedTimePos := duration_pos initial length
  stateLimit := stateLimit initial length
  transverseLimit := transverseLimit initial length
  stateLimit_eq_transverse := transverse_inclusion initial length
  wholePath := wholePath initial length
  wholePath_toLp_eq_stateLimit := rfl
  wholePath_initial := WholePrefixRows.initial_eq initial (length + 1)
  wholePath_zero_row time := wholeRestartPrefixPhysicalTrajectory_zero_row initial (length + 1) time.1
  transverse_fourierReality_ae := transverse_fourierReality_ae initial length
  gradient_summable := gradient_summable initial length
  wholeTangent := tangent initial length
  wholeTangent_eq_unforced_ae := tangent_eq_unforced_ae initial length
  rowExtension wave _ := extension initial length wave
  rowExtension_on_interval := extension_on_interval initial length
  rowTangent wave _ := rowTangent initial length wave
  rowTangent_eq_unforced_ae wave _ := rowTangent_eq_unforced_ae initial length wave
  rowTangent_eq_wholeTangent_ae := unweighted_row_ae initial length
  rowExtension_absolutelyContinuous wave _ := extension_absolutelyContinuous initial length wave
  rowExtension_ae_hasDerivAt := extension_ae_hasDerivAt initial length
  row_mild_identity := wave_mild initial length

theorem receipt_path (time : Icc (0 : Real) (duration initial length)) :
    (receipt initial length).wholePath time =
      wholeRestartPrefixPhysicalTrajectory initial (length + 1) time.1 := rfl

end
end SaturationMonoid.NavierStokes.WholePrefixReceipt
