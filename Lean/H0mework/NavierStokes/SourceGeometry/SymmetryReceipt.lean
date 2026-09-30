import H0mework.NavierStokes.SourceGeometry.SymmetryRows

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceEvenFrequency

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-- Translation by half of the first spatial period acts on the same complete
NS receipt, including its original nonlinear forcing and physical time. -/
def receiptShift {viscosity : Viscosity} {initial : ComplexVorticityHilbertState} {time : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt viscosity initial time) :
    WholeContinuousMildSerrinReceipt viscosity (shift initial) time where
  requestedTimePos := receipt.requestedTimePos
  stateLimit := timeShift time receipt.stateLimit
  transverseLimit := transverseTimeShift time receipt.transverseLimit
  stateLimit_eq_transverse := by rw [timeShift_inclusion, receipt.stateLimit_eq_transverse]
  wholePath := pathShift receipt.wholePath
  wholePath_toLp_eq_stateLimit := by rw [pathShift_toLp, receipt.wholePath_toLp_eq_stateLimit]
  wholePath_initial := congrArg shift receipt.wholePath_initial
  wholePath_zero_row := by
    intro actual
    simp only [pathShift_apply, shift_apply, receipt.wholePath_zero_row, smul_zero]
  transverse_fourierReality_ae := by
    filter_upwards [receipt.transverse_fourierReality_ae, transverseTimeShift_ae receipt.transverseLimit] with
      actual reality same
    rw [same]
    exact shift_reality reality
  gradient_summable := by simpa only [timeShift_gradient] using receipt.gradient_summable
  wholeTangent := timeShift time receipt.wholeTangent
  wholeTangent_eq_unforced_ae := by
    filter_upwards [receipt.wholeTangent_eq_unforced_ae, timeShift_ae receipt.wholeTangent,
      nonlinearFunction_shift receipt.transverseLimit, viscousFunction_shift viscosity.coeff receipt.stateLimit] with
      actual old tangent nonlinear viscous
    rw [tangent, old, nonlinear, viscous, map_sub]
  rowExtension := fun wave waveNe actual => phase wave • receipt.rowExtension wave waveNe actual
  rowExtension_on_interval := by
    intro wave waveNe actual
    simp only [receipt.rowExtension_on_interval, pathShift_apply, shift_apply]
  rowTangent := fun wave waveNe actual => phase wave • receipt.rowTangent wave waveNe actual
  rowTangent_eq_unforced_ae := by
    intro wave waveNe
    filter_upwards [receipt.rowTangent_eq_unforced_ae wave waveNe,
      transverseTimeShift_ae receipt.transverseLimit] with actual old same
    rw [old, same, shifted_nonlinear]
    simp only [pathShift_apply, shift_apply, smul_sub]
    congr 1
    exact smul_comm _ _ _
  rowTangent_eq_wholeTangent_ae := by
    intro wave waveNe
    filter_upwards [receipt.rowTangent_eq_wholeTangent_ae wave waveNe,
      timeShift_ae receipt.wholeTangent] with actual old same
    rw [same, shift_apply, smul_comm, old]
  rowExtension_absolutelyContinuous := fun wave waveNe =>
    (receipt.rowExtension_absolutelyContinuous wave waveNe).const_smul (phase wave)
  rowExtension_ae_hasDerivAt := by
    intro wave waveNe
    filter_upwards [receipt.rowExtension_ae_hasDerivAt wave waveNe] with actual old
    intro within
    simpa only [zeroExtension_shift, Pi.smul_apply] using! (old within).const_smul (phase wave)
  row_mild_identity := by
    intro wave waveNe actual
    simp only [pathShift_apply, shift_apply]
    rw [nonlinearRow_shift, mild_shift, receipt.row_mild_identity wave waveNe actual]

end
end SaturationMonoid.NavierStokes.SourceEvenFrequency
