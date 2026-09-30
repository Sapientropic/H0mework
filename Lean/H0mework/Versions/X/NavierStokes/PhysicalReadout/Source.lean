import H0mework.Versions.X.NavierStokes.PhysicalReadout.Fourier
import H0mework.NavierStokes.PhysicalReadout.EndpointVelocity
import H0mework.Versions.X.NavierStokes.CorrectionControl.Actual

set_option autoImplicit false
open scoped ENNReal BigOperators

namespace SaturationMonoid.NavierStokes.NativePhysicalSource

open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open NativePhysicalFourier NativeEndpointVelocityCarrier

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem receipt_reality {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : Icc (0 : ℝ) duration) :
    FiniteStateFourierReality (receipt.wholePath time) := by
  intro wave
  funext coordinate
  change receipt.wholePath time (waveNeg wave) coordinate = star (receipt.wholePath time wave coordinate)
  let row (frequency : IntegerWavevector) (actual : ℝ) : ℂ :=
    receipt.wholePath (projIcc (0 : ℝ) duration receipt.requestedTimePos.le actual) frequency coordinate
  have continuousRow (frequency : IntegerWavevector) : Continuous (row frequency) :=
    (continuous_apply coordinate).comp ((lp.evalCLM ℂ _ 2 frequency).continuous.comp
      (receipt.wholePath.continuous.comp continuous_projIcc))
  have subtypeEq : ∀ᵐ point ∂commonTimeMeasure duration,
      receipt.wholePath point (waveNeg wave) coordinate = star (receipt.wholePath point wave coordinate) := by
    filter_upwards [wholePath_fourierReality_ae receipt] with point reality
    exact congrFun (reality wave) coordinate
  have measureEq : commonTimeMeasure duration =
      Measure.comap (Subtype.val : Icc (0 : ℝ) duration → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  rw [measureEq] at subtypeEq
  have onInterval : ∀ᵐ actual ∂volume.restrict (Icc (0 : ℝ) duration),
      row (waveNeg wave) actual = star (row wave actual) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [subtypeEq] with point actual
    simpa only [row, projIcc_of_mem receipt.requestedTimePos.le point.2] using actual
  have equal := Measure.eqOn_Icc_of_ae_eq (μ := volume) receipt.requestedTimePos.ne onInterval
    (continuousRow (waveNeg wave)).continuousOn (continuousRow wave).star.continuousOn
  simpa only [row, projIcc_of_mem receipt.requestedTimePos.le time.2] using equal time.2

theorem velocity_reality (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) : FiniteStateFourierReality (wholeBiotSavartVelocityState state) := by
  intro wave
  change biotSavartVelocityCoefficient (waveNeg wave) (state (waveNeg wave)) =
    vectorConj (biotSavartVelocityCoefficient wave (state wave))
  rw [reality wave, biotSavartVelocityCoefficient_waveNeg_vectorConj]

/-- The same physical field constructor accepts original velocities, including weak endpoints. -/
def physicalCLM := realFieldCLM.comp wholeVelocityCLM

theorem physicalCLM_norm (velocity : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality velocity) :
    ‖physicalCLM velocity‖ = ‖velocity‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (realField_norm_sq (wholeVelocity velocity) (wholeVelocity_reality velocity reality)).trans
    (wholeVelocity_mass velocity)

def receiptField {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : Icc (0 : ℝ) duration) :=
  realField (wholeBiotSavartVelocityState (receipt.wholePath time))

theorem receiptField_eq_physicalCLM {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : Icc (0 : ℝ) duration) :
    receiptField receipt time = physicalCLM (puncturedWholeVelocityEuclideanState (receipt.wholePath time)) := by
  simp only [physicalCLM, ContinuousLinearMap.comp_apply, realFieldCLM, LinearMap.mkContinuous_apply,
    wholeVelocityCLM_apply, wholeVelocity_punctured]
  rfl

theorem receiptField_fourier {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : Icc (0 : ℝ) duration)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (receiptField receipt time point coordinate : ℂ)) wave =
      biotSavartVelocityCoefficient wave (receipt.wholePath time wave) coordinate :=
  realField_fourier _ (velocity_reality _ (receipt_reality receipt time)) coordinate wave

theorem receiptField_norm_le {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : Icc (0 : ℝ) duration) :
    ‖receiptField receipt time‖ ≤ ‖puncturedWholeVelocityEuclideanState initial‖ := by
  have normEq : ‖receiptField receipt time‖ =
      ‖puncturedWholeVelocityEuclideanState (receipt.wholePath time)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [puncturedWholeVelocityEuclideanState_norm_sq _ (wholePath_transverse receipt time)]
    exact (realField_norm_sq _ (velocity_reality _ (receipt_reality receipt time))).trans
      (wholeVorticityEuclideanMass_wholeBiotSavartVelocityState _ (wholePath_transverse receipt time))
  exact normEq.le.trans (NativeNormControl.receipt_velocity_norm_le receipt time)

end
end SaturationMonoid.NavierStokes.NativePhysicalSource
