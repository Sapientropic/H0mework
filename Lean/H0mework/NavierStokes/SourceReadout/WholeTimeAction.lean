import H0mework.NavierStokes.SourceReadout.TimeAction
import H0mework.NavierStokes.KineticRestart.KineticVelocityWholeCarrierMorphism
import H0mework.NavierStokes.EndpointTransport.CofinalNonlinearNegativeOneEuclideanBalance

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeWholeVelocityAction

open MeasureTheory Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open NativeStressSource

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}

/-- The original complete negative-one tangent read in the physical velocity Hilbert carrier. -/
def velocityTangentLp (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    Lp WholeRestartVelocityEndpointState 2 (commonTimeMeasure T) :=
  (wholeRestartKineticToVelocityCLM.compLpL 2 (commonTimeMeasure T))
    (puncturedEuclideanSpaceTimeState receipt.wholeTangent)

def velocityTangent (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ℝ → WholeRestartVelocityEndpointState :=
  commonTimeZeroExtension T (velocityTangentLp receipt)

theorem velocityTangent_intervalIntegrable (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    IntervalIntegrable (velocityTangent receipt) volume 0 T := by
  apply commonTimeZeroExtension_intervalIntegrable_of_integrable T receipt.requestedTimePos.le
  have onUniv := integrableOn_Lp_of_measure_ne_top (velocityTangentLp receipt)
    fact_one_le_two_ennreal.elim (measure_ne_top (commonTimeMeasure T) Set.univ)
  simpa only [integrableOn_univ] using onUniv

theorem velocityTangentLp_row (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure T), velocityTangentLp receipt time wave =
      euclideanCoordinateRow (biotSavartVelocityCoefficient wave.1
        (receipt.rowTangent wave.1 wave.2 time)) := by
  have mapped := wholeRestartKineticToVelocityCLM.coeFn_compLpL
    (puncturedEuclideanSpaceTimeState receipt.wholeTangent)
  filter_upwards [mapped, puncturedEuclideanSpaceTimeState_apply_ae receipt.wholeTangent,
    receipt.rowTangent_eq_wholeTangent_ae wave.1 wave.2] with time mappedEq euclideanEq tangentEq
  change ((wholeRestartKineticToVelocityCLM.compLpL 2 (commonTimeMeasure T))
    (puncturedEuclideanSpaceTimeState receipt.wholeTangent)) time wave = _
  rw [mappedEq, euclideanEq, wholeRestartKineticToVelocityCLM_apply,
    wholeRestartKineticToVelocityRowCLM_apply]
  change euclideanCoordinateRow (biotSavartVelocityCoefficient wave.1
    ((Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ) • receipt.wholeTangent time wave.1)) = _
  rw [tangentEq]

private theorem projectedPath_eq (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (time : Icc (0 : ℝ) T) :
    (actualWholeProjectedTransversePath receipt time.1).1 = receipt.wholePath time := by
  change receipt.wholePath (projIcc (0 : ℝ) T receipt.requestedTimePos.le time.1) = _
  rw [projIcc_of_mem receipt.requestedTimePos.le time.2]

theorem velocityTangentLp_momentum (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure T), velocityTangentLp receipt time wave =
      euclideanCoordinateRow (receiptMomentumAction receipt wave.1 time.1) := by
  filter_upwards [velocityTangentLp_row receipt wave,
    receipt.rowTangent_eq_unforced_ae wave.1 wave.2,
    receipt.wholePath_eq_transverse_ae] with time rowEq unforcedEq stateEq
  rw [rowEq, unforcedEq, ← stateEq, wholeStateVorticityBilinearCoefficientAt_self]
  rw [receiptMomentumAction, projectedPath_eq receipt time]
  rfl

private theorem momentum_integral_to_time (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (wave : NonzeroIntegerWavevector) (time : Icc (0 : ℝ) T) :
    (∫ actual in 0..time.1, receiptMomentumAction receipt wave.1 actual) =
      wholeBiotSavartVelocityState (receipt.wholePath time) wave.1 -
        wholeBiotSavartVelocityState initial wave.1 := by
  have derivative (actual : ℝ) (inside : actual ∈ uIcc (0 : ℝ) time.1) :
      HasDerivAt (receiptVelocityRow receipt wave.1)
        (receiptMomentumAction receipt wave.1 actual) actual := by
    have within : actual ∈ Icc (0 : ℝ) T := by
      rw [uIcc_of_le time.2.1] at inside
      exact ⟨inside.1, inside.2.trans time.2.2⟩
    have generated := (biotSavartVelocityCLM wave.1).hasFDerivAt.comp_hasDerivAt actual
      (receipt_vorticity_hasDerivAt receipt wave.1 wave.2 ⟨actual, within⟩)
    change HasDerivAt (receiptVelocityRow receipt wave.1)
      (biotSavartVelocityCoefficient wave.1 (wholeLatticeVorticityFourierTangentAt nu.coeff
        (receipt.wholePath ⟨actual, within⟩) wave.1)) actual at generated
    rw [receiptMomentumAction, projectedPath_eq receipt ⟨actual, within⟩]
    exact generated
  have update := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    ((receiptMomentumAction_continuous receipt wave.1).intervalIntegrable 0 time.1)
  rw [receiptVelocityRow_eq receipt wave.1 wave.2 time,
    receiptVelocityRow_eq receipt wave.1 wave.2 ⟨0, le_rfl, receipt.requestedTimePos.le⟩,
    receipt.wholePath_initial] at update
  exact update

/-- The whole Bochner impulse is the exact original velocity increment at every physical time. -/
theorem velocity_integral_write (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (time : Icc (0 : ℝ) T) :
    (∫ actual in 0..time.1, velocityTangent receipt actual) =
      puncturedWholeVelocityEuclideanState (receipt.wholePath time) -
        puncturedWholeVelocityEuclideanState initial := by
  have integrableAt : IntervalIntegrable (velocityTangent receipt) volume 0 time.1 :=
    (velocityTangent_intervalIntegrable receipt).mono_set (by
      rw [uIcc_of_le time.2.1, uIcc_of_le receipt.requestedTimePos.le]
      exact Icc_subset_Icc le_rfl time.2.2)
  apply lp.ext
  funext wave
  have evaluate := (lp.evalCLM ℂ
    (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
    |>.intervalIntegral_comp_comm integrableAt
  change (lp.evalCLM ℂ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
    (∫ actual in 0..time.1, velocityTangent receipt actual) = _
  rw [← evaluate]
  change (∫ actual in 0..time.1, velocityTangent receipt actual wave) = _
  have rowIntegral : (∫ actual in 0..time.1, velocityTangent receipt actual wave) =
      ∫ actual in 0..time.1, euclideanCoordinateRow (receiptMomentumAction receipt wave.1 actual) := by
    rw [← commonTime_integral_Iic_eq_intervalIntegral T receipt.requestedTimePos.le time,
      ← commonTime_integral_Iic_eq_intervalIntegral T receipt.requestedTimePos.le time]
    apply integral_congr_ae
    filter_upwards [ae_restrict_le (velocityTangentLp_momentum receipt wave)] with actual equality
    rw [velocityTangent, commonTimeZeroExtension_of_mem T _ actual.1 actual.2]
    exact equality
  rw [rowIntegral]
  have castIntegral : (∫ actual in 0..time.1,
      euclideanCoordinateRow (receiptMomentumAction receipt wave.1 actual)) =
      euclideanCoordinateRow (∫ actual in 0..time.1, receiptMomentumAction receipt wave.1 actual) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Coordinate => ℂ)).symm
      |>.toContinuousLinearMap.intervalIntegral_comp_comm
        ((receiptMomentumAction_continuous receipt wave.1).intervalIntegrable 0 time.1)
  change (∫ actual in 0..time.1, euclideanCoordinateRow (receiptMomentumAction receipt wave.1 actual)) =
    puncturedWholeVelocityEuclideanState (receipt.wholePath time) wave -
      puncturedWholeVelocityEuclideanState initial wave
  rw [castIntegral, momentum_integral_to_time receipt wave time]
  rfl

def velocityPrimitive (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ℝ → WholeRestartVelocityEndpointState := fun time =>
  puncturedWholeVelocityEuclideanState initial + ∫ earlier in 0..time, velocityTangent receipt earlier

theorem velocity_write (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (time : Icc (0 : ℝ) T) :
    puncturedWholeVelocityEuclideanState (receipt.wholePath time) = velocityPrimitive receipt time.1 := by
  rw [velocityPrimitive, velocity_integral_write receipt time]
  abel

/-- Its strong Banach-valued derivative is generated from the same original Bochner write. -/
theorem velocityPrimitive_ae_hasDerivAt (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ actual : ℝ, actual ∈ uIcc (0 : ℝ) T →
      HasDerivAt (velocityPrimitive receipt) (velocityTangent receipt actual) actual := by
  filter_upwards [(velocityTangent_intervalIntegrable receipt).ae_hasDerivAt_integral]
    with actual derivative
  intro inside
  have primitive := derivative inside 0 (by simp)
  change HasDerivAt
    (fun time => puncturedWholeVelocityEuclideanState initial +
      ∫ earlier in 0..time, velocityTangent receipt earlier)
    (velocityTangent receipt actual) actual
  exact primitive.const_add _

/-- The same compiler occurrence consumes the complete impulse and returns its literal next. -/
theorem occurrence_velocity_write (current : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    let occurrence := generatedWholeRestartNativeActualOccurrence current index
    (∫ actual in 0..occurrence.response.1.contact.time.1,
      velocityTangent (occurrenceReceipt occurrence) actual) =
      puncturedWholeVelocityEuclideanState occurrence.response.1.contact.physicalState -
        puncturedWholeVelocityEuclideanState (run current index).contact.physicalState := by
  let occurrence := generatedWholeRestartNativeActualOccurrence current index
  exact velocity_integral_write (occurrenceReceipt occurrence)
    ⟨_, (occurrenceReceipt occurrence).requestedTimePos.le, le_rfl⟩

end
end SaturationMonoid.NavierStokes.NativeWholeVelocityAction
