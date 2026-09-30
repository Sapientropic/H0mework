import H0mework.NavierStokes.SourceEstimates.WholeKineticCarrier

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholeKineticDecay

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence

noncomputable section

variable {nu : Viscosity} {initialState : ComplexVorticityHilbertState} {time : Real}
  (receipt : WholeContinuousMildSerrinReceipt nu initialState time)

theorem rowPower_integral (wave : IntegerWavevector) (nonzero : wave ≠ 0)
    (terminal : Icc (0 : Real) time) :
    (∫ actual in Iic terminal, rowPower receipt wave actual ∂commonTimeMeasure time) =
      complexCoordinateAmplitudeSq (receipt.wholePath terminal wave) / integerWaveViscousMultiplier wave -
        complexCoordinateAmplitudeSq (initialState wave) / integerWaveViscousMultiplier wave := by
  let raw := fun actual => 2 * complexCoordinateRealInner (receipt.rowExtension wave nonzero actual)
    (commonTimeZeroExtension time (receipt.rowTangent wave nonzero) actual) / integerWaveViscousMultiplier wave
  calc
    _ = ∫ actual in Iic terminal, raw actual.1 ∂commonTimeMeasure time := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro actual _
      simp only [raw, rowPower, dif_pos nonzero, receipt.rowExtension_on_interval,
        commonTimeZeroExtension_of_mem time _ actual.1 actual.2]
    _ = ∫ actual in (0 : Real)..terminal.1, raw actual :=
      commonTime_integral_Iic_eq_intervalIntegral time receipt.requestedTimePos.le terminal raw
    _ = _ := by
      dsimp only [raw]
      rw [intervalIntegral.integral_div, row_energy receipt wave nonzero terminal, sub_div]

theorem energy_identity (terminal : Icc (0 : Real) time) :
    (∫ actual in Iic terminal, power receipt actual ∂commonTimeMeasure time) =
      puncturedWholeVorticityKineticMass (receipt.wholePath terminal) -
        puncturedWholeVorticityKineticMass initialState := by
  let work := fun wave => ∫ actual in Iic terminal, rowPower receipt wave actual ∂commonTimeMeasure time
  have support : Function.support work ⊆ {wave | wave ≠ (0 : IntegerWavevector)} := by
    intro wave nonzero
    by_contra zero
    have equal : wave = 0 := by simpa using zero
    subst wave
    simp [work, rowPower] at nonzero
  have integrated : HasSum work (puncturedWholeVorticityKineticMass (receipt.wholePath terminal) -
      puncturedWholeVorticityKineticMass initialState) := by
    apply (hasSum_subtype_iff_of_support_subset support).mp
    exact ((summable_puncturedWholeVorticityKineticMass (receipt.wholePath terminal)).hasSum.sub
      (summable_puncturedWholeVorticityKineticMass initialState).hasSum).congr_fun
        (fun wave => rowPower_integral receipt wave.1 wave.2 terminal)
  have fromCarrier := SpaceTimeWork.integral_hasSum (carrier receipt) receipt.wholeTangent (Iic terminal)
  have perRow (wave : IntegerWavevector) :
      (∫ actual in Iic terminal, SpaceTimeWork.row (carrier receipt) receipt.wholeTangent wave actual
        ∂commonTimeMeasure time) = work wave := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (rowPower_eq_weighted_ae receipt wave)] with actual same
    exact same.symm
  rw [funext perRow] at fromCarrier
  calc
    _ = ∫ actual in Iic terminal, ∑' wave, SpaceTimeWork.row (carrier receipt) receipt.wholeTangent wave actual
        ∂commonTimeMeasure time := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (eventually_countable_forall.2 (rowPower_eq_weighted_ae receipt))] with actual same
      exact tsum_congr same
    _ = _ := fromCarrier.unique integrated

theorem power_eq_viscous_ae :
    ∀ᵐ actual ∂commonTimeMeasure time, power receipt actual =
      -2 * nu.coeff * wholeVorticityEuclideanMass (receipt.wholePath actual) := by
  filter_upwards [receiptPointwiseGradient_ae_summable receipt,
    receiptStateLimit_eq_wholePath_ae receipt, receipt.wholePath_eq_transverse_ae,
    wholePath_fourierReality_ae receipt,
    eventually_countable_forall.2 (fun wave : NonzeroIntegerWavevector =>
      receipt.rowTangent_eq_unforced_ae wave.1 wave.2)] with actual gradient state same reality rows
  rw [state] at gradient
  let field := receipt.wholePath actual
  let kinetic := puncturedWholeVorticityKineticEuclideanState field
  let tangent := puncturedWholeUnforcedNegativeOneEuclideanState nu.coeff field
    (wholePath_transverse receipt actual) gradient
  have pointwise (wave : NonzeroIntegerWavevector) : rowPower receipt wave.1 actual =
      2 * (inner Complex (kinetic wave) (tangent wave)).re := by
    have nonzero : wave.1 ≠ 0 := wave.2
    rw [rowPower, dif_pos nonzero, rows wave, ← same]
    change 2 * complexCoordinateRealInner (field wave.1)
      (wholeStateVorticityNonlinearCoefficientAt field wave.1 -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • field wave.1) /
          integerWaveViscousMultiplier wave.1 = _
    simp only [kinetic, tangent, puncturedWholeVorticityKineticEuclideanState_apply,
      puncturedWholeUnforcedNegativeOneEuclideanState_apply_eq_coefficient]
    rw [puncturedKinetic_unforcedNegativeOne_re_inner_eq,
      complexCoordinateRealInner_sub_right, complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_self, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    field_simp [ne_of_gt (integerWaveViscousMultiplier_pos wave)]
  have support : Function.support (fun wave => rowPower receipt wave actual) ⊆
      {wave | wave ≠ (0 : IntegerWavevector)} := by
    intro wave nonzero
    by_contra zero
    have equal : wave = 0 := by simpa using zero
    subst wave
    simp [rowPower] at nonzero
  have sum := ((Complex.hasSum_re (lp.hasSum_inner kinetic tangent)).mul_left 2).tsum_eq
  have cancellation := puncturedWholeUnforcedNegativeOneEuclideanState_kineticPairing nu.coeff field
    (receipt.wholePath_zero_row actual) (wholePath_transverse receipt actual) reality gradient
  calc
    _ = ∑' wave : NonzeroIntegerWavevector, rowPower receipt wave.1 actual :=
      (tsum_subtype_eq_of_support_subset support).symm
    _ = 2 * (inner Complex kinetic tangent).re := (tsum_congr pointwise).trans sum
    _ = _ := by rw [cancellation]; ring

end
end SaturationMonoid.NavierStokes.WholeKineticDecay
