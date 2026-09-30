import H0mework.NavierStokes.SourceEstimates.SpaceTimeWork
import H0mework.NavierStokes.Crossing.TangentCoercivity
import H0mework.NavierStokes.PairRestart.PairDuhamelKineticTriadRedirect

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholeKineticDecay

open scoped ENNReal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

noncomputable section

theorem realInner_smul_left (scalar : Real) (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (scalar • left) right = scalar * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

def weightCLM : ComplexVorticityHilbertState →L[Complex] ComplexVorticityHilbertState :=
  lp.mapCLM 2 (fun wave => wholeKineticFourierWeight wave • ContinuousLinearMap.id Complex _)
    zero_le_one (fun wave => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro value
      simpa only [smul_apply, ContinuousLinearMap.id_apply, norm_smul, one_mul] using
        mul_le_mul_of_nonneg_right (wholeKineticFourierWeight_norm_le_one wave) (norm_nonneg value))

theorem weightCLM_row (field : ComplexVorticityHilbertState) (wave : IntegerWavevector)
    (nonzero : wave ≠ 0) : weightCLM field wave =
      (Real.sqrt (integerWaveViscousMultiplier wave))⁻¹ • field wave := by
  ext coordinate
  simp [weightCLM, wholeKineticFourierWeight, nonzero, Complex.real_smul]

theorem weightCLM_zero (field : ComplexVorticityHilbertState) : weightCLM field 0 = 0 := by
  ext coordinate
  simp [weightCLM, wholeKineticFourierWeight]

variable {nu : Viscosity} {initialState : ComplexVorticityHilbertState} {time : Real}
  (receipt : WholeContinuousMildSerrinReceipt nu initialState time)

def carrier : SpaceTimeState time := (weightCLM.compLpL 2 (commonTimeMeasure time)) receipt.stateLimit

theorem carrier_row_ae (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    ∀ᵐ actual ∂commonTimeMeasure time, carrier receipt actual wave =
      (Real.sqrt (integerWaveViscousMultiplier wave))⁻¹ • receipt.wholePath actual wave := by
  filter_upwards [weightCLM.coeFn_compLpL receipt.stateLimit,
    receiptStateLimit_eq_wholePath_ae receipt] with actual weight same
  change carrier receipt actual = _ at weight
  rw [weight, same, weightCLM_row _ wave nonzero]

def rowPower (wave : IntegerWavevector) (actual : Icc (0 : Real) time) : Real :=
  if nonzero : wave ≠ 0 then 2 * complexCoordinateRealInner
    (receipt.wholePath actual wave) (receipt.rowTangent wave nonzero actual) /
      integerWaveViscousMultiplier wave else 0

theorem rowPower_eq_weighted_ae (wave : IntegerWavevector) :
    ∀ᵐ actual ∂commonTimeMeasure time, rowPower receipt wave actual =
      SpaceTimeWork.row (carrier receipt) receipt.wholeTangent wave actual := by
  by_cases nonzero : wave ≠ 0
  · filter_upwards [carrier_row_ae receipt wave nonzero,
      receipt.rowTangent_eq_wholeTangent_ae wave nonzero] with actual left right
    have sqrtNe := ne_of_gt (Real.sqrt_pos.2 (integerWaveViscousMultiplier_pos ⟨wave, nonzero⟩))
    have rightReal : Real.sqrt (integerWaveViscousMultiplier wave) • receipt.wholeTangent actual wave =
        receipt.rowTangent wave nonzero actual := by
      ext coordinate
      simpa only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] using congr_fun right coordinate
    have tangent : receipt.wholeTangent actual wave =
        (Real.sqrt (integerWaveViscousMultiplier wave))⁻¹ • receipt.rowTangent wave nonzero actual := by
      rw [← rightReal, smul_smul, inv_mul_cancel₀ sqrtNe, one_smul]
    rw [rowPower, dif_pos nonzero, SpaceTimeWork.row, left, tangent,
      realInner_smul_left, complexCoordinateRealInner_real_smul_right]
    have square := Real.sq_sqrt (integerWaveViscousMultiplier_pos ⟨wave, nonzero⟩).le
    field_simp [sqrtNe, ne_of_gt (integerWaveViscousMultiplier_pos ⟨wave, nonzero⟩)]
    rw [square]
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    filter_upwards [weightCLM.coeFn_compLpL receipt.stateLimit] with actual weight
    change carrier receipt actual = _ at weight
    simp only [rowPower, ne_eq, not_true_eq_false, SpaceTimeWork.row, weight, weightCLM_zero]
    simp [complexCoordinateRealInner]

def power (actual : Icc (0 : Real) time) : Real := ∑' wave, rowPower receipt wave actual

theorem power_integrable : Integrable (power receipt) (commonTimeMeasure time) := by
  apply (SpaceTimeWork.total_integrable (carrier receipt) receipt.wholeTangent).congr
  filter_upwards [eventually_countable_forall.2 (rowPower_eq_weighted_ae receipt)] with actual same
  exact tsum_congr fun wave => (same wave).symm

theorem row_energy (wave : IntegerWavevector) (nonzero : wave ≠ 0)
    (terminal : Icc (0 : Real) time) :
    (∫ actual in (0 : Real)..terminal.1, 2 * complexCoordinateRealInner
      (receipt.rowExtension wave nonzero actual)
      (commonTimeZeroExtension time (receipt.rowTangent wave nonzero) actual)) =
        complexCoordinateAmplitudeSq (receipt.wholePath terminal wave) -
          complexCoordinateAmplitudeSq (initialState wave) := by
  have ac := (receipt.rowExtension_absolutelyContinuous wave nonzero).mono (by
    rw [uIcc_of_le terminal.2.1, uIcc_of_le receipt.requestedTimePos.le]
    exact Icc_subset_Icc le_rfl terminal.2.2)
  have derivative : ∀ᵐ actual : Real, actual ∈ uIcc (0 : Real) terminal.1 →
      HasDerivAt (receipt.rowExtension wave nonzero)
        (commonTimeZeroExtension time (receipt.rowTangent wave nonzero) actual) actual := by
    filter_upwards [receipt.rowExtension_ae_hasDerivAt wave nonzero] with actual derivative
    intro member
    apply derivative
    rw [uIcc_of_le terminal.2.1] at member
    rw [uIcc_of_le receipt.requestedTimePos.le]
    exact ⟨member.1, member.2.trans terminal.2.2⟩
  have energy := AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity ac derivative
  rw [receipt.rowExtension_on_interval wave nonzero terminal,
    receipt.rowExtension_on_interval wave nonzero ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩,
    receipt.wholePath_initial] at energy
  exact energy

end
end SaturationMonoid.NavierStokes.WholeKineticDecay
