import H0mework.NavierStokes.CofinalAction.CofinalRecovery

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryMomentumIntegral

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeRecoveryRowAction NativeRecoveryPhysical NativeTimeJetCarrier NativeHigherTimeJets
open NativeCofinalRecoveryAction NativeCofinalMomentumAction

noncomputable section

variable {nu : Viscosity}
  {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

theorem velocity_zero (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (actual : ℝ) : velocity receipt actual 0 = 0 :=
  wholeMild_zero ledger receipt _

theorem rate_zero (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (actual : ℝ) : rateRow receipt 0 actual = 0 := by
  simp [rateRow, nonlinearRow, projectedDivergenceCLM_apply, transverseProjection,
    integerWaveViscousMultiplier]

theorem rate_integrable (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : IntervalIntegrable (rateRow receipt wave) volume 0 1 := by
  by_cases nonzero : wave ≠ 0
  · have pathPaid : IntervalIntegrable (rowExtension receipt wave) volume 0 1 :=
      (rowExtension_absolutelyContinuous receipt wave).continuousOn.intervalIntegrable
    have inherited := (inheritedForcing_integrable receipt wave).sub
      (pathPaid.smul (nu.coeff * integerWaveViscousMultiplier wave))
    apply inherited.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [inheritedForcing_eq_source_ae receipt wave] with time same member
    rw [uIoc_of_le zero_le_one] at member
    have inside : time ∈ Icc (0 : ℝ) 1 := ⟨member.1.le, member.2⟩
    simp only [Pi.smul_apply]
    rw [same inside, rowExtension_on_interval receipt wave nonzero ⟨time, inside⟩]
    rfl
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    have same : rateRow receipt 0 = fun _ => (0 : ComplexCoordinateVector) :=
      funext (rate_zero receipt)
    rw [same]
    exact intervalIntegrable_const

/-- The inherited Duhamel path writes the actual full velocity action at every endpoint. -/
theorem velocity_sub_eq_integral (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (a b : Icc (0 : ℝ) 1) (ordered : a.1 ≤ b.1) (wave : IntegerWavevector) :
    receipt.wholePath b wave - receipt.wholePath a wave =
      ∫ time in a.1..b.1, rateRow receipt wave time := by
  by_cases nonzero : wave ≠ 0
  · have sourceAC : AbsolutelyContinuousOnInterval (rowExtension receipt wave) a.1 b.1 :=
      (rowExtension_absolutelyContinuous receipt wave).mono (by
        simpa only [uIcc_of_le ordered, uIcc_of_le zero_le_one] using
          Icc_subset_Icc a.2.1 b.2.2)
    have sourcePaid := (rate_integrable receipt wave).mono_set (by
      rw [uIcc_of_le ordered, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc a.2.1 b.2.2)
    have sourceAE : ∀ᵐ time : ℝ, time ∈ uIcc a.1 b.1 →
        HasDerivAt (rowExtension receipt wave) (rateRow receipt wave time) time := by
      filter_upwards [rowExtension_derivative_ae receipt wave nonzero] with time evolves member
      rw [uIcc_of_le ordered] at member
      exact evolves ⟨a.2.1.trans member.1, member.2.trans b.2.2⟩
    have written := path_sub_eq_intervalIntegral sourceAC sourcePaid sourceAE b.1 (by simp)
    rw [rowExtension_on_interval receipt wave nonzero b,
      rowExtension_on_interval receipt wave nonzero a,
      velocity_on_interval receipt b, velocity_on_interval receipt a] at written
    exact written
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp only [wholeMild_zero ledger receipt, rate_zero, sub_self, intervalIntegral.integral_zero]

theorem source_recovery_momentum_write (initial : GeneratedWholeRestartCurrent nu)
    (a b : Icc (0 : ℝ) 1) (ordered : a.1 ≤ b.1) (wave : IntegerWavevector) :
    recoveryVelocity initial b wave - recoveryVelocity initial a wave =
      ∫ time in a.1..b.1,
        rateRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave time :=
  velocity_sub_eq_integral _ a b ordered wave

theorem wholePath_momentum_write
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (a b : Icc (0 : ℝ) 1) (ordered : a.1 ≤ b.1) (wave : IntegerWavevector) :
    receipt.wholePath b wave - receipt.wholePath a wave =
      ∫ time in a.1..b.1,
        projectedDivergenceCLM wave (NativeStressSource.quadraticFlux (velocity receipt time) wave) -
          (nu.coeff * integerWaveViscousMultiplier wave) • velocity receipt time wave :=
  velocity_sub_eq_integral receipt a b ordered wave

theorem source_recovery_zero (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    recoveryVelocity initial zeroTime wave = endpointVelocity initial wave := by
  rw [endpointVelocity_coefficient]
  exact (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).initial_row wave

theorem source_next_initial_momentum_write (initial : GeneratedWholeRestartCurrent nu)
    (wave : IntegerWavevector) :
    biotSavartVelocityCoefficient wave
        ((sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).initialState wave) -
      endpointVelocity initial wave =
        ∫ time in (0 : ℝ)..(sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1,
          rateRow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) wave time := by
  rw [(sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial).2.2 wave]
  rw [← source_recovery_zero initial wave]
  exact source_recovery_momentum_write initial zeroTime
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.1 wave

end
end SaturationMonoid.NavierStokes.NativeRecoveryMomentumIntegral
