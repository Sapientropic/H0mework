import H0mework.NavierStokes.RecoveryAction.Recovery
import H0mework.NavierStokes.NormControl.Global

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryKineticDecay

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeRecoveryControlProducer NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderFlux

noncomputable section

variable {nu : Viscosity}

def rate (nu : Viscosity) : ℝ := 2 * nu.coeff * (2 * Real.pi) ^ 2

theorem rate_pos : 0 < rate nu := by
  have viscosity := nu.coeff_pos
  have piPositive := Real.pi_pos
  unfold rate
  positivity

variable (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) (radius : ℕ)

def energy (actual : ℝ) : ℝ := finiteStateVorticityKineticEnergy (wholeRestartModes radius) ((ledger.family.stage radius).trajectory actual)

theorem energy_derivative (actual : Icc (0 : ℝ) 1) :
    HasDerivAt (energy ledger radius)
      (-nu.coeff * finiteStateVorticityMass (wholeRestartModes radius) ((ledger.family.stage radius).trajectory actual.1)) actual.1 :=
  finiteStateVorticityKineticEnergy_hasDerivAt_generator (wholeRestartModes radius)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
    (fun _ inside => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius inside)
    nu.coeff (ledger.family.stage radius).trajectory actual.1 ((ledger.family.stage radius).physical actual.1 actual.2).1
    (fun wave _ => ((ledger.family.stage radius).physical actual.1 actual.2).2.2.1 wave)
    (fun wave _ => ((ledger.family.stage radius).physical actual.1 actual.2).2.2.2 wave)

theorem energy_poincare (actual : Icc (0 : ℝ) 1) :
    2 * (2 * Real.pi) ^ 2 * energy ledger radius actual.1 ≤
      finiteStateVorticityMass (wholeRestartModes radius) ((ledger.family.stage radius).trajectory actual.1) := by
  have angularPos : 0 < (2 * Real.pi) ^ 2 := sq_pos_of_pos (by positivity)
  have rows (wave : IntegerWavevector) (inside : wave ∈ wholeRestartModes radius) :
      complexCoordinateVectorNormSq ((ledger.family.stage radius).trajectory actual.1 wave) /
        ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) ≤
      complexCoordinateVectorNormSq ((ledger.family.stage radius).trajectory actual.1 wave) / (2 * Real.pi) ^ 2 := by
    apply div_le_div_of_nonneg_left (complexCoordinateVectorNormSq_nonneg _) angularPos
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_integerWaveNormSq wave (ne_of_mem_of_not_mem inside (zero_not_mem_puncturedIntegerWaveFrequencyCube radius))) angularPos.le
  have summed := Finset.sum_le_sum rows
  rw [← Finset.sum_div] at summed
  have paid := (le_div_iff₀ angularPos).mp summed
  rw [energy, finiteStateVorticityKineticEnergy_eq_weightedVorticity (wholeRestartModes radius)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius) _
    (fun wave _ => ((ledger.family.stage radius).physical actual.1 actual.2).2.2.1 wave)]
  unfold finiteStateVorticityMass
  nlinarith

theorem energy_le_exp (actual : Icc (0 : ℝ) 1) :
    energy ledger radius actual.1 ≤ energy ledger radius 0 * Real.exp (-rate nu * actual.1) := by
  have bound := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (f := energy ledger radius) (coefficient := fun _ => -rate nu)
    (f' := fun time => -nu.coeff * finiteStateVorticityMass (wholeRestartModes radius) ((ledger.family.stage radius).trajectory time))
    (a := 0) (b := 1) (fun time inside => energy_derivative ledger radius ⟨time, inside⟩) continuous_const.continuousOn
    (fun time inside => by
      have paid := mul_le_mul_of_nonneg_left (energy_poincare ledger radius ⟨time, inside⟩) nu.coeff_pos.le
      unfold rate
      nlinarith)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using bound actual.1 actual.2

theorem stage_weight_zero_le_exp (actual : Icc (0 : ℝ) 1) (ceiling : ℝ) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight 0 ceiling) ((ledger.family.stage radius).trajectory actual.1) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 * Real.exp (-rate nu * actual.1) := by
  have generated := (energy_le_exp ledger radius actual).trans
    (mul_le_mul_of_nonneg_right (ledger.kinetic_energy_le radius ⟨0, le_rfl, zero_le_one⟩) (Real.exp_pos _).le)
  have doubled := mul_le_mul_of_nonneg_left generated (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [energy, weightedVelocityEnergy, wordWeight, pow_zero, one_pow, one_mul,
    finiteStateVorticityKineticEnergy, ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num] using doubled

theorem wholeMild_velocity_square_le_exp (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (actual : Icc (0 : ℝ) 1) :
    ‖puncturedEuclideanize (receipt.wholePath actual)‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 * Real.exp (-rate nu * actual.1) := by
  have paid := wholeMild_moment_of_eventual_stage_control ledger receipt.core id strictMono_id 0
    (‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 * Real.exp (-rate nu * actual.1)) actual
    (fun ceiling _ => Eventually.of_forall fun index => stage_weight_zero_le_exp ledger (receipt.core.subsequence index) actual ceiling)
  have sum : Summable fun wave => complexCoordinateAmplitudeSq (receipt.wholePath actual wave) := by
    have generated := paid.1
    change Summable (fun wave => (NativeFullOrderAction.frequencySize wave ^ 0) ^ 2 *
      complexCoordinateVectorNormSq (velocityEndpointWholeMildState receipt.core actual wave)) at generated
    simpa only [pow_zero, one_pow, one_mul, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      receipt.wholePath_apply] using generated
  have full : (∑' wave, complexCoordinateAmplitudeSq (receipt.wholePath actual wave)) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 * Real.exp (-rate nu * actual.1) := by
    simpa only [velocityMomentDensity, pow_zero, one_pow, one_mul,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, receipt.wholePath_apply] using paid.2
  rw [puncturedEuclideanize_norm_sq]
  exact (Summable.tsum_subtype_le (fun wave => complexCoordinateAmplitudeSq (receipt.wholePath actual wave))
    {wave : IntegerWavevector | wave ≠ 0} (fun _ => complexCoordinateAmplitudeSq_nonneg _) sum).trans full

end
end SaturationMonoid.NavierStokes.NativeRecoveryKineticDecay
