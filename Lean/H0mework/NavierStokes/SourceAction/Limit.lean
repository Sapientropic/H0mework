import H0mework.NavierStokes.SourceAction.Energy
import H0mework.NavierStokes.Restart.WholeContinuousMildSerrin

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeFullOrderLimit

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMildClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeMildAssembly
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open NativeFullOrderEnergy

noncomputable section

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed]
  {seed : Seed} {replay : GeneratedWholeRestartCanonicalReplay seed}

/-- The original whole-closure subsequence converges at every physical time
to the velocity read from its own continuous receipt. -/
theorem closure_velocity_row_tendsto
    (closure : GeneratedWholeRestartCriticalClosure replay) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    Tendsto (fun index => finiteStateVelocityCoefficient
      ((replay.current (closure.weakClosure.subsequence index)).trajectory time.1) wave)
      atTop (𝓝 (finiteStateVelocityCoefficient
        ((wholeRestartWholeContinuousMildSerrinReceipt closure).wholePath time) wave)) := by
  by_cases waveZero : wave = 0
  · subst wave
    simpa only [finiteStateVelocityCoefficient, biotSavartVelocityCoefficient_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ComplexCoordinateVector)) atTop (𝓝 0))
  · have observed := (wholeRestartFixedWaveMildHolderReceipt closure wave waveZero).row_full_tendsto
    have evaluated := ((BoundedContinuousFunction.evalCLM ℂ time).continuous.tendsto
      (wholeRestartFixedWaveMildData closure wave waveZero).rowPath).comp observed
    change Tendsto (fun index =>
      (replay.current (closure.weakClosure.subsequence index)).trajectory time.1 wave)
      atTop (𝓝 ((wholeRestartFixedWaveMildData closure wave waveZero).rowPath time)) at evaluated
    rw [← wholeRestartWholeMildAssembly_fixedWave_eq closure wave waveZero time] at evaluated
    exact (biotSavartVelocityCLM wave).continuous.tendsto _ |>.comp evaluated

theorem closure_weightedVelocityEnergy_tendsto
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (observed : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    Tendsto (fun index => weightedVelocityEnergy observed weight
      ((replay.current (closure.weakClosure.subsequence index)).trajectory time.1))
      atTop (𝓝 (weightedVelocityEnergy observed weight
        ((wholeRestartWholeContinuousMildSerrinReceipt closure).wholePath time))) := by
  have squareContinuous : Continuous complexCoordinateVectorNormSq := by
    unfold complexCoordinateVectorNormSq
    fun_prop
  unfold weightedVelocityEnergy
  apply tendsto_finsetSum
  intro wave _
  exact tendsto_const_nhds.mul ((squareContinuous.tendsto _).comp
    (closure_velocity_row_tendsto closure wave time))

theorem weightedVelocityEnergy_le_of_support
    (observed modes : Finset IntegerWavevector) (weight : IntegerWavevector → ℝ)
    (state : ComplexVorticityHilbertState)
    (support : ∀ wave, wave ∉ modes → state wave = 0) :
    weightedVelocityEnergy observed weight state ≤ weightedVelocityEnergy modes weight state := by
  have nonnegative (wave : IntegerWavevector) : 0 ≤ weight wave ^ 2 *
      complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave) := by
    apply mul_nonneg (sq_nonneg _)
    unfold complexCoordinateVectorNormSq
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  unfold weightedVelocityEnergy
  calc
    _ = ∑ wave ∈ observed ∩ modes, weight wave ^ 2 *
        complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro wave observedMem outside
      have waveOutside : wave ∉ modes := fun waveMem => outside (Finset.mem_inter.mpr ⟨observedMem, waveMem⟩)
      simp [finiteStateVelocityCoefficient, support wave waveOutside, complexCoordinateVectorNormSq]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun wave _ _ => nonnegative wave)

/-- A finite-stage budget is consumed on the original complete receipt,
without choosing a new limit or exceptional-time representative. -/
theorem generated_receipt_weightedVelocityEnergy_le
    (replay : GeneratedWholeRestartCanonicalReplay seed)
    (weight : IntegerWavevector → ℝ) (bound : ℝ)
    (finiteBound : ∀ radius, ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration seed),
      weightedVelocityEnergy (wholeRestartModes radius) weight
        ((replay.current radius).trajectory time) ≤ bound)
    (observed : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    weightedVelocityEnergy observed weight
      ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) ≤ bound := by
  let closure := generatedWholeRestartCriticalClosure replay
  apply le_of_tendsto' (closure_weightedVelocityEnergy_tendsto closure observed weight time)
  intro index
  let radius := closure.weakClosure.subsequence index
  exact (weightedVelocityEnergy_le_of_support observed (wholeRestartModes radius) weight
    ((replay.current radius).trajectory time.1) ((replay.current radius).physical time.1 time.2).2.1).trans
      (finiteBound radius time.1 time.2)

theorem generated_receipt_weightedVelocity_summable_and_tsum_le
    (replay : GeneratedWholeRestartCanonicalReplay seed)
    (weight : IntegerWavevector → ℝ) (bound : ℝ)
    (finiteBound : ∀ radius, ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration seed),
      weightedVelocityEnergy (wholeRestartModes radius) weight
        ((replay.current radius).trajectory time) ≤ bound)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    Summable (fun wave => weight wave ^ 2 * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) wave)) ∧
      (∑' wave, weight wave ^ 2 * complexCoordinateVectorNormSq
        (finiteStateVelocityCoefficient
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) wave)) ≤ bound := by
  have nonnegative (wave : IntegerWavevector) : 0 ≤ weight wave ^ 2 * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) wave) := by
    apply mul_nonneg (sq_nonneg _)
    unfold complexCoordinateVectorNormSq
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have finiteControl (observed : Finset IntegerWavevector) :=
    generated_receipt_weightedVelocityEnergy_le replay weight bound finiteBound observed time
  exact ⟨summable_of_sum_le nonnegative finiteControl,
    Real.tsum_le_of_sum_le nonnegative finiteControl⟩

end
end SaturationMonoid.NavierStokes.NativeFullOrderLimit
