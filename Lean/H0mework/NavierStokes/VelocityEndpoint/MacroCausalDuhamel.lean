import H0mework.NavierStokes.VelocityEndpoint.MacroPhysicalStage

/-!
# Causal Duhamel globalization of one endpoint macro stage

Every pre-accumulation receipt already carries an actual whole unforced mild
write.  This module transports those writes through the physical
Biot--Savart map before any endpoint quotient, recursively identifies the
result with the literal native run currents, and composes the generated
endpoint mild write on the same coefficient carrier.

In the source-owned zero kinetic-defect branch, the complete finite Duhamel
write-chain converges strongly to every post-accumulation value of the exact
macro physical stage.  No target path, continuation witness, cutoff,
integrability certificate, gluing equality, or branch choice is supplied by
the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointMacroCausalDuhamel

open scoped Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep

noncomputable section

theorem heatDuhamelComplexCoordinatePath_restart_eq_causal_sum
    (initial : ComplexCoordinateVector)
    (prior next : ℝ → ComplexCoordinateVector)
    (damping start joinTime time : ℝ) :
    heatDuhamelComplexCoordinatePath
        (heatDuhamelComplexCoordinatePath
          initial prior damping start joinTime)
        next damping joinTime time =
      Real.exp (-damping * (time - start)) • initial +
        (∫ earlier in start..joinTime,
          Real.exp (-damping * (time - earlier)) • prior earlier) +
        ∫ earlier in joinTime..time,
          Real.exp (-damping * (time - earlier)) • next earlier := by
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  rw [smul_add]
  rw [smul_smul]
  rw [← intervalIntegral.integral_smul]
  have initialWeight :
      Real.exp (-damping * (time - joinTime)) *
          Real.exp (-damping * (joinTime - start)) =
        Real.exp (-damping * (time - start)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [initialWeight]
  have priorIntegralEq :
      (∫ earlier in start..joinTime,
          Real.exp (-damping * (time - joinTime)) •
            (Real.exp (-damping * (joinTime - earlier)) • prior earlier)) =
        ∫ earlier in start..joinTime,
          Real.exp (-damping * (time - earlier)) • prior earlier := by
    apply intervalIntegral.integral_congr
    intro earlier _earlierMem
    dsimp
    rw [smul_smul, ← Real.exp_add]
    congr 1
    ring_nf
  rw [priorIntegralEq]

theorem biotSavartVelocityCoefficient_heatDuhamelComplexCoordinatePath
    (wave : IntegerWavevector)
    (initial : ComplexCoordinateVector)
    (nonlinear : ℝ → ComplexCoordinateVector)
    (damping start time : ℝ)
    (nonlinearIntegrable :
      IntervalIntegrable nonlinear volume start time) :
    biotSavartVelocityCoefficient wave
        (heatDuhamelComplexCoordinatePath
          initial nonlinear damping start time) =
      heatDuhamelComplexCoordinatePath
        (biotSavartVelocityCoefficient wave initial)
        (fun earlier =>
          biotSavartVelocityCoefficient wave (nonlinear earlier))
        damping start time := by
  have weightedIntegrable :
      IntervalIntegrable
        (fun earlier =>
          Real.exp (-damping * (time - earlier)) • nonlinear earlier)
        volume start time :=
    nonlinearIntegrable.continuousOn_smul (by fun_prop)
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  change
    (biotSavartVelocityCLM wave)
        (Real.exp (-damping * (time - start)) • initial +
          ∫ earlier in start..time,
            Real.exp (-damping * (time - earlier)) • nonlinear earlier) = _
  rw [map_add, map_smul]
  rw [← (biotSavartVelocityCLM wave).intervalIntegral_comp_comm
    weightedIntegrable]
  apply congrArg₂ (fun left right => left + right)
  · rfl
  · apply intervalIntegral.integral_congr
    intro earlier _earlierMem
    simp only [map_smul, biotSavartVelocityCLM_apply]

theorem fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (nu : ℝ)
    (wave : IntegerWavevector)
    (initial : ComplexCoordinateVector)
    (nonlinear :
      MeasureTheory.Lp ComplexCoordinateVector 1
        (commonTimeMeasure requestedTime))
    (time : Icc (0 : ℝ) requestedTime) :
    fixedWaveHeatDuhamelValue requestedTime nu wave initial nonlinear time =
      heatDuhamelComplexCoordinatePath
        initial
        (commonTimeZeroExtension requestedTime nonlinear)
        (nu * integerWaveViscousMultiplier wave) 0 time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime requestedTimeNonneg time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            nu (time.1 - earlier) wave •
          commonTimeZeroExtension requestedTime nonlinear earlier)
  have convertedIntegral' :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              nu (time.1 - earlier.1) wave •
            nonlinear earlier
          ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              nu (time.1 - earlier) wave •
            commonTimeZeroExtension requestedTime nonlinear earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    filter_upwards with earlier
    rw [commonTimeZeroExtension_of_mem
      requestedTime nonlinear earlier.1 earlier.property]
  unfold fixedWaveHeatDuhamelValue
  rw [convertedIntegral']
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

theorem
    wholeContinuousMildSerrinReceipt_biotSavartWholePath_wave_eq_heatDuhamelPath
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    biotSavartVelocityCoefficient wave
        (receipt.wholePath time wave) =
      heatDuhamelComplexCoordinatePath
        (biotSavartVelocityCoefficient wave (initialState wave))
        (fun earlier =>
          biotSavartVelocityCoefficient wave
            (commonTimeZeroExtension requestedTime
              (transverseSpaceTimeNonlinearRow
                receipt.transverseLimit wave) earlier))
        (nu.coeff * integerWaveViscousMultiplier wave) 0 time.1 := by
  rw [receipt.row_mild_identity wave waveNonzero time]
  rw [fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath
    requestedTime receipt.requestedTimePos.le nu.coeff wave
    (initialState wave)
    (transverseSpaceTimeNonlinearRow receipt.transverseLimit wave) time]
  exact
    biotSavartVelocityCoefficient_heatDuhamelComplexCoordinatePath
      wave (initialState wave)
      (commonTimeZeroExtension requestedTime
        (transverseSpaceTimeNonlinearRow receipt.transverseLimit wave))
      (nu.coeff * integerWaveViscousMultiplier wave) 0 time.1
      (by
        apply IntervalIntegrable.mono_set'
          (commonTimeZeroExtension_intervalIntegrable
            requestedTime receipt.requestedTimePos.le
            (transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave))
        rw [uIoc_of_le time.2.1,
          uIoc_of_le receipt.requestedTimePos.le]
        intro actual actualMem
        exact ⟨actualMem.1, actualMem.2.trans time.2.2⟩)

theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_eq_receiptVelocityHeatDuhamel
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (localTime :
      Icc (0 : ℝ) (run initial index).contact.time.1)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded
          (wholeRestartReceiptPreAccumulationTime
            initial elapsedBounded index localTime) wave =
      euclideanCoordinateRow
        (heatDuhamelComplexCoordinatePath
          (biotSavartVelocityCoefficient wave.1
            ((run initial index).initialState wave.1))
          (fun earlier =>
            biotSavartVelocityCoefficient wave.1
              (commonTimeZeroExtension
                (run initial index).contact.time.1
                (transverseSpaceTimeNonlinearRow
                  (run initial index).contact.prefixReceipt.transverseLimit
                  wave.1)
                earlier))
          (nu.coeff * integerWaveViscousMultiplier wave.1)
          0 localTime.1) := by
  unfold wholeRestartBoundedPreAccumulationVelocityTrajectory
  rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_receipt_chart]
  ext coordinate
  rw [puncturedWholeVelocityEuclideanState_apply,
    puncturedWholeVelocityEuclideanCoefficient_apply,
    euclideanCoordinateRow_apply]
  exact congrFun
    (wholeContinuousMildSerrinReceipt_biotSavartWholePath_wave_eq_heatDuhamelPath
      (run initial index).contact.prefixReceipt wave.1 wave.2 localTime)
    coordinate

/-- Put one actual inner restart receipt on its endpoint macro stage clock.
The time is determined by the two nested source clocks. -/
def wholeRestartEndpointMacroPreReceiptTime
    {nu : Viscosity}
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (index : ℕ)
    (localTime :
      Icc (0 : ℝ) (run current index).contact.time.1) :
    Icc (0 : ℝ) step.clockAdvance :=
  ⟨elapsedTime current index + localTime.1, by
    constructor
    · exact add_nonneg
        (GeneratedWholeRestartCurrent.elapsedTime_nonneg current index)
        localTime.2.1
    · have beforeAccumulation :
          elapsedTime current index + localTime.1 <
            wholeRestartVelocityAccumulationTime current := by
        calc
          elapsedTime current index + localTime.1 ≤
              elapsedTime current (index + 1) := by
            rw [elapsedTime_succ]
            linarith [localTime.2.2]
          _ < wholeRestartVelocityAccumulationTime current :=
            elapsedTime_lt_wholeRestartVelocityAccumulationTime
              current step.elapsedBounded (index + 1)
      exact (beforeAccumulation.trans (by
        rw [step.clockAdvance_eq_selectedAbsoluteTime]
        exact
          (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
            current step.elapsedBounded).selectedAbsoluteTime_gt_accumulation)).le⟩

/-- Every old-run chart inside an actual endpoint macro edge is literally
the same receipt's unforced velocity Duhamel write. -/
theorem physicalStage_eq_preReceiptVelocityHeatDuhamel
    {nu : Viscosity}
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (index : ℕ)
    (localTime :
      Icc (0 : ℝ) (run current index).contact.time.1)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    step.physicalStage
          (wholeRestartEndpointMacroPreReceiptTime
            step index localTime) wave =
      euclideanCoordinateRow
        (heatDuhamelComplexCoordinatePath
          (biotSavartVelocityCoefficient wave.1
            ((run current index).initialState wave.1))
          (fun earlier =>
            biotSavartVelocityCoefficient wave.1
              (commonTimeZeroExtension
                (run current index).contact.time.1
                (transverseSpaceTimeNonlinearRow
                  (run current index).contact.prefixReceipt.transverseLimit
                  wave.1)
                earlier))
          (nu.coeff * integerWaveViscousMultiplier wave.1)
          0 localTime.1) := by
  have timeBefore :
      (step.physicalStageTime
        (wholeRestartEndpointMacroPreReceiptTime
          step index localTime)).1 <
        wholeRestartVelocityAccumulationTime current := by
    change elapsedTime current index + localTime.1 <
      wholeRestartVelocityAccumulationTime current
    calc
      elapsedTime current index + localTime.1 ≤
          elapsedTime current (index + 1) := by
        rw [elapsedTime_succ]
        linarith [localTime.2.2]
      _ < wholeRestartVelocityAccumulationTime current :=
        elapsedTime_lt_wholeRestartVelocityAccumulationTime
          current step.elapsedBounded (index + 1)
  rw [physicalStage]
  rw [sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt
    current step.elapsedBounded _ timeBefore]
  convert
    wholeRestartBoundedPreAccumulationVelocityTrajectory_eq_receiptVelocityHeatDuhamel
      current step.elapsedBounded index localTime wave using 1
  apply congrArg
    (fun time =>
      wholeRestartBoundedPreAccumulationVelocityTrajectory
        current step.elapsedBounded time wave)
  apply Subtype.ext
  rfl

/-- Recursive velocity-side Duhamel write read from the actual restart
receipts.  Every nonlinear row and duration is selected by the source run. -/
noncomputable def wholeRestartVelocityNestedDuhamel
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    ℕ → ComplexCoordinateVector
  | 0 =>
      biotSavartVelocityCoefficient wave.1
        (initial.initialState wave.1)
  | index + 1 =>
      heatDuhamelComplexCoordinatePath
        (wholeRestartVelocityNestedDuhamel initial wave index)
        (fun earlier =>
          biotSavartVelocityCoefficient wave.1
            (commonTimeZeroExtension
              (run initial index).contact.time.1
              (transverseSpaceTimeNonlinearRow
                (run initial index).contact.prefixReceipt.transverseLimit
                wave.1)
              earlier))
        (nu.coeff * integerWaveViscousMultiplier wave.1)
        0 (run initial index).contact.time.1

/-- The recursive Duhamel write is not a surrogate trajectory: at every
finite stage it is exactly the velocity row of the source-owned next
current. -/
theorem wholeRestartVelocityNestedDuhamel_eq_runInitialVelocity
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    ∀ index : ℕ,
      wholeRestartVelocityNestedDuhamel initial wave index =
        biotSavartVelocityCoefficient wave.1
          ((run initial index).initialState wave.1)
  | 0 => rfl
  | index + 1 => by
      let terminal :
          Icc (0 : ℝ) (run initial index).contact.time.1 :=
        ⟨(run initial index).contact.time.1,
          (run initial index).contact.time_pos.le, le_rfl⟩
      rw [wholeRestartVelocityNestedDuhamel]
      rw [wholeRestartVelocityNestedDuhamel_eq_runInitialVelocity
        initial wave index]
      rw [←
        wholeContinuousMildSerrinReceipt_biotSavartWholePath_wave_eq_heatDuhamelPath
          (run initial index).contact.prefixReceipt
          wave.1 wave.2 terminal]
      have terminalEq :
          (run initial index).contact.prefixReceipt.wholePath terminal =
            (run initial index).contact.physicalState := by
        simpa only [terminal] using
          (run initial index).contact.prefixReceipt_terminal
      rw [terminalEq]
      exact congrArg
        (fun state : ComplexVorticityHilbertState =>
          biotSavartVelocityCoefficient wave.1 (state wave.1))
        (run_succ_initialState initial index).symm

/-- In the zero-defect branch the complete nested Duhamel write converges,
before any coefficient quotient, to the source-generated velocity endpoint
row. -/
theorem wholeRestartVelocityNestedDuhamel_succ_tendsto_endpoint_of_kineticDefect_eq_zero
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    let endpoint :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt.velocityEndpoint
    Tendsto
      (fun index =>
        wholeRestartVelocityNestedDuhamel initial wave (index + 1))
      atTop
      (nhds
        (wholeRestartVelocityEndpointCoefficient endpoint wave.1)) := by
  dsimp only
  apply tendsto_pi_nhds.mpr
  intro coordinate
  have physicalTrace :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint_of_kineticDefect_eq_zero
      initial elapsedBounded defectZero wave coordinate
  have sampled :=
    physicalTrace.comp
      (wholeRestartContactEndpointPreAccumulationTime_tendsto_atTop
        initial elapsedBounded)
  convert sampled using 1
  · funext index
    simp only [Function.comp_apply]
    rw [wholeRestartVelocityNestedDuhamel_eq_runInitialVelocity]
    rw [wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint]
    rw [run_succ_initialState]
    rfl
  · apply congrArg nhds
    rw [wholeRestartVelocityEndpointCoefficient_of_ne _ wave.1 wave.2]

/-- The endpoint half of one actual macro stage, written on the same
velocity coefficient carrier as the old nested receipt chain. -/
noncomputable def wholeRestartEndpointMacroVelocityDuhamelPath
    {nu : Viscosity}
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded
  let endpoint :=
    sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      current step.elapsedBounded
  heatDuhamelComplexCoordinatePath
    (wholeRestartVelocityEndpointCoefficient
      ledger.family.endpointReceipt.velocityEndpoint wave.1)
    (commonTimeZeroExtension 1
      (wholeVelocityLerayProjectionSpaceTime wave.1
        (endpoint.core.nonlinearLimit wave.1)))
    (nu.coeff * integerWaveViscousMultiplier wave.1) 0

/-- Every post-accumulation point of the actual macro stage is exactly the
endpoint Duhamel write, now on a real-line coefficient carrier suitable for
causal composition. -/
theorem physicalStage_eq_endpointMacroVelocityDuhamelPath_of_accumulation_le
    {nu : Viscosity}
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : Icc (0 : ℝ) step.clockAdvance)
    (timeAfter :
      wholeRestartVelocityAccumulationTime current ≤ time.1)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    step.physicalStage time wave =
      euclideanCoordinateRow
        (wholeRestartEndpointMacroVelocityDuhamelPath step wave
          (endpointAbsoluteToLocalTime
            (wholeRestartVelocityAccumulationTime current)
            ⟨time.1, timeAfter, (step.physicalStageTime time).2.2⟩).1) := by
  ext coordinate
  rw [step.physicalStage_row_mildIdentity_of_accumulation_le
    time timeAfter wave coordinate]
  unfold wholeRestartEndpointMacroVelocityDuhamelPath
  rw [euclideanCoordinateRow_apply]
  exact congrFun
    (fixedWaveHeatDuhamelValue_eq_heatDuhamelComplexCoordinatePath
      1 (by norm_num) nu.coeff wave.1
      (wholeRestartVelocityEndpointCoefficient
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt.velocityEndpoint
        wave.1)
      (wholeVelocityLerayProjectionSpaceTime wave.1
        ((sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
          current step.elapsedBounded).core.nonlinearLimit wave.1))
      (endpointAbsoluteToLocalTime
        (wholeRestartVelocityAccumulationTime current)
      ⟨time.1, timeAfter, (step.physicalStageTime time).2.2⟩))
    coordinate

/-- Zero defect makes the endpoint continuation the strong causal limit of
the complete finite source receipt chain.  The conclusion is already the
actual post-accumulation physical stage, not a caller-supplied target path. -/
theorem nestedDuhamel_tendsto_physicalStage_of_kineticDefect_eq_zero
    {nu : Viscosity}
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (defectZero :
      wholeRestartKineticWeakEndpointDefect current
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0)
    (time : Icc (0 : ℝ) step.clockAdvance)
    (timeAfter :
      wholeRestartVelocityAccumulationTime current ≤ time.1)
    (wave :
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector) :
    let localTime :=
      (endpointAbsoluteToLocalTime
        (wholeRestartVelocityAccumulationTime current)
        ⟨time.1, timeAfter, (step.physicalStageTime time).2.2⟩).1
    let endpointNonlinear :=
      commonTimeZeroExtension 1
        (wholeVelocityLerayProjectionSpaceTime wave.1
          ((sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
            current step.elapsedBounded).core.nonlinearLimit wave.1))
    Tendsto
      (fun index =>
        euclideanCoordinateRow
          (heatDuhamelComplexCoordinatePath
            (wholeRestartVelocityNestedDuhamel current wave (index + 1))
            endpointNonlinear
            (nu.coeff * integerWaveViscousMultiplier wave.1)
            0 localTime))
      atTop
      (nhds (step.physicalStage time wave)) := by
  dsimp only
  let endpoint :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt.velocityEndpoint
  let endpointNonlinear :=
    commonTimeZeroExtension 1
      (wholeVelocityLerayProjectionSpaceTime wave.1
        ((sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
          current step.elapsedBounded).core.nonlinearLimit wave.1))
  let localTime :=
    (endpointAbsoluteToLocalTime
      (wholeRestartVelocityAccumulationTime current)
      ⟨time.1, timeAfter, (step.physicalStageTime time).2.2⟩).1
  have nestedTendsto :=
    wholeRestartVelocityNestedDuhamel_succ_tendsto_endpoint_of_kineticDefect_eq_zero
      current step.elapsedBounded defectZero wave
  have continuationContinuous :
      Continuous fun initialRow : ComplexCoordinateVector =>
        heatDuhamelComplexCoordinatePath
          initialRow endpointNonlinear
          (nu.coeff * integerWaveViscousMultiplier wave.1)
          0 localTime := by
    simp_rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
    fun_prop
  have continuedTendsto :
      Tendsto
        (fun index =>
          heatDuhamelComplexCoordinatePath
            (wholeRestartVelocityNestedDuhamel current wave (index + 1))
            endpointNonlinear
            (nu.coeff * integerWaveViscousMultiplier wave.1)
            0 localTime)
        atTop
        (nhds
          (heatDuhamelComplexCoordinatePath
            (wholeRestartVelocityEndpointCoefficient endpoint wave.1)
            endpointNonlinear
            (nu.coeff * integerWaveViscousMultiplier wave.1)
            0 localTime)) :=
    (continuationContinuous.tendsto
      (wholeRestartVelocityEndpointCoefficient endpoint wave.1)).comp
        nestedTendsto
  have euclideanContinuous :
      Continuous euclideanCoordinateRow :=
    PiLp.continuous_toLp
      (p := (2 : ENNReal))
      (β := fun _ : Coordinate => ℂ)
  have physicalTendsto :
      Tendsto
        (fun index =>
          euclideanCoordinateRow
            (heatDuhamelComplexCoordinatePath
              (wholeRestartVelocityNestedDuhamel
                current wave (index + 1))
              endpointNonlinear
              (nu.coeff * integerWaveViscousMultiplier wave.1)
              0 localTime))
        atTop
        (nhds
          (euclideanCoordinateRow
            (heatDuhamelComplexCoordinatePath
              (wholeRestartVelocityEndpointCoefficient endpoint wave.1)
              endpointNonlinear
              (nu.coeff * integerWaveViscousMultiplier wave.1)
              0 localTime))) := by
    convert
      ((euclideanContinuous.tendsto
        (heatDuhamelComplexCoordinatePath
          (wholeRestartVelocityEndpointCoefficient endpoint wave.1)
          endpointNonlinear
          (nu.coeff * integerWaveViscousMultiplier wave.1)
          0 localTime)).comp continuedTendsto) using 1
    rfl
  rw [physicalStage_eq_endpointMacroVelocityDuhamelPath_of_accumulation_le
    step time timeAfter wave]
  simpa only [Function.comp_apply,
    wholeRestartEndpointMacroVelocityDuhamelPath,
    endpoint, endpointNonlinear, localTime] using physicalTendsto

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointMacroCausalDuhamel
end NavierStokes
end SaturationMonoid
