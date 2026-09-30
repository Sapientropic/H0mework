import H0mework.NavierStokes.Accumulation.BoundaryDisposition
import H0mework.NavierStokes.Accumulation.NativeTurbulenceLaw
import H0mework.NavierStokes.Fourier.ConcreteNonlinearOutput
import H0mework.NavierStokes.Crossing.HighFrequencyAggregateRateObstruction
import H0mework.NavierStokes.Restart.BoundedPreAccumulationVelocityStrongTrace
import H0mework.NavierStokes.VelocityEndpoint.PositiveTimeH1Reentry
import H0mework.NavierStokes.Fourier.WholeVelocityPairDiagonalBudget
import H0mework.NavierStokes.ShellSources.InfiniteLineageHilbertCompletion

/-!
# Concrete nonlinear effect data

A concrete closed-triad whole-vorticity source selects a short actual restart
receipt on which one positive nonlinear Fourier row regenerates.  This module
proves the state, contact, persistence, outflux, and payment estimates only.
Root authority and inquiry execution remain owned by the sealed boundary
engine; no domain-local root or event inventory is assembled here.
-/

set_option autoImplicit false

open scoped BigOperators Interval ENNReal

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteEffectRecurrence

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientConcreteActivePair
open ThreeDimensionalVorticityCoefficientConcreteActiveClosedTriad
open ThreeDimensionalVorticityCoefficientConcreteNonlinearOutput
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeMildAssembly
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregatePersistence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateRateObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticViscousExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMildClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def concreteBoundaryState : ComplexVorticityHilbertState :=
  generatedComplexVorticityState concreteActiveClosedTriadSource
    (generatedSupport concreteActiveClosedTriadSource)

theorem concreteBoundaryState_zero : concreteBoundaryState 0 = 0 := by
  simp [concreteBoundaryState]

theorem concreteBoundaryState_transverse :
    WholeStateTransverse concreteBoundaryState := by
  intro wave
  rw [concreteBoundaryState, generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ generatedSupport concreteActiveClosedTriadSource
  · rw [if_pos waveMem]
    exact generatedVorticityCoefficient_transverse _ _
  · rw [if_neg waveMem]
    simp

theorem concreteBoundaryState_reality :
    FiniteStateFourierReality concreteBoundaryState := by
  intro wave
  rw [concreteBoundaryState, generatedComplexVorticityState_apply,
    generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ generatedSupport concreteActiveClosedTriadSource
  · have negMem :
        waveNeg wave ∈ generatedSupport concreteActiveClosedTriadSource :=
      generatedSupport_waveNeg_mem _ waveMem
    rw [if_pos waveMem, if_pos negMem,
      generatedVorticityCoefficient_waveNeg]
  · have negNotMem :
        waveNeg wave ∉ generatedSupport concreteActiveClosedTriadSource := by
      simpa using waveMem
    rw [if_neg waveMem, if_neg negNotMem]
    simp

def concreteBoundarySeed (nu : Viscosity) :
    SourceOwnedWholeRestartPhysicalSeed nu where
  physicalState := concreteBoundaryState
  physicalState_zero := concreteBoundaryState_zero
  transverse := concreteBoundaryState_transverse
  reality := concreteBoundaryState_reality

def concreteBoundaryReplay (nu : Viscosity) :=
  generatedWholeRestartCanonicalReplay (concreteBoundarySeed nu)

def concreteBoundaryReceipt (nu : Viscosity) :=
  wholeRestartWholeContinuousMildSerrinReceipt
    (generatedWholeRestartCriticalClosure (concreteBoundaryReplay nu))

theorem concreteBoundaryState_nonlinearOutput :
    wholeStateVorticityNonlinearCoefficientAt
        concreteBoundaryState concreteStretchingOutput =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  have supported :
      ∀ wave : IntegerWavevector,
        wave ∉ generatedSupport concreteActiveClosedTriadSource →
          concreteBoundaryState wave = 0 := by
    intro wave waveNotMem
    simp [concreteBoundaryState, generatedComplexVorticityState_apply,
      waveNotMem]
  calc
    wholeStateVorticityNonlinearCoefficientAt
        concreteBoundaryState concreteStretchingOutput =
      finiteStateVorticityNonlinearCoefficientAt
        (generatedSupport concreteActiveClosedTriadSource)
        concreteBoundaryState concreteStretchingOutput := by
          apply wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
          exact supported
    _ = generatedVorticityNonlinearCoefficientAt
        concreteActiveClosedTriadSource concreteStretchingOutput := by
          exact finiteStateVorticityNonlinearCoefficientAt_generatedSource
            concreteActiveClosedTriadSource concreteStretchingOutput
    _ = _ := concreteNonlinearOutput_coefficient

theorem concreteBoundaryReceipt_output_continuous
    (nu : Viscosity) :
    Continuous fun time :
        Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)) =>
      wholeStateVorticityNonlinearCoefficientAt
        ((concreteBoundaryReceipt nu).wholePath time)
        concreteStretchingOutput := by
  let transversePath :
      Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)) →
        WholeTransverseVorticityState := fun time =>
    ⟨(concreteBoundaryReceipt nu).wholePath time,
      wholePath_transverse (concreteBoundaryReceipt nu) time⟩
  have transversePathContinuous : Continuous transversePath :=
    (concreteBoundaryReceipt nu).wholePath.continuous.subtype_mk
      (wholePath_transverse (concreteBoundaryReceipt nu))
  have rowContinuous :
      Continuous fun time :
          Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)) =>
        wholeStateVorticityNonlinearCoefficientAt
          (transversePath time).1 concreteStretchingOutput :=
    (wholeStateVorticityNonlinearCoefficientAt_continuous
      concreteStretchingOutput).comp transversePathContinuous
  simpa only [transversePath] using rowContinuous

theorem concreteBoundaryReceipt_output_initial_persistence
    (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ time : Icc (0 : Real)
          (wholeRestartDuration (concreteBoundarySeed nu)),
        time.1 < epsilon →
          (1 / 8 : Real) <
            (wholeStateVorticityNonlinearCoefficientAt
              ((concreteBoundaryReceipt nu).wholePath time)
              concreteStretchingOutput 1).re := by
  let zeroTime :
      Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos (concreteBoundarySeed nu)).le⟩⟩
  let coordinateValue :
      Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)) →
        Real := fun time =>
    (wholeStateVorticityNonlinearCoefficientAt
      ((concreteBoundaryReceipt nu).wholePath time)
      concreteStretchingOutput 1).re
  have coordinateContinuous : Continuous coordinateValue := by
    exact Complex.continuous_re.comp
      ((continuous_apply 1).comp
        (concreteBoundaryReceipt_output_continuous nu))
  have zeroValue : coordinateValue zeroTime = 1 / 4 := by
    dsimp only [coordinateValue, zeroTime]
    rw [(concreteBoundaryReceipt nu).wholePath_initial]
    change
      (wholeStateVorticityNonlinearCoefficientAt
        concreteBoundaryState concreteStretchingOutput 1).re = 1 / 4
    rw [concreteBoundaryState_nonlinearOutput]
    norm_num
  have neighborhoodOpen :
      IsOpen {time | (1 / 8 : Real) < coordinateValue time} :=
    isOpen_lt continuous_const coordinateContinuous
  have zeroMem : zeroTime ∈
      {time | (1 / 8 : Real) < coordinateValue time} := by
    rw [Set.mem_setOf_eq, zeroValue]
    norm_num
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen zeroTime zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro time timeLt
  apply ballSubset
  rw [Metric.mem_ball]
  change dist time.1 zeroTime.1 < epsilon
  simpa only [zeroTime, Real.dist_eq, sub_zero,
    abs_of_nonneg time.2.1] using timeLt

def concreteBoundaryPersistenceTime (nu : Viscosity) : Real :=
  Classical.choose (concreteBoundaryReceipt_output_initial_persistence nu)

theorem concreteBoundaryPersistenceTime_pos (nu : Viscosity) :
    0 < concreteBoundaryPersistenceTime nu :=
  (Classical.choose_spec
    (concreteBoundaryReceipt_output_initial_persistence nu)).1

theorem concreteBoundaryPersistenceTime_spec
    (nu : Viscosity)
    (time : Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)))
    (timeLt : time.1 < concreteBoundaryPersistenceTime nu) :
    (1 / 8 : Real) <
      (wholeStateVorticityNonlinearCoefficientAt
        ((concreteBoundaryReceipt nu).wholePath time)
        concreteStretchingOutput 1).re :=
  (Classical.choose_spec
    (concreteBoundaryReceipt_output_initial_persistence nu)).2 time timeLt

def concreteBoundaryShortDuration (nu : Viscosity) : Real :=
  min (wholeRestartDuration (concreteBoundarySeed nu))
      (concreteBoundaryPersistenceTime nu) / 2

theorem concreteBoundaryShortDuration_pos (nu : Viscosity) :
    0 < concreteBoundaryShortDuration nu := by
  unfold concreteBoundaryShortDuration
  exact div_pos
    (lt_min (wholeRestartDuration_pos (concreteBoundarySeed nu))
      (concreteBoundaryPersistenceTime_pos nu)) (by norm_num)

theorem concreteBoundaryShortDuration_le_original (nu : Viscosity) :
    concreteBoundaryShortDuration nu ≤
      wholeRestartDuration (concreteBoundarySeed nu) := by
  unfold concreteBoundaryShortDuration
  have minLe := min_le_left
    (wholeRestartDuration (concreteBoundarySeed nu))
    (concreteBoundaryPersistenceTime nu)
  have minPos : 0 <
      min (wholeRestartDuration (concreteBoundarySeed nu))
        (concreteBoundaryPersistenceTime nu) :=
    lt_min (wholeRestartDuration_pos (concreteBoundarySeed nu))
      (concreteBoundaryPersistenceTime_pos nu)
  nlinarith

theorem concreteBoundaryShortDuration_lt_persistence (nu : Viscosity) :
    concreteBoundaryShortDuration nu < concreteBoundaryPersistenceTime nu := by
  unfold concreteBoundaryShortDuration
  have minLe := min_le_right
    (wholeRestartDuration (concreteBoundarySeed nu))
    (concreteBoundaryPersistenceTime nu)
  have persistencePos := concreteBoundaryPersistenceTime_pos nu
  nlinarith

def concreteBoundaryShortReceipt (nu : Viscosity) :
    WholeContinuousMildSerrinReceipt
      nu concreteBoundaryState (concreteBoundaryShortDuration nu) :=
  restrictWholeContinuousMildSerrinReceipt
    (concreteBoundaryShortDuration_pos nu)
    (concreteBoundaryShortDuration_le_original nu)
    (concreteBoundaryReceipt nu)

def concreteBoundaryShortContact (nu : Viscosity) :=
  generatedPositiveWholeRestartContact (concreteBoundaryShortReceipt nu)

def concreteBoundaryShortCurrent (nu : Viscosity) :
    GeneratedWholeRestartCurrent nu where
  initialState := concreteBoundaryState
  duration := concreteBoundaryShortDuration nu
  receipt := concreteBoundaryShortReceipt nu
  contact := concreteBoundaryShortContact nu

def concreteBoundaryShortContactOriginalTime (nu : Viscosity) :
    Icc (0 : Real) (wholeRestartDuration (concreteBoundarySeed nu)) :=
  commonTimeInclusion (concreteBoundaryShortDuration_le_original nu)
    (concreteBoundaryShortContact nu).time

theorem concreteBoundaryShortContact_time_lt_persistence (nu : Viscosity) :
    (concreteBoundaryShortContactOriginalTime nu).1 <
      concreteBoundaryPersistenceTime nu :=
  lt_of_le_of_lt (concreteBoundaryShortContact nu).time.2.2
    (concreteBoundaryShortDuration_lt_persistence nu)

theorem concreteBoundaryShortContact_output_pos (nu : Viscosity) :
    (1 / 8 : Real) <
      (wholeStateVorticityNonlinearCoefficientAt
        (concreteBoundaryShortContact nu).physicalState
        concreteStretchingOutput 1).re := by
  change (1 / 8 : Real) <
    (wholeStateVorticityNonlinearCoefficientAt
      ((concreteBoundaryReceipt nu).wholePath
        (concreteBoundaryShortContactOriginalTime nu))
      concreteStretchingOutput 1).re
  exact concreteBoundaryPersistenceTime_spec nu
    (concreteBoundaryShortContactOriginalTime nu)
    (concreteBoundaryShortContact_time_lt_persistence nu)

theorem concreteBoundaryShortCurrent_initial_output_pos (nu : Viscosity) :
    (1 / 8 : Real) <
      (wholeStateVorticityNonlinearCoefficientAt
        (concreteBoundaryShortCurrent nu).initialState
        concreteStretchingOutput 1).re := by
  change (1 / 8 : Real) <
    (wholeStateVorticityNonlinearCoefficientAt
      concreteBoundaryState concreteStretchingOutput 1).re
  rw [concreteBoundaryState_nonlinearOutput]
  norm_num

theorem concreteBoundaryShortCurrent_firstTarget_output_pos (nu : Viscosity) :
    (1 / 8 : Real) <
      (wholeStateVorticityNonlinearCoefficientAt
        (run (concreteBoundaryShortCurrent nu) 1).initialState
        concreteStretchingOutput 1).re := by
  rw [show (1 : Nat) = 0 + 1 by omega, run_succ_initialState]
  exact concreteBoundaryShortContact_output_pos nu

/-! ## Concrete source-native outflux effect -/

def concreteDepletingModes : Finset IntegerWavevector :=
  {concreteTestingWave, concreteStretchingOutput}

theorem concreteStretchingOutput_eq_waveNeg_testing :
    concreteStretchingOutput = waveNeg concreteTestingWave := by
  decide

theorem concreteDepletingModes_zeroNotMem :
    (0 : IntegerWavevector) ∉ concreteDepletingModes := by
  decide

theorem concreteDepletingModes_disjoint_pairOutput :
    Disjoint concreteDepletingModes
      (finiteVorticityPairOutputSupport concreteDepletingModes) := by
  decide

private theorem concreteDepletingModes_resolvedWork_zero
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityNonlinearWork concreteDepletingModes
        (complexSharpSupportProjection concreteDepletingModes state) = 0 := by
  unfold finiteStateVorticityNonlinearWork
  apply Finset.sum_eq_zero
  intro wave waveMem
  have coefficientZero :
      finiteStateVorticityNonlinearCoefficientAt concreteDepletingModes
          (complexSharpSupportProjection concreteDepletingModes state) wave = 0 :=
    finiteStateVorticityNonlinearCoefficientAt_eq_zero_of_not_mem_pairOutput
      concreteDepletingModes _ wave fun wavePairMem =>
        (Finset.disjoint_left.mp concreteDepletingModes_disjoint_pairOutput)
          waveMem wavePairMem
  rw [coefficientZero]
  simp [complexCoordinateRealInner]

private theorem concreteDepletingModes_resolvedPower_zero
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (actual : Real) :
    actualResolvedEnstrophyPower receipt concreteDepletingModes actual = 0 := by
  change 2 * finiteStateVorticityNonlinearWork concreteDepletingModes
    (complexSharpSupportProjection concreteDepletingModes
      (actualWholeProjectedTransversePath receipt actual).1) = 0
  rw [concreteDepletingModes_resolvedWork_zero]
  ring

private theorem concreteDepletingModes_resolvedWork_zero_receipt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    actualResolvedEnstrophyWork receipt concreteDepletingModes = 0 := by
  unfold actualResolvedEnstrophyWork
  simp_rw [concreteDepletingModes_resolvedPower_zero receipt]
  simp

private theorem concreteDepletingModes_pairWork_eq_projectedPower_integral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    actualWholeFinitePairOccurrenceWork receipt concreteDepletingModes =
      ∫ actual in (0 : Real)..requestedTime,
        nativeTemporalProjectedWholeEnstrophyPower
          receipt concreteDepletingModes actual := by
  rw [actualWholeFinitePairOccurrenceWork_eq_resolved_add_nativeFluxWork
    receipt concreteDepletingModes concreteDepletingModes_zeroNotMem]
  rw [concreteDepletingModes_resolvedWork_zero_receipt]
  simp only [zero_add]
  unfold actualNativeTurbulenceEnstrophyFluxWork
  apply intervalIntegral.integral_congr
  intro actual _actualMem
  have split := actualProjectedWholeEnstrophyPower_eq_resolved_add_native
    receipt concreteDepletingModes actual
  rw [concreteDepletingModes_resolvedPower_zero receipt actual,
    zero_add] at split
  exact split.symm

theorem nativeTemporalProjectedWholeEnstrophyPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous (nativeTemporalProjectedWholeEnstrophyPower receipt modes) := by
  have stateContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous receipt)
  unfold nativeTemporalProjectedWholeEnstrophyPower
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro wave waveMem
  have stateRowContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp stateContinuous
  have projectedRowContinuous :
      Continuous fun actual : Real =>
        (complexSharpSupportProjection modes
          (actualWholeProjectedTransversePath receipt actual).1) wave := by
    simpa only [complexSharpSupportProjection_apply, if_pos waveMem] using
      stateRowContinuous
  have nonlinearContinuous :
      Continuous fun actual : Real =>
        wholeStateVorticityNonlinearCoefficientAt
          (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
      (actualWholeProjectedTransversePath_continuous receipt)
  exact complexCoordinateRealInner_prod_continuous.comp
    (projectedRowContinuous.prodMk nonlinearContinuous)

theorem positiveOutflux_contactTime_payment
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime threshold : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (outflux : NativeTemporalPositiveOutfluxAt
      receipt concreteDepletingModes threshold) :
    threshold * requestedTime +
        finiteStateVorticityCoefficientEnstrophy concreteDepletingModes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) +
        actualWholeFiniteViscousPayment receipt concreteDepletingModes ≤
      finiteStateVorticityCoefficientEnstrophy
        concreteDepletingModes initialState := by
  have workLe :
      actualWholeFinitePairOccurrenceWork receipt concreteDepletingModes ≤
        -threshold * requestedTime := by
    rw [concreteDepletingModes_pairWork_eq_projectedPower_integral]
    have integralLe := intervalIntegral.integral_mono_on
      (f := nativeTemporalProjectedWholeEnstrophyPower
        receipt concreteDepletingModes)
      (g := fun _actual : Real => -threshold)
      (μ := volume)
      receipt.requestedTimePos.le
      ((nativeTemporalProjectedWholeEnstrophyPower_continuous
        receipt concreteDepletingModes).intervalIntegrable 0 requestedTime)
      (continuous_const.intervalIntegrable 0 requestedTime)
      (fun actual actualMem => by
        have := outflux actual actualMem
        linarith)
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using integralLe
  have workEq :=
    actualWholeFinitePairOccurrenceWork_eq_terminal_sub_initial_add_viscousPayment
      receipt concreteDepletingModes concreteDepletingModes_zeroNotMem
  rw [workEq] at workLe
  linarith

theorem positiveOutflux_stage_payment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {threshold : Real}
    (stage : Nat)
    (outflux : NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt
      concreteDepletingModes threshold) :
    threshold * (run initial stage).contact.time.1 +
        finiteStateVorticityCoefficientEnstrophy concreteDepletingModes
          (run initial (stage + 1)).initialState ≤
      finiteStateVorticityCoefficientEnstrophy concreteDepletingModes
        (run initial stage).initialState := by
  have payment := positiveOutflux_contactTime_payment
    (run initial stage).contact.prefixReceipt outflux
  rw [(run initial stage).contact.prefixReceipt_terminal] at payment
  rw [run_succ_initialState]
  have viscousNonneg := actualWholeFiniteViscousPayment_nonneg
    (run initial stage).contact.prefixReceipt concreteDepletingModes
  linarith

private theorem finiteStateVorticityCoefficientEnstrophy_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityCoefficientEnstrophy modes state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_nonneg fun wave _waveMem =>
    complexCoordinateAmplitudeSq_nonneg (state wave)

/-- The actual receipt payments telescope directly over one finite native
prefix.  Every summand is read from the corresponding `run` occurrence. -/
theorem positiveOutflux_prefix_payment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {threshold : Real}
    (length : Nat)
    (outflux : ∀ stage < length, NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt
      concreteDepletingModes threshold) :
    threshold *
          (∑ stage ∈ Finset.range length,
            (run initial stage).contact.time.1) +
        finiteStateVorticityCoefficientEnstrophy concreteDepletingModes
          (run initial length).initialState ≤
      finiteStateVorticityCoefficientEnstrophy concreteDepletingModes
        initial.initialState := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      have step := positiveOutflux_stage_payment initial length
        (outflux length (Nat.lt_succ_self length))
      have prefixPaid := inductionHypothesis (fun stage stageLt =>
        outflux stage (stageLt.trans (Nat.lt_succ_self length)))
      rw [Finset.sum_range_succ]
      nlinarith

theorem contactTime_summable_of_positiveOutflux
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    {threshold : Real}
    (thresholdPos : 0 < threshold)
    (outflux : ∀ stage, NativeTemporalPositiveOutfluxAt
      (run initial stage).contact.prefixReceipt
      concreteDepletingModes threshold) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  apply summable_of_sum_range_le
  · intro stage
    exact (run_contact_time_pos initial stage).le
  · intro length
    have paid := positiveOutflux_prefix_payment initial length
      (fun stage _stageLt => outflux stage)
    have terminalNonneg := finiteStateVorticityCoefficientEnstrophy_nonneg
      concreteDepletingModes (run initial length).initialState
    apply (le_div_iff₀ thresholdPos).2
    nlinarith

private theorem concreteBoundaryState_testing :
    concreteBoundaryState concreteTestingWave =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  unfold concreteBoundaryState
  rw [generatedComplexVorticityState_apply,
    if_pos concreteTestingWave_mem_closedTriadSupport,
    concreteClosedTriad_generatedVorticity_testing]

private theorem concreteBoundaryState_stretching :
    concreteBoundaryState concreteStretchingOutput =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  rw [concreteStretchingOutput_eq_waveNeg_testing,
    concreteBoundaryState_reality,
    concreteBoundaryState_testing]
  ext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

private theorem concreteBoundaryState_nonlinear_testing :
    wholeStateVorticityNonlinearCoefficientAt concreteBoundaryState
        concreteTestingWave =
      ![(-1 / 4 : Complex), 1 / 4, 0] := by
  rw [wholeStateVorticityNonlinearCoefficientAt_waveNeg
      concreteBoundaryState concreteBoundaryState_transverse
      concreteBoundaryState_reality concreteTestingWave,
    ← concreteStretchingOutput_eq_waveNeg_testing,
    concreteBoundaryState_nonlinearOutput]
  ext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem concreteBoundaryReceipt_projectedPower_zero
    (nu : Viscosity) :
    nativeTemporalProjectedWholeEnstrophyPower
        (concreteBoundaryReceipt nu) concreteDepletingModes 0 = -1 := by
  have stateEq :
      (actualWholeProjectedTransversePath
        (concreteBoundaryReceipt nu) 0).1 = concreteBoundaryState := by
    change (concreteBoundaryReceipt nu).wholePath
      (Set.projIcc (0 : Real)
        (wholeRestartDuration (concreteBoundarySeed nu))
        (concreteBoundaryReceipt nu).requestedTimePos.le 0) =
      concreteBoundaryState
    rw [Set.projIcc_of_mem
      (concreteBoundaryReceipt nu).requestedTimePos.le
      ⟨le_rfl, (concreteBoundaryReceipt nu).requestedTimePos.le⟩]
    exact (concreteBoundaryReceipt nu).wholePath_initial
  unfold nativeTemporalProjectedWholeEnstrophyPower
  rw [stateEq]
  change 2 * (∑ wave ∈ concreteDepletingModes,
    complexCoordinateRealInner
      ((complexSharpSupportProjection concreteDepletingModes
        concreteBoundaryState) wave)
      (wholeStateVorticityNonlinearCoefficientAt
        concreteBoundaryState wave)) = -1
  have sumEq :
      (∑ wave ∈ concreteDepletingModes,
        complexCoordinateRealInner
          ((complexSharpSupportProjection concreteDepletingModes
            concreteBoundaryState) wave)
          (wholeStateVorticityNonlinearCoefficientAt
            concreteBoundaryState wave)) = -1 / 2 := by
    unfold concreteDepletingModes
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton,
        complexSharpSupportProjection_apply, if_pos (by simp),
        complexSharpSupportProjection_apply, if_pos (by simp),
        concreteBoundaryState_testing,
        concreteBoundaryState_nonlinear_testing,
        concreteBoundaryState_stretching,
        concreteBoundaryState_nonlinearOutput]
      norm_num [complexCoordinateRealInner, Fin.sum_univ_succ]
    · decide
  rw [sumEq]
  ring

theorem concreteBoundaryReceipt_outflux_initial_persistence
    (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Icc (0 : Real)
          (wholeRestartDuration (concreteBoundarySeed nu)),
        actual < epsilon →
          (1 / 2 : Real) <
            -nativeTemporalProjectedWholeEnstrophyPower
              (concreteBoundaryReceipt nu) concreteDepletingModes actual := by
  let outfluxValue : Real → Real := fun actual =>
    -nativeTemporalProjectedWholeEnstrophyPower
      (concreteBoundaryReceipt nu) concreteDepletingModes actual
  have outfluxContinuous : Continuous outfluxValue :=
    (nativeTemporalProjectedWholeEnstrophyPower_continuous
      (concreteBoundaryReceipt nu) concreteDepletingModes).neg
  have zeroValue : outfluxValue 0 = 1 := by
    dsimp only [outfluxValue]
    rw [concreteBoundaryReceipt_projectedPower_zero]
    norm_num
  have neighborhoodOpen :
      IsOpen {actual | (1 / 2 : Real) < outfluxValue actual} :=
    isOpen_lt continuous_const outfluxContinuous
  have zeroMem : 0 ∈ {actual | (1 / 2 : Real) < outfluxValue actual} := by
    rw [Set.mem_setOf_eq, zeroValue]
    norm_num
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

def concreteOutfluxPersistenceTime (nu : Viscosity) : Real :=
  Classical.choose (concreteBoundaryReceipt_outflux_initial_persistence nu)

theorem concreteOutfluxPersistenceTime_pos (nu : Viscosity) :
    0 < concreteOutfluxPersistenceTime nu :=
  (Classical.choose_spec
    (concreteBoundaryReceipt_outflux_initial_persistence nu)).1

theorem concreteOutfluxPersistenceTime_spec
    (nu : Viscosity)
    (actual : Real)
    (actualMem : actual ∈ Icc (0 : Real)
      (wholeRestartDuration (concreteBoundarySeed nu)))
    (actualLt : actual < concreteOutfluxPersistenceTime nu) :
    (1 / 2 : Real) <
      -nativeTemporalProjectedWholeEnstrophyPower
        (concreteBoundaryReceipt nu) concreteDepletingModes actual :=
  (Classical.choose_spec
    (concreteBoundaryReceipt_outflux_initial_persistence nu)).2
      actual actualMem actualLt

def concreteOutfluxShortDuration (nu : Viscosity) : Real :=
  min (wholeRestartDuration (concreteBoundarySeed nu))
      (concreteOutfluxPersistenceTime nu) / 2

theorem concreteOutfluxShortDuration_pos (nu : Viscosity) :
    0 < concreteOutfluxShortDuration nu := by
  unfold concreteOutfluxShortDuration
  exact div_pos
    (lt_min (wholeRestartDuration_pos (concreteBoundarySeed nu))
      (concreteOutfluxPersistenceTime_pos nu)) (by norm_num)

theorem concreteOutfluxShortDuration_le_original (nu : Viscosity) :
    concreteOutfluxShortDuration nu ≤
      wholeRestartDuration (concreteBoundarySeed nu) := by
  unfold concreteOutfluxShortDuration
  have minLe := min_le_left
    (wholeRestartDuration (concreteBoundarySeed nu))
    (concreteOutfluxPersistenceTime nu)
  have minPos : 0 < min
      (wholeRestartDuration (concreteBoundarySeed nu))
      (concreteOutfluxPersistenceTime nu) :=
    lt_min (wholeRestartDuration_pos (concreteBoundarySeed nu))
      (concreteOutfluxPersistenceTime_pos nu)
  nlinarith

theorem concreteOutfluxShortDuration_lt_persistence (nu : Viscosity) :
    concreteOutfluxShortDuration nu < concreteOutfluxPersistenceTime nu := by
  unfold concreteOutfluxShortDuration
  have minLe := min_le_right
    (wholeRestartDuration (concreteBoundarySeed nu))
    (concreteOutfluxPersistenceTime nu)
  have persistencePos := concreteOutfluxPersistenceTime_pos nu
  nlinarith

def concreteOutfluxShortReceipt (nu : Viscosity) :
    WholeContinuousMildSerrinReceipt nu concreteBoundaryState
      (concreteOutfluxShortDuration nu) :=
  restrictWholeContinuousMildSerrinReceipt
    (concreteOutfluxShortDuration_pos nu)
    (concreteOutfluxShortDuration_le_original nu)
    (concreteBoundaryReceipt nu)

def concreteOutfluxShortContact (nu : Viscosity) :=
  generatedPositiveWholeRestartContact (concreteOutfluxShortReceipt nu)

def concreteOutfluxShortCurrent (nu : Viscosity) :
    GeneratedWholeRestartCurrent nu where
  initialState := concreteBoundaryState
  duration := concreteOutfluxShortDuration nu
  receipt := concreteOutfluxShortReceipt nu
  contact := concreteOutfluxShortContact nu

theorem concreteOutfluxShortCurrent_initial_active
    (nu : Viscosity) :
    NativeTemporalPositiveOutfluxAt
      (concreteOutfluxShortCurrent nu).contact.prefixReceipt
      concreteDepletingModes (1 / 2) := by
  intro actual actualMem
  have actualLeShort : actual ≤ concreteOutfluxShortDuration nu :=
    actualMem.2.trans (concreteOutfluxShortContact nu).time.2.2
  have actualLeOriginal :
      actual ≤ wholeRestartDuration (concreteBoundarySeed nu) :=
    actualLeShort.trans (concreteOutfluxShortDuration_le_original nu)
  have stateEq :
      (actualWholeProjectedTransversePath
        (concreteOutfluxShortCurrent nu).contact.prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath
        (concreteBoundaryReceipt nu) actual).1 := by
    change
      (concreteOutfluxShortCurrent nu).contact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real)
            (concreteOutfluxShortCurrent nu).contact.time.1
            (concreteOutfluxShortCurrent nu).contact.time_pos.le actual) =
        (concreteBoundaryReceipt nu).wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration (concreteBoundarySeed nu))
            (concreteBoundaryReceipt nu).requestedTimePos.le actual)
    rw [Set.projIcc_of_mem
      (concreteOutfluxShortCurrent nu).contact.time_pos.le actualMem]
    rw [Set.projIcc_of_mem
      (concreteBoundaryReceipt nu).requestedTimePos.le
      ⟨actualMem.1, actualLeOriginal⟩]
    rfl
  unfold nativeTemporalProjectedWholeEnstrophyPower
  rw [stateEq]
  exact (concreteOutfluxPersistenceTime_spec nu actual
    ⟨actualMem.1, actualLeOriginal⟩
    (lt_of_le_of_lt actualLeShort
      (concreteOutfluxShortDuration_lt_persistence nu))).le

/-!
The concrete state/contact/outflux producer ends here.  Recursive living-root
authority is deliberately supplied only by the sealed boundary inquiry engine;
a domain readout must not rebuild that private executor from this source data.
-/

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteEffectRecurrence
end NavierStokes
end SaturationMonoid
