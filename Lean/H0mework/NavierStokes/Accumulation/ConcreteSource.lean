import H0mework.NavierStokes.Accumulation.ConcreteEffectRecurrence
import H0mework.NavierStokes.Accumulation.TemporalActionCoupling
import H0mework.NavierStokes.Restart.CumulativeCriticalDissipation

set_option autoImplicit false

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteThreeDimensionalSource

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientConcreteActivePair
open ThreeDimensionalVorticityCoefficientConcreteActiveClosedTriad
open ThreeDimensionalVorticityCoefficientConcreteNonlinearOutput
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteEffectRecurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- A fourth primitive frequency transverse to the old closed-triad plane. -/
def concreteLiftWave : IntegerWavevector :=
  ![0, 0, 1]

/-- A raw row already transverse to `concreteLiftWave`. -/
def concreteLiftRawVorticity : ComplexCoordinateVector :=
  ![1, 0, 0]

def concreteThreeDimensionalRawVorticity
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave = concreteLiftWave then
    concreteLiftRawVorticity
  else
    concreteClosedTriadRawVorticity wave

/-- The old active closed triad with one genuinely transverse source row. -/
def concreteThreeDimensionalSource : RawVorticityFourierSource where
  activeModes := insert concreteLiftWave
    concreteActiveClosedTriadSource.activeModes
  rawVorticity := concreteThreeDimensionalRawVorticity

@[simp] theorem concreteLiftWave_ne_zero : concreteLiftWave ≠ 0 := by
  decide

theorem concreteThreeDimensionalSource_generatedSupport_eq :
    generatedSupport concreteThreeDimensionalSource =
      insert concreteLiftWave
        (insert (waveNeg concreteLiftWave)
          (generatedSupport concreteActiveClosedTriadSource)) := by
  decide

@[simp] theorem concreteLiftWave_mem_generatedSupport :
    concreteLiftWave ∈ generatedSupport concreteThreeDimensionalSource := by
  rw [concreteThreeDimensionalSource_generatedSupport_eq]
  simp

@[simp] theorem concreteAdvectingWave_mem_generatedSupport :
    concreteAdvectingWave ∈
      generatedSupport concreteThreeDimensionalSource := by
  rw [concreteThreeDimensionalSource_generatedSupport_eq]
  simp

@[simp] theorem concreteTransportedWave_mem_generatedSupport :
    concreteTransportedWave ∈
      generatedSupport concreteThreeDimensionalSource := by
  rw [concreteThreeDimensionalSource_generatedSupport_eq]
  simp

@[simp] theorem concreteTestingWave_mem_generatedSupport :
    concreteTestingWave ∈
      generatedSupport concreteThreeDimensionalSource := by
  rw [concreteThreeDimensionalSource_generatedSupport_eq]
  simp

theorem concreteThreeDimensional_generatedVorticity_advecting :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        concreteAdvectingWave =
      ![0, (1 / 2 : Complex), 0] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteAdvectingWave_mem_generatedSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, concreteThreeDimensionalSource,
      concreteThreeDimensionalRawVorticity, concreteLiftWave,
      concreteActiveClosedTriadSource,
      concreteClosedTriadRawVorticity,
      concreteAdvectingRawVorticity, concreteAdvectingWave,
      concreteTransportedWave, concreteTestingWave, waveNeg,
      complexWavevector, integerWaveNormSq, dotProduct,
      Fin.sum_univ_succ]

theorem concreteThreeDimensional_generatedVorticity_transported :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        concreteTransportedWave =
      ![0, 0, (1 / 2 : Complex)] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteTransportedWave_mem_generatedSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, concreteThreeDimensionalSource,
      concreteThreeDimensionalRawVorticity, concreteLiftWave,
      concreteActiveClosedTriadSource,
      concreteClosedTriadRawVorticity,
      concreteTransportedRawVorticity, concreteAdvectingWave,
      concreteTransportedWave, concreteTestingWave, waveNeg,
      complexWavevector, integerWaveNormSq, dotProduct,
      Fin.sum_univ_succ]

theorem concreteThreeDimensional_generatedVorticity_testing :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        concreteTestingWave =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteTestingWave_mem_generatedSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, concreteThreeDimensionalSource,
      concreteThreeDimensionalRawVorticity, concreteLiftWave,
      concreteActiveClosedTriadSource,
      concreteClosedTriadRawVorticity,
      concreteTestingRawVorticity, concreteAdvectingWave,
      concreteTransportedWave, concreteTestingWave, waveNeg,
      complexWavevector, integerWaveNormSq, dotProduct,
      Fin.sum_univ_succ] <;>
    norm_num

theorem concreteThreeDimensional_generatedVorticity_lift :
    generatedVorticityCoefficient concreteThreeDimensionalSource
        concreteLiftWave =
      ![(1 / 2 : Complex), 0, 0] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteLiftWave_mem_generatedSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection, realitySymmetrizedVorticity,
      supportedRawVorticity, concreteThreeDimensionalSource,
      concreteThreeDimensionalRawVorticity, concreteLiftWave,
      concreteActiveClosedTriadSource, concreteLiftRawVorticity,
      concreteAdvectingWave, concreteTransportedWave,
      concreteTestingWave, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ]

/-- The lift row does not create any new ordered pair in the old depletion
output fiber. -/
theorem concreteThreeDimensional_nonlinearOutput_fiber_eq :
    generatedStretchingPairFiber concreteThreeDimensionalSource
        concreteStretchingOutput =
      generatedStretchingPairFiber concreteActiveClosedTriadSource
        concreteStretchingOutput := by
  decide

theorem concreteThreeDimensional_generatedVelocity_advecting :
    generatedVelocityCoefficient concreteThreeDimensionalSource
        concreteAdvectingWave =
      ![0, 0, (Complex.I / (((4 : Real) * Real.pi : Real) : Complex))] := by
  rw [generatedVelocityCoefficient,
    concreteThreeDimensional_generatedVorticity_advecting]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient, concreteAdvectingWave,
      complexWavevector, integerWaveNormSq, cross_apply,
      Fin.sum_univ_succ]
  all_goals ring_nf

theorem concreteThreeDimensional_generatedVelocity_transported :
    generatedVelocityCoefficient concreteThreeDimensionalSource
        concreteTransportedWave =
      ![(Complex.I / (((4 : Real) * Real.pi : Real) : Complex)), 0, 0] := by
  rw [generatedVelocityCoefficient,
    concreteThreeDimensional_generatedVorticity_transported]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient, concreteTransportedWave,
      complexWavevector, integerWaveNormSq, cross_apply,
      Fin.sum_univ_succ]
  all_goals ring_nf

theorem concreteThreeDimensional_stretchingPair_nonlinearContribution :
    generatedVorticityNonlinearPairContribution
        concreteThreeDimensionalSource concreteStretchingPair =
      ![(-1 / 4 : Complex), 0, 0] := by
  rw [generatedVorticityNonlinearPairContribution,
    generatedStretchingPairContribution,
    generatedVorticityAdvectionPairContribution]
  simp only [concreteStretchingPair,
    concreteThreeDimensional_generatedVorticity_advecting,
    concreteThreeDimensional_generatedVorticity_transported,
    concreteThreeDimensional_generatedVelocity_advecting,
    concreteThreeDimensional_generatedVelocity_transported]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [concreteTransportedWave, complexWavevector, dotProduct,
      Fin.sum_univ_succ]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem concreteThreeDimensional_reversePair_nonlinearContribution :
    generatedVorticityNonlinearPairContribution
        concreteThreeDimensionalSource concreteReverseStretchingPair =
      ![0, (1 / 4 : Complex), 0] := by
  rw [generatedVorticityNonlinearPairContribution,
    generatedStretchingPairContribution,
    generatedVorticityAdvectionPairContribution]
  simp only [concreteReverseStretchingPair,
    concreteThreeDimensional_generatedVorticity_advecting,
    concreteThreeDimensional_generatedVorticity_transported,
    concreteThreeDimensional_generatedVelocity_advecting,
    concreteThreeDimensional_generatedVelocity_transported]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [concreteAdvectingWave, complexWavevector, dotProduct,
      Fin.sum_univ_succ]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem concreteThreeDimensional_nonlinearOutput :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteStretchingOutput =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  rw [generatedVorticityNonlinearCoefficientAt,
    concreteThreeDimensional_nonlinearOutput_fiber_eq,
    concreteNonlinearOutput_fiber_eq]
  have pairNotMem :
      concreteStretchingPair ∉
        ({concreteReverseStretchingPair} : Finset StretchingPair) := by
    decide
  rw [Finset.sum_insert pairNotMem, Finset.sum_singleton,
    concreteThreeDimensional_stretchingPair_nonlinearContribution,
    concreteThreeDimensional_reversePair_nonlinearContribution]
  ext coordinate
  fin_cases coordinate <;> norm_num

/-! ## A literal non-planar generated row -/

def concreteLiftPair : StretchingPair :=
  (concreteLiftWave, concreteAdvectingWave)

def concreteReverseLiftPair : StretchingPair :=
  (concreteAdvectingWave, concreteLiftWave)

def concreteLiftOutput : IntegerWavevector :=
  ![1, 0, 1]

theorem concreteThreeDimensional_liftOutput_fiber_eq :
    generatedStretchingPairFiber concreteThreeDimensionalSource
        concreteLiftOutput =
      {concreteLiftPair, concreteReverseLiftPair} := by
  decide

theorem concreteThreeDimensional_generatedVelocity_lift :
    generatedVelocityCoefficient concreteThreeDimensionalSource
        concreteLiftWave =
      ![0, (Complex.I / (((4 : Real) * Real.pi : Real) : Complex)), 0] := by
  rw [generatedVelocityCoefficient,
    concreteThreeDimensional_generatedVorticity_lift]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient, concreteLiftWave,
      complexWavevector, integerWaveNormSq, cross_apply,
      Fin.sum_univ_succ]
  all_goals ring_nf

theorem concreteThreeDimensional_liftPair_nonlinearContribution :
    generatedVorticityNonlinearPairContribution
        concreteThreeDimensionalSource concreteLiftPair =
      ![0, 0, (-1 / 4 : Complex)] := by
  rw [generatedVorticityNonlinearPairContribution,
    generatedStretchingPairContribution,
    generatedVorticityAdvectionPairContribution]
  simp only [concreteLiftPair,
    concreteThreeDimensional_generatedVorticity_lift,
    concreteThreeDimensional_generatedVorticity_advecting,
    concreteThreeDimensional_generatedVelocity_lift,
    concreteThreeDimensional_generatedVelocity_advecting]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [concreteAdvectingWave, complexWavevector, dotProduct,
      Fin.sum_univ_succ]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem concreteThreeDimensional_reverseLiftPair_nonlinearContribution :
    generatedVorticityNonlinearPairContribution
        concreteThreeDimensionalSource concreteReverseLiftPair =
      ![(1 / 4 : Complex), 0, 0] := by
  rw [generatedVorticityNonlinearPairContribution,
    generatedStretchingPairContribution,
    generatedVorticityAdvectionPairContribution]
  simp only [concreteReverseLiftPair,
    concreteThreeDimensional_generatedVorticity_lift,
    concreteThreeDimensional_generatedVorticity_advecting,
    concreteThreeDimensional_generatedVelocity_lift,
    concreteThreeDimensional_generatedVelocity_advecting]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [concreteLiftWave, complexWavevector, dotProduct,
      Fin.sum_univ_succ]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem concreteThreeDimensional_liftOutput_nonlinearCoefficient :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteLiftOutput =
      ![(1 / 4 : Complex), 0, -1 / 4] := by
  rw [generatedVorticityNonlinearCoefficientAt,
    concreteThreeDimensional_liftOutput_fiber_eq]
  have pairNotMem :
      concreteLiftPair ∉
        ({concreteReverseLiftPair} : Finset StretchingPair) := by
    decide
  rw [Finset.sum_insert pairNotMem, Finset.sum_singleton,
    concreteThreeDimensional_liftPair_nonlinearContribution,
    concreteThreeDimensional_reverseLiftPair_nonlinearContribution]
  ext coordinate
  fin_cases coordinate <;> norm_num

theorem concreteThreeDimensional_liftOutput_nonlinearCoefficient_ne_zero :
    generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteLiftOutput ≠ 0 := by
  rw [concreteThreeDimensional_liftOutput_nonlinearCoefficient]
  intro equality
  have coordinate := congrFun equality 0
  norm_num at coordinate

def concreteThreeDimensionalState : ComplexVorticityHilbertState :=
  generatedComplexVorticityState concreteThreeDimensionalSource
    (generatedSupport concreteThreeDimensionalSource)

theorem concreteThreeDimensionalState_zero :
    concreteThreeDimensionalState 0 = 0 := by
  simp [concreteThreeDimensionalState]

theorem concreteThreeDimensionalState_transverse :
    WholeStateTransverse concreteThreeDimensionalState := by
  intro wave
  rw [concreteThreeDimensionalState, generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ generatedSupport concreteThreeDimensionalSource
  · rw [if_pos waveMem]
    exact generatedVorticityCoefficient_transverse _ _
  · rw [if_neg waveMem]
    simp

theorem concreteThreeDimensionalState_reality :
    FiniteStateFourierReality concreteThreeDimensionalState := by
  intro wave
  rw [concreteThreeDimensionalState, generatedComplexVorticityState_apply,
    generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ generatedSupport concreteThreeDimensionalSource
  · have negMem : waveNeg wave ∈
        generatedSupport concreteThreeDimensionalSource :=
      generatedSupport_waveNeg_mem _ waveMem
    rw [if_pos waveMem, if_pos negMem,
      generatedVorticityCoefficient_waveNeg]
  · have negNotMem : waveNeg wave ∉
        generatedSupport concreteThreeDimensionalSource := by
      simpa using waveMem
    rw [if_neg waveMem, if_neg negNotMem]
    simp

theorem concreteThreeDimensionalState_testing :
    concreteThreeDimensionalState concreteTestingWave =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  unfold concreteThreeDimensionalState
  rw [generatedComplexVorticityState_apply,
    if_pos concreteTestingWave_mem_generatedSupport,
    concreteThreeDimensional_generatedVorticity_testing]

theorem concreteThreeDimensionalState_lift :
    concreteThreeDimensionalState concreteLiftWave =
      ![(1 / 2 : Complex), 0, 0] := by
  unfold concreteThreeDimensionalState
  rw [generatedComplexVorticityState_apply,
    if_pos concreteLiftWave_mem_generatedSupport,
    concreteThreeDimensional_generatedVorticity_lift]

theorem concreteThreeDimensionalState_stretching :
    concreteThreeDimensionalState concreteStretchingOutput =
      ![(1 / 2 : Complex), -1 / 2, 0] := by
  rw [concreteStretchingOutput_eq_waveNeg_testing,
    concreteThreeDimensionalState_reality,
    concreteThreeDimensionalState_testing]
  ext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

theorem concreteThreeDimensionalState_nonlinearOutput :
    wholeStateVorticityNonlinearCoefficientAt
        concreteThreeDimensionalState concreteStretchingOutput =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  have supported :
      ∀ wave : IntegerWavevector,
        wave ∉ generatedSupport concreteThreeDimensionalSource →
          concreteThreeDimensionalState wave = 0 := by
    intro wave waveNotMem
    simp [concreteThreeDimensionalState,
      generatedComplexVorticityState_apply, waveNotMem]
  calc
    wholeStateVorticityNonlinearCoefficientAt
        concreteThreeDimensionalState concreteStretchingOutput =
      finiteStateVorticityNonlinearCoefficientAt
        (generatedSupport concreteThreeDimensionalSource)
        concreteThreeDimensionalState concreteStretchingOutput := by
          apply wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
          exact supported
    _ = generatedVorticityNonlinearCoefficientAt
        concreteThreeDimensionalSource concreteStretchingOutput := by
          exact finiteStateVorticityNonlinearCoefficientAt_generatedSource
            concreteThreeDimensionalSource concreteStretchingOutput
    _ = _ := concreteThreeDimensional_nonlinearOutput

theorem concreteThreeDimensionalState_nonlinear_testing :
    wholeStateVorticityNonlinearCoefficientAt
        concreteThreeDimensionalState concreteTestingWave =
      ![(-1 / 4 : Complex), (1 / 4 : Complex), 0] := by
  rw [wholeStateVorticityNonlinearCoefficientAt_waveNeg
      concreteThreeDimensionalState concreteThreeDimensionalState_transverse
      concreteThreeDimensionalState_reality concreteTestingWave,
    ← concreteStretchingOutput_eq_waveNeg_testing,
    concreteThreeDimensionalState_nonlinearOutput]
  ext coordinate
  fin_cases coordinate <;> norm_num [vectorConj]

def concreteThreeDimensionalSeed (nu : Viscosity) :
    SourceOwnedWholeRestartPhysicalSeed nu where
  physicalState := concreteThreeDimensionalState
  physicalState_zero := concreteThreeDimensionalState_zero
  transverse := concreteThreeDimensionalState_transverse
  reality := concreteThreeDimensionalState_reality

def concreteThreeDimensionalReplay (nu : Viscosity) :=
  generatedWholeRestartCanonicalReplay (concreteThreeDimensionalSeed nu)

def concreteThreeDimensionalReceipt (nu : Viscosity) :=
  wholeRestartWholeContinuousMildSerrinReceipt
    (generatedWholeRestartCriticalClosure
      (concreteThreeDimensionalReplay nu))

theorem concreteThreeDimensionalReceipt_projectedPower_zero
    (nu : Viscosity) :
    nativeTemporalProjectedWholeEnstrophyPower
        (concreteThreeDimensionalReceipt nu) concreteDepletingModes 0 = -1 := by
  have stateEq :
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalReceipt nu) 0).1 =
          concreteThreeDimensionalState := by
    change (concreteThreeDimensionalReceipt nu).wholePath
      (Set.projIcc (0 : Real)
        (wholeRestartDuration (concreteThreeDimensionalSeed nu))
        (concreteThreeDimensionalReceipt nu).requestedTimePos.le 0) =
      concreteThreeDimensionalState
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalReceipt nu).requestedTimePos.le
      ⟨le_rfl, (concreteThreeDimensionalReceipt nu).requestedTimePos.le⟩]
    exact (concreteThreeDimensionalReceipt nu).wholePath_initial
  unfold nativeTemporalProjectedWholeEnstrophyPower
  rw [stateEq]
  change 2 * (∑ wave ∈ concreteDepletingModes,
    complexCoordinateRealInner
      ((complexSharpSupportProjection concreteDepletingModes
        concreteThreeDimensionalState) wave)
      (wholeStateVorticityNonlinearCoefficientAt
        concreteThreeDimensionalState wave)) = -1
  have sumEq :
      (∑ wave ∈ concreteDepletingModes,
        complexCoordinateRealInner
          ((complexSharpSupportProjection concreteDepletingModes
            concreteThreeDimensionalState) wave)
          (wholeStateVorticityNonlinearCoefficientAt
            concreteThreeDimensionalState wave)) = -1 / 2 := by
    unfold concreteDepletingModes
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton,
        complexSharpSupportProjection_apply, if_pos (by simp),
        complexSharpSupportProjection_apply, if_pos (by simp),
        concreteThreeDimensionalState_testing,
        concreteThreeDimensionalState_nonlinear_testing,
        concreteThreeDimensionalState_stretching,
        concreteThreeDimensionalState_nonlinearOutput]
      norm_num [complexCoordinateRealInner, Fin.sum_univ_succ]
    · decide
  rw [sumEq]
  ring

theorem concreteThreeDimensionalReceipt_outflux_initial_persistence
    (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Icc (0 : Real)
          (wholeRestartDuration (concreteThreeDimensionalSeed nu)),
        actual < epsilon →
          (1 / 2 : Real) <
            -nativeTemporalProjectedWholeEnstrophyPower
              (concreteThreeDimensionalReceipt nu)
              concreteDepletingModes actual := by
  let outfluxValue : Real → Real := fun actual =>
    -nativeTemporalProjectedWholeEnstrophyPower
      (concreteThreeDimensionalReceipt nu) concreteDepletingModes actual
  have outfluxContinuous : Continuous outfluxValue :=
    (nativeTemporalProjectedWholeEnstrophyPower_continuous
      (concreteThreeDimensionalReceipt nu) concreteDepletingModes).neg
  have zeroValue : outfluxValue 0 = 1 := by
    dsimp only [outfluxValue]
    rw [concreteThreeDimensionalReceipt_projectedPower_zero]
    norm_num
  have neighborhoodOpen :
      IsOpen {actual | (1 / 2 : Real) < outfluxValue actual} :=
    isOpen_lt continuous_const outfluxContinuous
  have zeroMem : 0 ∈
      {actual | (1 / 2 : Real) < outfluxValue actual} := by
    change (1 / 2 : Real) < outfluxValue 0
    rw [zeroValue]
    norm_num
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

def concreteThreeDimensionalOutfluxPersistenceTime
    (nu : Viscosity) : Real :=
  Classical.choose
    (concreteThreeDimensionalReceipt_outflux_initial_persistence nu)

theorem concreteThreeDimensionalOutfluxPersistenceTime_pos
    (nu : Viscosity) :
    0 < concreteThreeDimensionalOutfluxPersistenceTime nu :=
  (Classical.choose_spec
    (concreteThreeDimensionalReceipt_outflux_initial_persistence nu)).1

theorem concreteThreeDimensionalOutfluxPersistenceTime_spec
    (nu : Viscosity)
    (actual : Real)
    (actualMem : actual ∈ Icc (0 : Real)
      (wholeRestartDuration (concreteThreeDimensionalSeed nu)))
    (actualLt : actual <
      concreteThreeDimensionalOutfluxPersistenceTime nu) :
    (1 / 2 : Real) <
      -nativeTemporalProjectedWholeEnstrophyPower
        (concreteThreeDimensionalReceipt nu)
        concreteDepletingModes actual :=
  (Classical.choose_spec
    (concreteThreeDimensionalReceipt_outflux_initial_persistence nu)).2
      actual actualMem actualLt

def concreteThreeDimensionalOutfluxShortDuration
    (nu : Viscosity) : Real :=
  min (wholeRestartDuration (concreteThreeDimensionalSeed nu))
      (concreteThreeDimensionalOutfluxPersistenceTime nu) / 2

theorem concreteThreeDimensionalOutfluxShortDuration_pos
    (nu : Viscosity) :
    0 < concreteThreeDimensionalOutfluxShortDuration nu := by
  unfold concreteThreeDimensionalOutfluxShortDuration
  exact div_pos
    (lt_min (wholeRestartDuration_pos (concreteThreeDimensionalSeed nu))
      (concreteThreeDimensionalOutfluxPersistenceTime_pos nu))
    (by norm_num)

theorem concreteThreeDimensionalOutfluxShortDuration_le_original
    (nu : Viscosity) :
    concreteThreeDimensionalOutfluxShortDuration nu ≤
      wholeRestartDuration (concreteThreeDimensionalSeed nu) := by
  unfold concreteThreeDimensionalOutfluxShortDuration
  have minLe := min_le_left
    (wholeRestartDuration (concreteThreeDimensionalSeed nu))
    (concreteThreeDimensionalOutfluxPersistenceTime nu)
  have minPos : 0 < min
      (wholeRestartDuration (concreteThreeDimensionalSeed nu))
      (concreteThreeDimensionalOutfluxPersistenceTime nu) :=
    lt_min (wholeRestartDuration_pos (concreteThreeDimensionalSeed nu))
      (concreteThreeDimensionalOutfluxPersistenceTime_pos nu)
  nlinarith

theorem concreteThreeDimensionalOutfluxShortDuration_lt_persistence
    (nu : Viscosity) :
    concreteThreeDimensionalOutfluxShortDuration nu <
      concreteThreeDimensionalOutfluxPersistenceTime nu := by
  unfold concreteThreeDimensionalOutfluxShortDuration
  have minLe := min_le_right
    (wholeRestartDuration (concreteThreeDimensionalSeed nu))
    (concreteThreeDimensionalOutfluxPersistenceTime nu)
  have persistencePos :=
    concreteThreeDimensionalOutfluxPersistenceTime_pos nu
  nlinarith

def concreteThreeDimensionalOutfluxShortReceipt
    (nu : Viscosity) :
    WholeContinuousMildSerrinReceipt nu concreteThreeDimensionalState
      (concreteThreeDimensionalOutfluxShortDuration nu) :=
  restrictWholeContinuousMildSerrinReceipt
    (concreteThreeDimensionalOutfluxShortDuration_pos nu)
    (concreteThreeDimensionalOutfluxShortDuration_le_original nu)
    (concreteThreeDimensionalReceipt nu)

def concreteThreeDimensionalOutfluxShortContact
    (nu : Viscosity) :=
  generatedPositiveWholeRestartContact
    (concreteThreeDimensionalOutfluxShortReceipt nu)

/-- Genuine nonplanar concrete current retaining the exact old `-1` outflux
row at its first actual contact. -/
def concreteThreeDimensionalOutfluxShortCurrent
    (nu : Viscosity) : GeneratedWholeRestartCurrent nu where
  initialState := concreteThreeDimensionalState
  duration := concreteThreeDimensionalOutfluxShortDuration nu
  receipt := concreteThreeDimensionalOutfluxShortReceipt nu
  contact := concreteThreeDimensionalOutfluxShortContact nu

/-- The transverse lift row survives on a source-selected positive window of
the same short receipt.  This is a physical coefficient lower bound, not a
clock or future-recurrence premise. -/
theorem concreteThreeDimensionalOutfluxShortReceipt_lift_persistence
    (nu : Viscosity) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ actual ∈ Icc (0 : Real)
          (concreteThreeDimensionalOutfluxShortDuration nu),
        actual < epsilon →
          (1 / 8 : Real) <
            complexCoordinateAmplitudeSq
              ((actualWholeProjectedTransversePath
                (concreteThreeDimensionalOutfluxShortReceipt nu) actual).1
                  concreteLiftWave) := by
  let liftMass : Real → Real := fun actual =>
    complexCoordinateAmplitudeSq
      ((actualWholeProjectedTransversePath
        (concreteThreeDimensionalOutfluxShortReceipt nu) actual).1
          concreteLiftWave)
  have stateContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath
          (concreteThreeDimensionalOutfluxShortReceipt nu) actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous
        (concreteThreeDimensionalOutfluxShortReceipt nu))
  have rowContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath
          (concreteThreeDimensionalOutfluxShortReceipt nu) actual).1
            concreteLiftWave :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 concreteLiftWave).continuous.comp stateContinuous
  have liftMassContinuous : Continuous liftMass := by
    exact complexCoordinateAmplitudeSq_continuous.comp rowContinuous
  have stateAtZero :
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalOutfluxShortReceipt nu) 0).1 =
          concreteThreeDimensionalState := by
    change
      (concreteThreeDimensionalOutfluxShortReceipt nu).wholePath
          (Set.projIcc (0 : Real)
            (concreteThreeDimensionalOutfluxShortDuration nu)
            (concreteThreeDimensionalOutfluxShortReceipt nu
              ).requestedTimePos.le 0) =
        concreteThreeDimensionalState
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalOutfluxShortReceipt nu).requestedTimePos.le
      ⟨le_rfl, (concreteThreeDimensionalOutfluxShortReceipt nu
        ).requestedTimePos.le⟩]
    exact (concreteThreeDimensionalOutfluxShortReceipt nu).wholePath_initial
  have liftMassZero : liftMass 0 = 1 / 4 := by
    dsimp only [liftMass]
    rw [stateAtZero, concreteThreeDimensionalState_lift]
    norm_num [complexCoordinateAmplitudeSq, complexCoordinateRealInner,
      Fin.sum_univ_succ]
  have neighborhoodOpen :
      IsOpen {actual | (1 / 8 : Real) < liftMass actual} :=
    isOpen_lt continuous_const liftMassContinuous
  have zeroMem : 0 ∈ {actual | (1 / 8 : Real) < liftMass actual} := by
    change (1 / 8 : Real) < liftMass 0
    rw [liftMassZero]
    norm_num
  obtain ⟨epsilon, epsilonPos, ballSubset⟩ :=
    Metric.isOpen_iff.mp neighborhoodOpen 0 zeroMem
  refine ⟨epsilon, epsilonPos, ?_⟩
  intro actual actualMem actualLt
  apply ballSubset
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg actualMem.1]
  exact actualLt

def concreteThreeDimensionalLiftPersistenceTime
    (nu : Viscosity) : Real :=
  Classical.choose
    (concreteThreeDimensionalOutfluxShortReceipt_lift_persistence nu)

theorem concreteThreeDimensionalLiftPersistenceTime_pos
    (nu : Viscosity) :
    0 < concreteThreeDimensionalLiftPersistenceTime nu :=
  (Classical.choose_spec
    (concreteThreeDimensionalOutfluxShortReceipt_lift_persistence nu)).1

theorem concreteThreeDimensionalLiftPersistenceTime_spec
    (nu : Viscosity)
    (actual : Real)
    (actualMem : actual ∈ Icc (0 : Real)
      (concreteThreeDimensionalOutfluxShortDuration nu))
    (actualLt : actual < concreteThreeDimensionalLiftPersistenceTime nu) :
    (1 / 8 : Real) <
      complexCoordinateAmplitudeSq
        ((actualWholeProjectedTransversePath
          (concreteThreeDimensionalOutfluxShortReceipt nu) actual).1
            concreteLiftWave) :=
  (Classical.choose_spec
    (concreteThreeDimensionalOutfluxShortReceipt_lift_persistence nu)).2
      actual actualMem actualLt

theorem concreteThreeDimensionalOutfluxShortCurrent_initial_active
    (nu : Viscosity) :
    NativeTemporalPositiveOutfluxAt
      (concreteThreeDimensionalOutfluxShortCurrent nu).contact.prefixReceipt
      concreteDepletingModes (1 / 2) := by
  intro actual actualMem
  have actualLeShort :
      actual ≤ concreteThreeDimensionalOutfluxShortDuration nu :=
    actualMem.2.trans
      (concreteThreeDimensionalOutfluxShortContact nu).time.2.2
  have actualLeOriginal :
      actual ≤ wholeRestartDuration (concreteThreeDimensionalSeed nu) :=
    actualLeShort.trans
      (concreteThreeDimensionalOutfluxShortDuration_le_original nu)
  have stateEq :
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalOutfluxShortCurrent nu
          ).contact.prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalReceipt nu) actual).1 := by
    change
      (concreteThreeDimensionalOutfluxShortCurrent nu
        ).contact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real)
            (concreteThreeDimensionalOutfluxShortCurrent nu).contact.time.1
            (concreteThreeDimensionalOutfluxShortCurrent nu
              ).contact.time_pos.le actual) =
        (concreteThreeDimensionalReceipt nu).wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration (concreteThreeDimensionalSeed nu))
            (concreteThreeDimensionalReceipt nu).requestedTimePos.le actual)
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalOutfluxShortCurrent nu
        ).contact.time_pos.le actualMem]
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalReceipt nu).requestedTimePos.le
      ⟨actualMem.1, actualLeOriginal⟩]
    rfl
  unfold nativeTemporalProjectedWholeEnstrophyPower
  rw [stateEq]
  exact (concreteThreeDimensionalOutfluxPersistenceTime_spec nu actual
    ⟨actualMem.1, actualLeOriginal⟩
    (lt_of_le_of_lt actualLeShort
      (concreteThreeDimensionalOutfluxShortDuration_lt_persistence nu))).le

/-- A final source-owned restriction keeps both the active outflux window and
the fixed nonzero lift row. -/
def concreteThreeDimensionalActiveLiftDuration
    (nu : Viscosity) : Real :=
  min (concreteThreeDimensionalOutfluxShortDuration nu)
      (concreteThreeDimensionalLiftPersistenceTime nu) / 2

theorem concreteThreeDimensionalActiveLiftDuration_pos
    (nu : Viscosity) :
    0 < concreteThreeDimensionalActiveLiftDuration nu := by
  unfold concreteThreeDimensionalActiveLiftDuration
  exact div_pos
    (lt_min (concreteThreeDimensionalOutfluxShortDuration_pos nu)
      (concreteThreeDimensionalLiftPersistenceTime_pos nu))
    (by norm_num)

theorem concreteThreeDimensionalActiveLiftDuration_le_outfluxShort
    (nu : Viscosity) :
    concreteThreeDimensionalActiveLiftDuration nu ≤
      concreteThreeDimensionalOutfluxShortDuration nu := by
  unfold concreteThreeDimensionalActiveLiftDuration
  have minLe := min_le_left
    (concreteThreeDimensionalOutfluxShortDuration nu)
    (concreteThreeDimensionalLiftPersistenceTime nu)
  have minPos : 0 < min
      (concreteThreeDimensionalOutfluxShortDuration nu)
      (concreteThreeDimensionalLiftPersistenceTime nu) :=
    lt_min (concreteThreeDimensionalOutfluxShortDuration_pos nu)
      (concreteThreeDimensionalLiftPersistenceTime_pos nu)
  nlinarith

theorem concreteThreeDimensionalActiveLiftDuration_lt_liftPersistence
    (nu : Viscosity) :
    concreteThreeDimensionalActiveLiftDuration nu <
      concreteThreeDimensionalLiftPersistenceTime nu := by
  unfold concreteThreeDimensionalActiveLiftDuration
  have minLe := min_le_right
    (concreteThreeDimensionalOutfluxShortDuration nu)
    (concreteThreeDimensionalLiftPersistenceTime nu)
  have persistencePos :=
    concreteThreeDimensionalLiftPersistenceTime_pos nu
  nlinarith

def concreteThreeDimensionalActiveLiftReceipt
    (nu : Viscosity) :
    WholeContinuousMildSerrinReceipt nu concreteThreeDimensionalState
      (concreteThreeDimensionalActiveLiftDuration nu) :=
  restrictWholeContinuousMildSerrinReceipt
    (concreteThreeDimensionalActiveLiftDuration_pos nu)
    (concreteThreeDimensionalActiveLiftDuration_le_outfluxShort nu)
    (concreteThreeDimensionalOutfluxShortReceipt nu)

def concreteThreeDimensionalActiveLiftContact
    (nu : Viscosity) :=
  generatedPositiveWholeRestartContact
    (concreteThreeDimensionalActiveLiftReceipt nu)

def concreteThreeDimensionalActiveLiftCurrent
    (nu : Viscosity) : GeneratedWholeRestartCurrent nu where
  initialState := concreteThreeDimensionalState
  duration := concreteThreeDimensionalActiveLiftDuration nu
  receipt := concreteThreeDimensionalActiveLiftReceipt nu
  contact := concreteThreeDimensionalActiveLiftContact nu

theorem concreteThreeDimensionalActiveLiftCurrent_initial_active
    (nu : Viscosity) :
    NativeTemporalPositiveOutfluxAt
      (concreteThreeDimensionalActiveLiftCurrent nu).contact.prefixReceipt
      concreteDepletingModes (1 / 2) := by
  intro actual actualMem
  have actualLeFinal :
      actual ≤ concreteThreeDimensionalActiveLiftDuration nu :=
    actualMem.2.trans
      (concreteThreeDimensionalActiveLiftContact nu).time.2.2
  have actualLeShort :
      actual ≤ concreteThreeDimensionalOutfluxShortDuration nu :=
    actualLeFinal.trans
      (concreteThreeDimensionalActiveLiftDuration_le_outfluxShort nu)
  have actualLeOriginal :
      actual ≤ wholeRestartDuration (concreteThreeDimensionalSeed nu) :=
    actualLeShort.trans
      (concreteThreeDimensionalOutfluxShortDuration_le_original nu)
  have stateEq :
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalActiveLiftCurrent nu
          ).contact.prefixReceipt actual).1 =
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalReceipt nu) actual).1 := by
    change
      (concreteThreeDimensionalActiveLiftCurrent nu
        ).contact.prefixReceipt.wholePath
          (Set.projIcc (0 : Real)
            (concreteThreeDimensionalActiveLiftCurrent nu).contact.time.1
            (concreteThreeDimensionalActiveLiftCurrent nu
              ).contact.time_pos.le actual) =
        (concreteThreeDimensionalReceipt nu).wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration (concreteThreeDimensionalSeed nu))
            (concreteThreeDimensionalReceipt nu).requestedTimePos.le actual)
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalActiveLiftCurrent nu
        ).contact.time_pos.le actualMem]
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalReceipt nu).requestedTimePos.le
      ⟨actualMem.1, actualLeOriginal⟩]
    rfl
  unfold nativeTemporalProjectedWholeEnstrophyPower
  rw [stateEq]
  exact (concreteThreeDimensionalOutfluxPersistenceTime_spec nu actual
    ⟨actualMem.1, actualLeOriginal⟩
    (lt_of_le_of_lt actualLeShort
      (concreteThreeDimensionalOutfluxShortDuration_lt_persistence nu))).le

theorem concreteThreeDimensionalActiveLiftCurrent_contact_liftMass_gt
    (nu : Viscosity) :
    (1 / 8 : Real) <
      complexCoordinateAmplitudeSq
        ((concreteThreeDimensionalActiveLiftCurrent nu).contact.physicalState
          concreteLiftWave) := by
  let actual :=
    (concreteThreeDimensionalActiveLiftContact nu).time.1
  have actualMem : actual ∈ Icc (0 : Real)
      (concreteThreeDimensionalOutfluxShortDuration nu) := by
    exact
      ⟨(concreteThreeDimensionalActiveLiftContact nu).time_pos.le,
        (concreteThreeDimensionalActiveLiftContact nu).time.2.2.trans
          (concreteThreeDimensionalActiveLiftDuration_le_outfluxShort nu)⟩
  have actualLt : actual <
      concreteThreeDimensionalLiftPersistenceTime nu :=
    (concreteThreeDimensionalActiveLiftContact nu).time.2.2.trans_lt
      (concreteThreeDimensionalActiveLiftDuration_lt_liftPersistence nu)
  have persisted :=
    concreteThreeDimensionalLiftPersistenceTime_spec
      nu actual actualMem actualLt
  have stateEq :
      (actualWholeProjectedTransversePath
        (concreteThreeDimensionalOutfluxShortReceipt nu) actual).1 =
      (concreteThreeDimensionalActiveLiftCurrent nu).contact.physicalState := by
    change
      (concreteThreeDimensionalOutfluxShortReceipt nu).wholePath
          (Set.projIcc (0 : Real)
            (concreteThreeDimensionalOutfluxShortDuration nu)
            (concreteThreeDimensionalOutfluxShortReceipt nu
              ).requestedTimePos.le actual) =
        (concreteThreeDimensionalActiveLiftReceipt nu).wholePath
          (concreteThreeDimensionalActiveLiftContact nu).time
    rw [Set.projIcc_of_mem
      (concreteThreeDimensionalOutfluxShortReceipt nu).requestedTimePos.le
      actualMem]
    rfl
  rwa [stateEq] at persisted

theorem concreteThreeDimensionalActiveLiftCurrent_contact_wholeMass_gt
    (nu : Viscosity) :
    (1 / 8 : Real) <
      wholeVorticityEuclideanMass
        (concreteThreeDimensionalActiveLiftCurrent nu).contact.physicalState := by
  have singleLe :
      complexCoordinateAmplitudeSq
          ((concreteThreeDimensionalActiveLiftCurrent nu).contact.physicalState
            concreteLiftWave) ≤
        wholeVorticityEuclideanMass
          (concreteThreeDimensionalActiveLiftCurrent nu).contact.physicalState := by
    simpa [finiteStateVorticityCoefficientEnstrophy] using
      (finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        {concreteLiftWave}
        (concreteThreeDimensionalActiveLiftCurrent nu).contact.physicalState)
  exact
    (concreteThreeDimensionalActiveLiftCurrent_contact_liftMass_gt nu).trans_le
      singleLe

/-! ## Fixed final-mouth candidate -/

/-- Source-selected viscosity below the fixed half-critical scale.  Its value
is computed from the generated lattice constant; no viscosity or smallness
parameter remains in the public mouth. -/
def concreteCounterexampleViscosity : Viscosity where
  coeff := Real.sqrt criticalEnstrophyLatticeConstant / 100
  coeff_pos := by
    exact div_pos
      (Real.sqrt_pos.2 criticalEnstrophyLatticeConstant_pos)
      (by norm_num)

/-- Genuine nonplanar source current at the selected viscosity.  Its receipt,
contact and restart compiler are all generated internally. -/
def concreteCounterexampleInitial :
    GeneratedWholeRestartCurrent concreteCounterexampleViscosity :=
  concreteThreeDimensionalActiveLiftCurrent
    concreteCounterexampleViscosity

theorem concreteCounterexampleInitial_initial_active :
    NativeTemporalPositiveOutfluxAt
      concreteCounterexampleInitial.contact.prefixReceipt
      concreteDepletingModes (1 / 2) :=
  concreteThreeDimensionalActiveLiftCurrent_initial_active
    concreteCounterexampleViscosity

/-- The selected viscosity and retained lift row put the first actual contact
strictly on the half-critical side.  Thus the concrete candidate cannot fall
into the existing initial-smallness/global-time absorption theorem. -/
theorem concreteCounterexampleInitial_halfCriticalCrossed :
    wholeRestartHalfCriticalCrossed concreteCounterexampleInitial 0 := by
  have constantPos : 0 < criticalEnstrophyLatticeConstant :=
    criticalEnstrophyLatticeConstant_pos
  have viscositySquare :
      concreteCounterexampleViscosity.coeff ^ 2 =
        criticalEnstrophyLatticeConstant / 10000 := by
    change
      (Real.sqrt criticalEnstrophyLatticeConstant / 100) ^ 2 =
        criticalEnstrophyLatticeConstant / 10000
    rw [div_pow, Real.sq_sqrt constantPos.le]
    norm_num
  have piSqLt : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have weightedPiSqLt :
      criticalEnstrophyLatticeConstant * Real.pi ^ 2 <
        criticalEnstrophyLatticeConstant * 16 :=
    mul_lt_mul_of_pos_left piSqLt constantPos
  have clockSideLt :
      (1 / 2 : Real) * concreteCounterexampleViscosity.coeff ^ 2 *
          (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant * (1 / 8 : Real) := by
    rw [viscositySquare]
    nlinarith
  have massLower :
      (1 / 8 : Real) <
        wholeVorticityEuclideanMass
          concreteCounterexampleInitial.contact.physicalState := by
    simpa only [concreteCounterexampleInitial] using
      concreteThreeDimensionalActiveLiftCurrent_contact_wholeMass_gt
        concreteCounterexampleViscosity
  unfold wholeRestartHalfCriticalCrossed
  rw [run_zero]
  exact clockSideLt.trans
    (mul_lt_mul_of_pos_left massLower constantPos)

/-- The concrete outflux is an installed coordinate of the fixed original
boundary root, not a sibling effect source. -/
def concreteCounterexamplePositiveOutfluxRecognition :
    SourceNativeEffectDynamicalRecognitionAt
      (boundaryFinalLivingRoot concreteCounterexampleInitial) where
  effectLaw := boundaryPositiveOutfluxClosureLaw
    concreteCounterexampleInitial concreteDepletingModes (1 / 2)
  installation := boundaryPositiveOutfluxInstallation
    concreteCounterexampleInitial concreteDepletingModes (1 / 2)

private def concreteCounterexampleInitialVisit :
    SourceNativeTemporalVisitAt
      (boundaryFinalLivingRoot concreteCounterexampleInitial
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (boundaryFinalLivingRoot concreteCounterexampleInitial
    ).toAuthoritativeRoot.toRoot.initialVisit

private def concreteCounterexampleInitialActive :
    BoundaryPositiveOutfluxActiveAt concreteCounterexampleInitial
      concreteDepletingModes (1 / 2)
      ((boundaryPositiveOutfluxEventVocabulary
        concreteCounterexampleInitial concreteDepletingModes).emit
          (boundaryEmitted concreteCounterexampleInitial (.finite 0))) :=
  .finite 0
    (generatedWholeRestartNativeActualOccurrence
      concreteCounterexampleInitial 0)
    concreteCounterexampleInitial_initial_active

private theorem concreteCounterexampleInitial_classify_eq :
    (boundaryPositiveOutfluxClosureLaw concreteCounterexampleInitial
      concreteDepletingModes (1 / 2)).vocabulary.classify
        ((boundaryPositiveOutfluxEventVocabulary
          concreteCounterexampleInitial concreteDepletingModes).emit
            (boundaryEmitted concreteCounterexampleInitial (.finite 0))) =
      .inl concreteCounterexampleInitialActive := by
  classical
  change
    (if witness : Nonempty
          (BoundaryPositiveOutfluxActiveAt concreteCounterexampleInitial
            concreteDepletingModes (1 / 2)
            ((boundaryPositiveOutfluxEventVocabulary
              concreteCounterexampleInitial concreteDepletingModes).emit
                (boundaryEmitted concreteCounterexampleInitial (.finite 0))))
      then Sum.inl witness.some else Sum.inr _) =
        Sum.inl concreteCounterexampleInitialActive
  rw [dif_pos ⟨concreteCounterexampleInitialActive⟩]
  congr
  exact Subsingleton.elim _ _

private def concreteCounterexampleInitialSourceAuthority :
    concreteCounterexamplePositiveOutfluxRecognition.CausalEntryAuthorityAt
      concreteCounterexampleInitialVisit
      (boundaryFiniteEntry concreteCounterexampleInitial) :=
  ((SourceNativeEffectDynamicalRecognitionAt.CausalEntryAuthorityAt.generatedFromInitial?
      concreteCounterexamplePositiveOutfluxRecognition
      (boundaryFiniteEntry concreteCounterexampleInitial)
      .initial).get (by rfl)).2

/-- Initial actual outflux outcome generated at the exact first visit of the
fixed boundary root. -/
def concreteCounterexampleInitialRootedOutflux :
    concreteCounterexamplePositiveOutfluxRecognition.RootedActiveOutcomeAt
      concreteCounterexampleInitialVisit :=
  concreteCounterexamplePositiveOutfluxRecognition.generatedRootedActiveAtVisit
    concreteCounterexampleInitialVisit
    concreteCounterexampleInitialActive
    concreteCounterexampleInitial_classify_eq
    concreteCounterexampleInitialSourceAuthority

/-- The initial installed outcome immediately generates its canonical causal
closure (`next` or same-row finite cut) inside the original root. -/
def concreteCounterexampleInitialCausalClosure :
    concreteCounterexampleInitialRootedOutflux.CausalClosureAt :=
  concreteCounterexampleInitialRootedOutflux.generatedCausalClosure

/-- Direct conditional consumer identifying the last source theorem.  This is
not the final public mouth: injectivity must be generated by the concrete
source and eliminated before promotion. -/
theorem concreteCounterexample_contactTime_summable_of_scale_injective
    (injective : Function.Injective
      (restartCoefficientCeiling concreteCounterexampleInitial)) :
    Summable fun n =>
      (run concreteCounterexampleInitial n).contact.time.1 :=
  contactTime_summable_of_restartCoefficientCeiling_injective
    concreteCounterexampleInitial injective

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartConcreteThreeDimensionalSource
end NavierStokes
end SaturationMonoid
