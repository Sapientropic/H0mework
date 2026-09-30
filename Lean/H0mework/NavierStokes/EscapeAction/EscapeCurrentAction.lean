import H0mework.NavierStokes.EscapeAction.EscapePairedCurrent

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeEscapeCurrentAction

open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeRecoveryCoverage NativeRecoveryEscapeCarrier NativeRecoveryEscapeStress NativeRecoveryEscapeMomentum
open NativePairedCurrentFourier NativeEscapePairedCurrent

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def currentCurve (escape : SourceActionEscape receipt point) (index : ℕ)
    (direction : Fin 4) (wave : IntegerWavevector) (actual : ℝ) : ℂ :=
  mFourierCoeff (fun place => (field (wholeBiotSavartVelocityState
    ((ledger.family.stage (radius escape index)).trajectory actual)) direction place : ℂ)) wave

theorem currentCurve_sample (escape : SourceActionEscape receipt point) (index : ℕ)
    (direction : Fin 4) (wave : IntegerWavevector) :
    currentCurve escape index direction wave (escape.sample index) = actual escape index direction wave := rfl

theorem currentCurve_spatial (escape : SourceActionEscape receipt point) (index : ℕ)
    (direction : Fin 3) (wave : IntegerWavevector) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    currentCurve escape index direction.succ wave time = biotSavartVelocityCoefficient wave
      ((ledger.family.stage (radius escape index)).trajectory time wave) direction :=
  spatial_fourier _ (NativePhysicalSource.velocity_reality _
    ((ledger.family.stage (radius escape index)).physical time inside).2.2.2) direction wave

def finiteMomentum (escape : SourceActionEscape receipt point) (index : ℕ) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  biotSavartVelocityCoefficient wave
    (finiteStateVorticityGenerator (wholeRestartModes (radius escape index)) nu.coeff (state escape index) wave)

theorem spatial_current_hasDerivAt (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (direction : Fin 3) (wave : IntegerWavevector) :
    HasDerivAt (currentCurve escape index direction.succ wave) (finiteMomentum escape index wave direction) (escape.sample index) := by
  have original := ((ledger.family.stage (radius escape index)).physical _ (sampleTime escape pointLe index).2).1
  have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt _ original
  have velocity := ((biotSavartVelocityCLM wave).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ row
  have coordinate := (ContinuousLinearMap.proj direction : ComplexCoordinateVector →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt _ velocity
  change HasDerivAt (fun time => biotSavartVelocityCoefficient wave
      ((ledger.family.stage (radius escape index)).trajectory time wave) direction)
    (finiteMomentum escape index wave direction) (escape.sample index) at coordinate
  apply coordinate.congr_of_eventuallyEq
  have positive : 0 < escape.sample index := escape.anchor_inside.1.trans
    ((le_max_left _ _).trans_lt (escape.sample_inside index).1)
  have before : escape.sample index < 1 := (escape.sample_inside index).2.trans_le pointLe
  filter_upwards [Ioo_mem_nhds positive before] with time inside
  exact currentCurve_spatial escape index direction wave time ⟨inside.1.le, inside.2.le⟩

theorem finiteMomentum_eq_actual_of_mem (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (index : ℕ) (wave : IntegerWavevector) (inside : wave ∈ wholeRestartModes (radius escape index)) :
    finiteMomentum escape index wave = actualMomentum escape index wave := by
  have physical := (ledger.family.stage (radius escape index)).physical _ (sampleTime escape pointLe index).2
  have supported : ∀ frequency ∉ wholeRestartModes (radius escape index), state escape index frequency = 0 := physical.2.1
  have same := finiteModes_generator_eq_wholeTangent_sub_omittedDefect
    (wholeRestartModes (radius escape index)) nu.coeff (state escape index) supported wave
  simp only [finiteModesOmittedNonlinearDefectAt, if_pos inside, sub_zero] at same
  exact congrArg (biotSavartVelocityCoefficient wave) same

theorem finiteMomentum_tendsto (stress : StressAt escape) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    Tendsto (fun index => finiteMomentum escape (stress.refinement index) wave) atTop (𝓝 (momentum stress pointLe wave)) := by
  have original := tendsto_pi_nhds.mp (momentum_tendsto stress pointLe) wave
  apply original.congr'
  by_cases nonzero : wave ≠ 0
  · have included : ∀ᶠ index in atTop, wave ∈ wholeRestartModes (radius escape (stress.refinement index)) :=
      (escape.radius_tendsto.comp stress.refinement_strict.tendsto_atTop)
        (nonzero_integerWave_eventually_mem_puncturedFrequencyCube wave nonzero)
    filter_upwards [included] with index inside
    exact (finiteMomentum_eq_actual_of_mem escape pointLe (stress.refinement index) wave inside).symm
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    exact Eventually.of_forall fun _ => by simp [finiteMomentum, actualMomentum]

theorem current_time_derivative_tendsto (stress : StressAt escape) (pointLe : point ≤ 1)
    (direction : Fin 3) (wave : IntegerWavevector) :
    Tendsto (fun index => deriv (currentCurve escape (stress.refinement index) direction.succ wave)
      (escape.sample (stress.refinement index))) atTop (𝓝 (momentum stress pointLe wave direction)) := by
  have original := (continuous_apply direction).tendsto _ |>.comp (finiteMomentum_tendsto stress pointLe wave)
  apply original.congr'
  exact Eventually.of_forall fun index => (spatial_current_hasDerivAt escape pointLe (stress.refinement index) direction wave).deriv.symm

theorem source_current_time_derivative_tendsto (initial : GeneratedWholeRestartCurrent nu) (point : ℝ)
    (inside : point ∈ Ioo (0 : ℝ) (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1)
    (uncovered : point ∉ NativeRecoveryAEWindows.regularSet (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1) (direction : Fin 3) (wave : IntegerWavevector) :
    let escape := sourceUncoveredAction initial point inside uncovered
    let stress := sourceStress initial point inside uncovered
    let pointLe := inside.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2
    Tendsto (fun index => deriv (currentCurve escape (stress.refinement index) direction.succ wave)
      (escape.sample (stress.refinement index))) atTop (𝓝 (momentum stress pointLe wave direction)) :=
  current_time_derivative_tendsto _ _ direction wave

end
end SaturationMonoid.NavierStokes.NativeEscapeCurrentAction
