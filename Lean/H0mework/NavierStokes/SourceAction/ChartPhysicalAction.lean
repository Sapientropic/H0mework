import H0mework.NavierStokes.SourceAction.FinitePrefixChart

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeTimeChartPhysicalAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderSynthesis NativePhysicalContinuous NativeMixedTimeSpace NativeTimeJetCarrier
open NativeReceiptTimeProfile NativeStressSource

noncomputable section

theorem spatialField_real_smul (coefficient : ℝ) (velocity : ComplexVorticityHilbertState) (point : PhysicalSpace) :
    spatialField (coefficient • velocity) point = coefficient • spatialField velocity point := by
  have scalar (coordinate : Coordinate) : scalarContinuous (coefficient • velocity) coordinate =
      coefficient • scalarContinuous velocity coordinate := by
    unfold scalarContinuous
    rw [← tsum_const_smul'']
    apply tsum_congr
    intro wave
    change (coefficient • velocity wave coordinate) • UnitAddTorus.mFourier wave =
      coefficient • (velocity wave coordinate • UnitAddTorus.mFourier wave)
    exact smul_assoc coefficient (velocity wave coordinate) (UnitAddTorus.mFourier wave)
  ext coordinate
  change (scalarContinuous (coefficient • velocity) coordinate (circlePoint point)).re =
    coefficient * (scalarContinuous velocity coordinate (circlePoint point)).re
  rw [scalar]
  simp only [ContinuousMap.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
  {receipt : WholeContinuousMildSerrinReceipt nu initial duration}

theorem receipt_physical_hasDerivWithinAt (window : Window receipt) (actual : ℝ)
    (inside : actual ∈ Icc window.first window.last) (point : PhysicalSpace) :
    HasDerivWithinAt (fun time => spatialField (NativeReceiptSpacetime.velocity receipt time) point)
      (spatialField (NativeReceiptSpacetime.timeJet window 1 actual) point)
      (Icc window.first window.last) actual := by
  have source := profileWord_hasDerivWithinAt (jets window 0) (jets window 1) (jets_evolve window 0)
    0 (fun empty => Fin.elim0 empty) point
    ⟨NativeReceiptSpacetime.inverse window actual, NativeReceiptSpacetime.inverse_mem window actual inside⟩
  simp only [profileWord, profileField, iteratedFDeriv_zero_apply] at source
  have coordinate : HasDerivWithinAt (NativeReceiptSpacetime.inverse window) (factor window)⁻¹
      (Icc window.first window.last) actual := by
    convert! (((hasDerivAt_id actual).sub_const window.first).div_const (factor window)).hasDerivWithinAt using 1
    simp only [one_div]
  have written := source.scomp actual coordinate (NativeReceiptSpacetime.inverse_mem window)
  rw [NativeReceiptSpacetime.timeJet, pow_one, spatialField_real_smul]
  exact written.congr_of_mem
    (fun time member => by
      simp only [Function.comp_apply, profileWord, profileField, iteratedFDeriv_zero_apply]
      rw [NativeReceiptSpacetime.velocity_read window time member]) inside

theorem receipt_physical_hasDerivAt (window : Window receipt) (actual : ℝ)
    (inside : actual ∈ Ioo window.first window.last) (point : PhysicalSpace) :
    HasDerivAt (fun time => spatialField (NativeReceiptSpacetime.velocity receipt time) point)
      (spatialField (NativeReceiptSpacetime.timeJet window 1 actual) point) actual :=
  (receipt_physical_hasDerivWithinAt window actual ⟨inside.1.le, inside.2.le⟩ point).hasDerivAt
    (Icc_mem_nhds inside.1 inside.2)

open NativeFinitePrefixTimeChart

theorem source_physical_hasDerivAt (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    HasDerivAt (fun sample => spatialField (velocity index sample) point)
      (spatialField (velocityRate index parameter) point) parameter := by
  rw [velocityRate, spatialField_real_smul]
  exact (receipt_physical_hasDerivAt (window index) (physicalTime index parameter)
    (physicalTime_mem index parameter) point).scomp parameter (physicalTime_hasDerivAt index parameter)

theorem source_physical_clock_hasDerivAt (index : ℕ) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (NativeFinitePrefixTimeChart.duration index)) (point : PhysicalSpace) :
    HasDerivAt (fun time => spatialField (NativeReceiptSpacetime.velocity (NativeFinitePrefixTimeChart.receipt index) time) point)
      (spatialField (NativeReceiptSpacetime.timeJet (window index) 1 actual) point) actual :=
  receipt_physical_hasDerivAt (window index) actual inside point

theorem source_physical_deriv_unscale (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    (clockRate index parameter)⁻¹ • deriv (fun sample => spatialField (velocity index sample) point) parameter =
      spatialField (NativeReceiptSpacetime.timeJet (window index) 1 (physicalTime index parameter)) point := by
  rw [(source_physical_hasDerivAt index parameter point).deriv, velocityRate, spatialField_real_smul,
    smul_smul, inv_mul_cancel₀ (clockRate_pos index parameter).ne', one_smul]

theorem source_physical_action_row (index : ℕ) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (NativeFinitePrefixTimeChart.duration index)) (wave : IntegerWavevector) :
    NativeReceiptSpacetime.timeJet (window index) 1 actual wave =
      receiptMomentumAction (NativeFinitePrefixTimeChart.receipt index) wave actual :=
  NativeReceiptSpacetime.timeJet_one_row (window index) actual ⟨inside.1.le, inside.2.le⟩ wave

end
end SaturationMonoid.NavierStokes.NativeTimeChartPhysicalAction
