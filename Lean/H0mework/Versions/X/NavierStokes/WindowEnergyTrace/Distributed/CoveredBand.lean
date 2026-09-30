import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Lyapunov

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeTraceCoveredBand
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeWindowHighTransportProduct (Z)
noncomputable section
variable {nu : Viscosity}

private theorem product_zero_left (v : Z) : NativeWindowHighTransportProduct.product 0 v=0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero,mul_zero,zero_mul] using
    NativeWindowHighTransportProduct.product_bound 0 v

theorem projected_high_zero (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (radius : ℕ) (covered : F⊆integerWaveFrequencyCube radius)
    (time : ℝ) : complexSharpSupportProjection F
      (NativeWindowHighPressureCurrent.value seed radius time)=0 := by
  apply lp.ext
  funext k
  by_cases inside : k∈F
  · rw [complexSharpSupportProjection_apply,if_pos inside,
      NativeWindowHighPressureCurrent.value,NativeWindowPressureLowInputs.high_row,
      if_pos (covered inside)]
    rfl
  · simp only [complexSharpSupportProjection_apply,if_neg inside]
    rfl

theorem transport_current_zero (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (radius : ℕ) (covered : F⊆integerWaveFrequencyCube radius)
    (time : ℝ) : NativeWindowHighTransportSource.current seed F radius time=0 := by
  have high : NativeWindowHighTransportSource.highVelocity seed F radius time=0 := by
    rw [← NativeWindowHighPressureCurrent.projected_value_original]
    exact projected_high_zero seed F radius covered time
  funext j output input
  simp only [NativeWindowHighTransportSource.current,NativeWindowHighTransportSource.component,
    high,map_zero,product_zero_left,neg_zero,Pi.zero_apply]

theorem pressure_current_zero (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (radius : ℕ) (covered : F⊆integerWaveFrequencyCube radius)
    (time : ℝ) : NativeWindowHighPressureCurrent.current seed F radius time=0 := by
  funext j output input
  simp only [NativeWindowHighPressureCurrent.current,NativeWindowHighPressureCurrent.rawCurrent,
    NativeWindowHighPressureCurrent.product,projected_high_zero seed F radius covered time,
    map_zero,product_zero_left,neg_zero,ite_self,add_zero,Pi.zero_apply]

theorem correction_zero (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (radius : ℕ) (covered : F⊆integerWaveFrequencyCube radius)
    (order : ℕ) (time : ℝ) (output input : Coordinate) :
    NativeWindowJointNormalForm.correctionJet seed F radius order time output input=0 := by
  have first : NativeWindowHighTransportSource.window seed F radius order time=0 := by
    simp only [NativeWindowHighTransportSource.window,
      transport_current_zero seed F radius covered,smul_zero,integral_zero]
  have last : NativeWindowHighPressureResolvent.window seed F radius order time=0 := by
    simp only [NativeWindowHighPressureResolvent.window,
      pressure_current_zero seed F radius covered,smul_zero,integral_zero]
  simp only [NativeWindowJointNormalForm.correctionJet,
    NativeWindowHighTransportResolvent.primitive,NativeWindowHighPressureResolvent.primitive,
    first,last,map_zero,sub_zero]

theorem trace_original (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (radius : ℕ) (covered : F⊆integerWaveFrequencyCube radius)
    (time : ℝ) : NativeWindowTraceOperator.field seed time F radius=
      NativeWindowStressHeatSource.physical (NativeWindowTraceGradient.traceStress seed time F) := by
  rw [NativeWindowTraceOperator.field_split]
  have same : NativeWindowTraceEnergy.correction seed F radius time=0 := by
    unfold NativeWindowTraceEnergy.correction
    apply Finset.sum_eq_zero
    intro i _
    rw [← NativeWindowJointNormalForm.correctionJet_zero]
    exact correction_zero seed F radius covered 0 time i i
  rw [same,add_zero]

theorem cube_trace_original (seed : GeneratedWholeRestartCurrent nu)
    (low outerRadius : ℕ) (time : ℝ) :
    NativeWindowTraceOperator.field seed time (integerWaveFrequencyCube outerRadius)
      (max low outerRadius)=NativeWindowStressHeatSource.physical
        (NativeWindowTraceGradient.traceStress seed time (integerWaveFrequencyCube outerRadius)) := by
  apply trace_original
  intro wave inside
  rw [integerWaveFrequencyCube,Fintype.mem_piFinset] at inside ⊢
  intro coordinate
  have member := inside coordinate
  rw [Finset.mem_Icc] at member ⊢
  have larger : (outerRadius : ℤ) ≤ max low outerRadius := by
    exact_mod_cast le_max_right low outerRadius
  constructor <;> omega

end
end SaturationMonoid.NavierStokes.NativeTraceCoveredBand
