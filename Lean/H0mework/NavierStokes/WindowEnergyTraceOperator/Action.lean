import H0mework.NavierStokes.WindowEnergyTraceOperator.Kernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceOperatorAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest
open NativeWindowOperatorGreen NativeResolventAdjoint
open NativeWindowAugmentedFixedOperator (spectral rowRead)
open NativeWindowTraceOperator (test test_pairing jointTest jointTest_pairing)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem row_pairing (x y : ComplexCoordinateVector) :
    (∑ i : Coordinate,inner ℝ (x i) (y i))=complexCoordinateRealInner x y := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro i _
  change (y i*star (x i)).re=_
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectral_laplacian (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (x y : physicalSpace M) : spectral nu M M x y=pairing M x y+
      nu.coeff*pairing M x (laplacian M zero closed nu y) := by
  rw [pairing_eq,pairing_eq]
  change (∑ wave ∈ M,∑ i : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave)*
    inner ℝ (x.1 wave i) (y.1 wave i))=_
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro wave inside
  rw [← Finset.mul_sum,row_pairing,laplacian_row]
  simp only [complexCoordinateRealInner,Pi.smul_apply,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.mul_im,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem jointTest_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ)
    (zero : 0∉M) (closed : FiniteModeNegClosed M) (x y : physicalSpace M) :
    pairing M x (jointTest seed time M F radius y)=
      ∑ i : Coordinate,inner ℝ (NativeWindowTraceEnergy.relative seed F radius time)
        (physical (evaluate M F i x*evaluate M F i y))-
          nu.coeff*pairing M x (laplacian M zero closed nu y) := by
  rw [jointTest_pairing,spectral_laplacian M zero closed]
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem field_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowTraceOperator.field seed (step.2.clockAdvance+time) F radius=NativeWindowTraceOperator.field step.1 time F radius := by
  have same := congrArg Prod.fst (NativeWindowTraceEnergy.whole_next seed F radius step generated time nonnegative)
  change NativeWindowTraceEnergy.relative seed F radius (step.2.clockAdvance+time)=NativeWindowTraceEnergy.relative step.1 F radius time at same
  simp only [NativeWindowTraceOperator.field_original,same]

theorem test_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (M L F : Finset IntegerWavevector) (radius : ℕ) :
    test seed (step.2.clockAdvance+time) M L F radius=test step.1 time M L F radius := by
  simp only [test,NativeWindowTraceOperator.form,NativeWindowTraceOperator.matrixForm,NativeWindowTraceOperator.read,
    field_next seed step generated time nonnegative]

theorem jointTest_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (M F : Finset IntegerWavevector) (radius : ℕ) :
    jointTest seed (step.2.clockAdvance+time) M F radius=jointTest step.1 time M F radius := by
  simp only [jointTest,test_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceOperatorAction
