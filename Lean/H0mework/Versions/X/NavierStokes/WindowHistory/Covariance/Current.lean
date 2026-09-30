import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalCurrent
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Covariance

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceCurrent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeWholeH1Mixed (modes)
open NativePhysicalFourier (Torus)
open NativeWindowHistoryCreationCovariance (trace covariance)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowHistoryMeanAction (meanValue)
noncomputable section
variable {nu : Viscosity}

theorem read_cube (M : ℕ) (i : Coordinate) (v : NativeCompleteStressAction.FullSpace) :
    NativeWindowFiniteGramFourier.read (integerWaveFrequencyCube M) i v=
      NativeWindowFiniteGramFourier.read (modes M) i v := by
  have same : complexSharpSupportProjection (integerWaveFrequencyCube M) (NativeEndpointVelocityCarrier.wholeVelocity v.fst)=
      complexSharpSupportProjection (modes M) (NativeEndpointVelocityCarrier.wholeVelocity v.fst) := by
    apply lp.ext
    funext k
    by_cases zero:k=0
    · subst k
      simp only [complexSharpSupportProjection_apply,NativeEndpointVelocityCarrier.wholeVelocity_zero,ite_self]
    · simp only [complexSharpSupportProjection_apply]
      have member:k∈modes M ↔ k∈integerWaveFrequencyCube M:=by
        change k∈(integerWaveFrequencyCube M).erase 0 ↔ _
        simp [zero]
      simp only [member]
  apply ContinuousMap.ext
  intro x
  rw [NativeWindowFiniteGramFourier.read_original,NativeWindowFiniteGramFourier.read_original,same]

theorem stress_cube (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (i j : Coordinate) :
    NativeWindowFiniteGramFourier.stress seed time (integerWaveFrequencyCube M) i j=
      NativeWindowFiniteGramFourier.stress seed time (modes M) i j := by
  unfold NativeWindowFiniteGramFourier.stress NativeWindowFiniteGramFourier.pairRead
  simp only [read_cube]

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) : ℝ :=
  (NativeWindowAbsoluteTimePhysicalCurrent.current seed M time 0 x).re

theorem gram (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    value seed M time x=2+(∑i : Coordinate,NativeWindowFiniteGramFourier.stress seed time (modes M) i i x)/8 := by
  simp only [value,NativeWindowAbsoluteTimePhysicalCurrent.source_current,Fin.cases_zero,
    Complex.add_re,Complex.div_ofNat_re,Complex.re_ofNat,Complex.re_sum,Complex.ofReal_re]

theorem covariance_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) (x : Torus) :
    value seed M time x=2+(∑i : Coordinate,(evaluate (modes M) (modes M) i (meanValue seed M time) x)^2)/8+
      trace seed M time x/8 := by
  have each (i : Coordinate):=NativeWindowHistoryCreationCovariance.covariance_diagonal seed M time nonnegative i x
  simp only [stress_cube] at each
  have all:=congrArg (fun f : Coordinate → ℝ => ∑i,f i) (funext each)
  rw [gram,NativeWindowHistoryCreationCovariance.trace_matrix]
  simp only [Finset.sum_sub_distrib,ContinuousMap.sum_apply] at all ⊢
  linarith only [all]

theorem lower (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) (x : Torus) :
    2≤value seed M time x ∧ (1+trace seed M time x)/8≤value seed M time x := by
  rw [covariance_split seed M time nonnegative x]
  have mean0 : 0≤∑i : Coordinate,(evaluate (modes M) (modes M) i (meanValue seed M time) x)^2:=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have trace0:=NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time x
  constructor <;> linarith only [mean0,trace0]

theorem inverse_cost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) (x : Torus) (a : ℝ) (a0 : 0≤a) :
    a/value seed M time x≤8*(a/(1+trace seed M time x)) := by
  have positive : 0<1+trace seed M time x:=by
    linarith [NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time x]
  have paid:=lower seed M time nonnegative x
  have value0 : 0<value seed M time x:=by linarith [paid.1]
  rw [div_le_iff₀ value0]
  apply (mul_le_mul_iff_right₀ positive).mp
  have cancel : (1+trace seed M time x)*(8*(a/(1+trace seed M time x))*value seed M time x)=
      8*a*value seed M time x:=by field_simp
  rw [cancel]
  nlinarith only [mul_le_mul_of_nonneg_left paid.2 a0]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (x : Torus) : value seed M (step.2.clockAdvance+time) x=value step.1 M time x := by
  simp only [gram,NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceCurrent
