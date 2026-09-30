import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalMatter
import H0mework.Versions.X.NavierStokes.WindowStressHeat.Fourier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalRead
open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativePhysicalContinuous NativeEndpointVelocityCarrier
open NativeWholeResolvent (wholePhysical)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowAbsoluteTimeFourier (Fiber field evaluation)
open NativeWindowFiniteGramFourier (complexRead read)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance physicalHaar : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs AddCircle.haarAddCircle.IsAddHaarMeasure
variable {nu : Viscosity}

theorem complexRead_real (F : Finset IntegerWavevector)
    (state : NativeCompleteStressAction.FullSpace)
    (reality : FiniteStateFourierReality (complexSharpSupportProjection F (wholeVelocity state.fst)))
    (i : Coordinate) (x : Torus) : complexRead F i state x=(read F i state x : ℂ) := by
  have amplitude : Summable (NativeFullOrderAction.amplitude (complexSharpSupportProjection F (wholeVelocity state.fst))) :=
    NativeCorrectionPhysical.finite_amplitude_paid F (wholeVelocity state.fst)
  have equal : (complexRead F i state : Torus → ℂ)=ᵐ[volume] fun x => (read F i state x : ℂ) := by
    filter_upwards [scalarContinuous_ae _ i amplitude,scalarField_real _ reality i] with x continuous real
    change complexRead F i state x=((complexRead F i state x).re : ℂ)
    rw [NativeWindowFiniteGramFourier.complexRead_original,← continuous]
    apply Complex.ext
    · rfl
    · simpa using real
  exact congrFun (Measure.eq_of_ae_eq equal (complexRead F i state).continuous
    (Complex.continuous_ofReal.comp (read F i state).continuous)) x

abbrev Lag := Lp ℂ 2 averageMeasure

def scalarMap (time : ℝ) : Lag →ₗᵢ[ℂ] Fiber where
  toFun := NativeWindowAbsoluteTimeIsometry.map ℂ time
  map_add' u v := (NativeWindowAbsoluteTimeIsometry.map ℂ time).map_add u v
  map_smul' c v := NativeWindowAbsoluteTimeIsometry.map_scalar ℂ time c v
  norm_map' := (NativeWindowAbsoluteTimeIsometry.map ℂ time).norm_map

def lagField (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (i : Coordinate) (x : Torus) : Lag :=
  (evaluation F i x).compLpL 2 averageMeasure (NativeWindowTraceWholeHistory.history seed time)

theorem field_map (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (i : Coordinate) (x : Torus) :
    field F i (NativeWindowAbsoluteTimeSource.history seed time) x=scalarMap time (lagField seed F time i x) := by
  rw [NativeWindowAbsoluteTimeFourier.field_evaluation]
  have natural:=NativeWindowAbsoluteTimeIsometry.naturality wholePhysical (evaluation F i x) time
    (NativeWindowTraceWholeHistory.history seed time)
  rw [NativeWindowAbsoluteTimeBridge.source_map] at natural
  exact natural.symm

theorem evaluation_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (s : ℝ) (i : Coordinate) (x : Torus) :
    evaluation F i x (NativeWindowTraceWholeHistory.original seed s)=complexRead F i (NativeUnifiedCompleteSource.source seed s) x := by
  simp only [evaluation,complexRead,sum_apply,ContinuousMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,ContinuousMap.smul_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  change mFourier k x*wholeVelocity (NativeUnifiedCompleteSource.source seed s).fst k i=
    wholeVelocity (NativeUnifiedCompleteSource.source seed s).fst k i*mFourier k x
  ring

theorem lagField_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (i : Coordinate) (x : Torus) :
    lagField seed F time i x=ᵐ[averageMeasure] fun lag => complexRead F i (NativeUnifiedCompleteSource.source seed (time-lag)) x := by
  filter_upwards [(evaluation F i x).coeFn_compLpL (NativeWindowTraceWholeHistory.history seed time),
    NativeWindowTraceWholeHistory.history_ae seed time] with lag first original
  change lagField seed F time i x lag=_ at first
  rw [first,original]
  exact evaluation_original seed F (time-lag) i x

theorem background_map (time : ℝ) : NativeWindowAbsoluteTimePhysicalMatter.background time=
    scalarMap time (Lp.constL 2 averageMeasure ℂ (1 : ℂ)) := by
  apply Lp.ext
  have weighted:=NativeWindowAbsoluteTimeIsometry.weighted_ae ℂ
    (Lp.coeFn_const (p := 2) (μ := averageMeasure) (1 : ℂ))
  have shifted:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae weighted
  filter_upwards [NativeWindowAbsoluteTimePhysicalMatter.background_ae time,
    NativeWindowAbsoluteTimeIsometry.map_ae ℂ time (Lp.constL 2 averageMeasure ℂ (1 : ℂ)),shifted]
    with s first last actual
  change scalarMap time (Lp.constL 2 averageMeasure ℂ (1 : ℂ)) s=_ at last
  rw [first,last]
  change NativeWindowKernelHalfDensity.rootKernel (time-s) •
    ((Lp.constL 2 averageMeasure ℂ (1 : ℂ)) : Lag) (time-s)=
      NativeWindowKernelHalfDensity.rootKernel (time-s) • (1 : ℂ) at actual
  rw [actual]
  simp

theorem source_mean (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (i : Coordinate) (x : Torus) :
    inner ℂ (NativeWindowAbsoluteTimePhysicalMatter.background time)
      (field F i (NativeWindowAbsoluteTimeSource.history seed time) x)=
        complexRead F i (NativeForwardWindowSource.source seed time) x := by
  rw [background_map,field_map,(scalarMap time).inner_map_map,L2.inner_def]
  let L : NativeCompleteStressAction.FullSpace →L[ℝ] ℂ:=
    ((ContinuousMap.evalCLM ℂ x).restrictScalars ℝ).comp (complexRead F i)
  have averaged:=L.integral_comp_comm (NativeForwardWindowPairingReadout.original_integrable seed time)
  rw [← NativeForwardWindowPairingReadout.source_probability_integral] at averaged
  calc
    _ = ∫ lag,complexRead F i (NativeUnifiedCompleteSource.source seed (time-lag)) x ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const (p := 2) (μ := averageMeasure) (1 : ℂ),lagField_ae seed F time i x]
        with lag one source
      change ((Lp.constL 2 averageMeasure ℂ (1 : ℂ)) : Lag) lag=(1 : ℂ) at one
      rw [one,source]
      simp [RCLike.inner_apply]
    _ = _ := averaged


theorem source_pair (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (time : ℝ) (i j : Coordinate) (x : Torus) :
    inner ℂ (field F i (NativeWindowAbsoluteTimeSource.history seed time) x)
      (field F j (NativeWindowAbsoluteTimeSource.history seed time) x)=
        (NativeWindowFiniteGramFourier.stress seed time F i j x : ℂ) := by
  rw [field_map,field_map,(scalarMap time).inner_map_map,L2.inner_def,NativeWindowFiniteGramFourier.stress_apply]
  calc
    _ = ∫ lag,(read F i (NativeUnifiedCompleteSource.source seed (time-lag)) x : ℂ)*
        (read F j (NativeUnifiedCompleteSource.source seed (time-lag)) x : ℂ) ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [lagField_ae seed F time i x,lagField_ae seed F time j x] with lag first last
      have reality:=complexSharpSupportProjection_reality F _ closed
        (wholeVelocity_reality _ (NativeCompletePairedAction.source seed (time-lag)).reality)
      rw [first,last,complexRead_real F _ reality i x,complexRead_real F _ reality j x]
      simp [RCLike.inner_apply]
      ring
    _ = _ := by
      simp only [← Complex.ofReal_mul]
      exact integral_complex_ofReal

theorem source_stress_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (closed : ∀ k,k∈F → waveNeg k∈F) (time : ℝ) (i j : Coordinate) (k : IntegerWavevector) :
    mFourierCoeff (fun x : Torus => -inner ℂ (field F i (NativeWindowAbsoluteTimeSource.history seed time) x)
      (field F j (NativeWindowAbsoluteTimeSource.history seed time) x)) k=
        ∫ lag,NativeCompleteStressCarrier.read (NativeUnheatedWindowStress.finiteStress seed F (time-lag)) k i j ∂averageMeasure := by
  simp only [source_pair seed F closed time i j]
  change (∫ x : Torus,mFourier (-k) x • -(NativeWindowFiniteGramFourier.stress seed time F i j x : ℂ))=_
  simp only [smul_neg,integral_neg]
  change -mFourierCoeff (fun x : Torus => (NativeWindowFiniteGramFourier.stress seed time F i j x : ℂ)) k=_
  rw [NativeWindowFiniteGramFourier.stress_fourier seed time F closed i j k,neg_neg]

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalRead
