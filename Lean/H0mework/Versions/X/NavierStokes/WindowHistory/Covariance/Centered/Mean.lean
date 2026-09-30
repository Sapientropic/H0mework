import H0mework.Versions.X.NavierStokes.WindowSchurMean.WeightedResidualTest
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalCompletion

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowAbsoluteTimeFourier (Fiber Space physical field)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def meanScalar (time : ℝ) : Fiber →L[ℝ] ℝ :=
  innerSL ℝ (NativeWindowAbsoluteTimePhysicalMatter.background time)

def meanSpace (time : ℝ) : Space →L[ℝ] Lp ℝ 2 (volume : Measure Torus) :=
  (meanScalar time).compLpL 2 volume

def finiteMeanField (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (i : Coordinate) : Lp ℝ 2 (volume : Measure Torus) :=
  meanSpace time (physical (modes M) i (NativeWindowAbsoluteTimeSource.history seed time))

def fullMeanField (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (i : Coordinate) : Lp ℝ 2 (volume : Measure Torus) :=
  meanSpace time (NativeWindowAbsoluteTimePhysicalCompletion.synthesis i
    (NativeWindowAbsoluteTimeSource.history seed time))

theorem finiteMeanField_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
  (i : Coordinate) :
    finiteMeanField seed M time i=
      (ContinuousMap.toLp 2 volume ℝ)
        (NativeWindowFiniteGramFourier.read (modes M) i
          (NativeForwardWindowSource.source seed time)) := by
  unfold finiteMeanField meanSpace
  apply Lp.ext
  filter_upwards [
    (meanScalar time).coeFn_compLpL (physical (modes M) i (NativeWindowAbsoluteTimeSource.history seed time)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus)
      (field (modes M) i (NativeWindowAbsoluteTimeSource.history seed time)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (volume : Measure Torus)
      (NativeWindowFiniteGramFourier.read (modes M) i (NativeForwardWindowSource.source seed time))]
    with x first second third
  rw [first]
  change meanScalar time (((ContinuousMap.toLp 2 volume ℂ)
    (field (modes M) i (NativeWindowAbsoluteTimeSource.history seed time))) x)=_
  rw [second,third]
  have actual := congrArg Complex.re
    (NativeWindowAbsoluteTimePhysicalCurrent.mean_real seed M time i x)
  rw [← NativeWindowAbsoluteTimePhysicalStress.real_pair] at actual
  change inner ℝ (NativeWindowAbsoluteTimePhysicalMatter.background time)
    (field (modes M) i (NativeWindowAbsoluteTimeSource.history seed time) x)=_ at actual
  simpa only [meanScalar,real_inner_comm,innerSL_apply_apply,Complex.ofReal_re] using actual

theorem finiteMeanField_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (i : Coordinate) :
    Tendsto (fun M => finiteMeanField seed M time i) atTop
      (𝓝 (fullMeanField seed time i)) :=
  (meanSpace time).continuous.tendsto _ |>.comp
    (NativeWindowAbsoluteTimePhysicalCompletion.source_tendsto seed time i)


end
end SaturationMonoid.NavierStokes.NativeCenteredCovariance
