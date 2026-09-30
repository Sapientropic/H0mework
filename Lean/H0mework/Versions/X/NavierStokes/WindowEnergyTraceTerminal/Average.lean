import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Operator
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceDual.Window

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalAverage
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeResolventAdjoint NativePhysicalFourier NativeWholeH1Mixed
open NativeWindowStressHeatSource (physical)
open NativeWindowTraceTerminalOperator (stressNorm)
open NativeWindowTraceGradient (traceStress)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceDualWindow (value value_read)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def squareRead (S : C(Torus,ℝ)) : C(Torus,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (physical (S*S))).comp physical

theorem squareRead_original (S u : C(Torus,ℝ)) :
    squareRead S (u*u)=‖physical (S*u)‖^2 := by
  change inner ℝ (physical (S*S)) (physical (u*u))=_
  rw [NativeWindowStressHeatSource.physical_inner,NativeWindowTraceTerminalSynthesis.physical_square]
  apply integral_congr_ae
  filter_upwards with point
  simp only [ContinuousMap.mul_apply]
  ring

def stressSquare (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (sample : ℝ) : ℝ :=
  ∑ i : Coordinate,‖physical (traceStress seed observation F*NativeWindowStressHeatTime.field seed F i sample)‖^2

theorem stressSquare_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) :
    Integrable (fun shift => stressSquare seed observation F (observation-shift)) averageMeasure := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have paid := (squareRead (traceStress seed observation F)).integrable_comp
    (NativeWindowFiniteGramFourier.pair_integrable seed observation F i i)
  simpa only [NativeWindowFiniteGramFourier.pairRead,← NativeWindowStressHeatTime.field_original,
    squareRead_original] using! paid

theorem stressSquare_average (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) :
    (∫ shift,stressSquare seed observation F (observation-shift) ∂averageMeasure)=
      ∫ point : Torus,(traceStress seed observation F point)^3 := by
  have paid (i : Coordinate) := (squareRead (traceStress seed observation F)).integrable_comp
    (NativeWindowFiniteGramFourier.pair_integrable seed observation F i i)
  have same : stressSquare seed observation F = fun sample => ∑ i : Coordinate,
      squareRead (traceStress seed observation F) (NativeWindowFiniteGramFourier.pairRead F i i
        (NativeUnifiedCompleteSource.source seed sample)) := by
    funext sample
    simp only [stressSquare,NativeWindowFiniteGramFourier.pairRead,← NativeWindowStressHeatTime.field_original,
      squareRead_original]
  rw [same,integral_finsetSum Finset.univ (fun i _ => paid i)]
  simp only [(squareRead (traceStress seed observation F)).integral_comp_comm
    (NativeWindowFiniteGramFourier.pair_integrable seed observation F _ _),← map_sum]
  change squareRead (traceStress seed observation F) (traceStress seed observation F)=_
  rw [squareRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  simp only [ContinuousMap.mul_apply]
  ring

theorem stressNorm_square (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M : ℕ) (F : Finset IntegerWavevector) (cover : ∀ k∈F,k≠0 →k∈modes M)
    (sample : ℝ) (nonnegative : 0 ≤ sample) :
    stressNorm seed observation (modes M) F (value seed M sample)^2 ≤
      3*stressSquare seed observation F sample := by
  simp only [stressNorm,value_read seed M sample nonnegative F cover]
  have bound := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate) (fun _ => (1:ℝ))
    (fun i => ‖physical (traceStress seed observation F*NativeWindowStressHeatTime.field seed F i sample)‖)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_ofNat,mul_one,stressSquare] using! bound

theorem source_stressSquare (seed : GeneratedWholeRestartCurrent nu) (observation horizon : ℝ)
    (inside : observation∈Icc 0 horizon) (radius : ℕ) :
    (∫ shift,stressSquare seed observation (integerWaveFrequencyCube radius) (observation-shift) ∂averageMeasure) ≤
      NativeWindowTraceTerminalCubic.budget seed horizon := by
  rw [stressSquare_average]
  exact NativeWindowTraceTerminalCubic.source_cubic_bound seed radius observation horizon inside

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalAverage
