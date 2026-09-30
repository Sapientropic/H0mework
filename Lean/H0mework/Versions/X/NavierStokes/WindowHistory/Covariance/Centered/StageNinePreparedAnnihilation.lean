import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedRelative
import H0mework.Versions.X.NavierStokes.WindowHistoryAnnihilation.Control

set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativePhysicalFourier NativeCommonAdvectorAction
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWindowHistoryAnnihilationRows (input current averageGradient)
open NativeWindowHistoryCreationGeometry (gradientSquare)
open NativeWindowHistoryCreationCovariance (trace)
open NativeWindowStressHeatSource (physical)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryAnnihilationControl (laplacianAction graphCost)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
local instance annihilationPhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance annihilationPhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem prepared_annihilation_stress_bound (M : ℕ) (time : ℝ) (r : H) :
    ‖annihilation stackedShortCurrent M time r‖^2≤
      3*(∫point : Torus,NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M) point*averageGradient M r point) := by
  apply (NativeWindowHistoryAnnihilationRows.pressure_bound stackedShortCurrent M time r).trans
  simp only [NativeWindowTraceTerminalSynthesis.physical_square]
  have rows (i : Coordinate):Integrable (fun point : Torus => (current stackedShortCurrent M time r i point)^2) :=
    ((current stackedShortCurrent M time r i).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum Finset.univ (fun i _ => rows i),← integral_const_mul]
  have positive (point : Torus):0≤averageGradient M r point := by
    rw [NativeWindowHistoryAnnihilationRows.averageGradient_point]
    exact integral_nonneg fun _ => NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ _ point
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    ((((NativeWindowTraceGradient.traceStress stackedShortCurrent time
      (integerWaveFrequencyCube M)).continuous.mul
      (averageGradient M r).continuous).const_mul 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  exact Eventually.of_forall fun point =>
    (NativeWindowHistoryAnnihilationControl.point_bound stackedShortCurrent M time r point).trans (by
      have bound:=mul_le_mul_of_nonneg_right
        (trace_le_stress_total stackedShortCurrent M time point) (positive point)
      change 3*trace stackedShortCurrent M time point*averageGradient M r point≤
        3*(NativeWindowTraceGradient.traceStress stackedShortCurrent time
          (integerWaveFrequencyCube M) point*averageGradient M r point)
      nlinarith only [bound])

private theorem testing_original (f w : C(Torus,ℝ)) :
    ((innerSL ℝ (physical f)).comp physical) w=∫point : Torus,f point*w point := by
  rw [ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatSource.physical_inner]

def preparedAnnihilationBudget (horizon eta : ℝ) : ℝ :=
  3*preparedCreationBudget horizon (eta/3)

theorem preparedAnnihilationBudget_nonnegative (horizon eta : ℝ) (positive : 0<eta) :
    0≤preparedAnnihilationBudget horizon eta :=
  mul_nonneg (by norm_num) (preparedCreationBudget_nonnegative horizon (eta/3) (by positivity))

theorem prepared_annihilation_bound (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) (M : ℕ) (time : ℝ)
    (inside : time∈Icc (-2 : ℝ) horizon) (r : H) :
    ‖annihilation stackedShortCurrent M time r‖^2≤
      eta*‖laplacianAction butterflyGainViscosity M r‖^2+
      preparedAnnihilationBudget horizon eta*NativeWindowTraceWholeHistory.gradient M r := by
  let f:=NativeWindowTraceGradient.traceStress stackedShortCurrent time (integerWaveFrequencyCube M)
  let testing:=(innerSL ℝ (physical f)).comp physical
  have integrable:Integrable (fun lag => testing (gradientSquare (modes M) (modes_zero M)
      (modes_closed M) (input M r lag))) averageMeasure :=
    testing.integrable_comp (NativeWindowHistoryAnnihilationRows.gradient_integrable M r)
  have gradPaid:Integrable (fun lag => curlPair (modes M) (input M r lag).1
      (input M r lag).1) averageMeasure :=
    NativeWindowTraceWholeHistory.gradient_integrable butterflyGainViscosity M r
  have estimate:∀lag,testing (gradientSquare (modes M) (modes_zero M)
      (modes_closed M) (input M r lag))≤
      (eta/3)*graphCost butterflyGainViscosity M r lag+
        preparedCreationBudget horizon (eta/3)*
          curlPair (modes M) (input M r lag).1 (input M r lag).1 := by
    intro lag
    rw [show testing _=∫point : Torus,f point*gradientSquare (modes M)
      (modes_zero M) (modes_closed M) (input M r lag) point from testing_original _ _]
    exact prepared_gradient_form horizon (eta/3) nonnegative (by positivity) M time inside _
  have paid:=integral_mono_ae integrable (((NativeWindowHistoryAnnihilationControl.graph_integrable
    butterflyGainViscosity M r).const_mul (eta/3)).add
    (gradPaid.const_mul (preparedCreationBudget horizon (eta/3)))) (Eventually.of_forall estimate)
  have actual:(∫point : Torus,f point*averageGradient M r point)=
      ∫lag,testing (gradientSquare (modes M) (modes_zero M) (modes_closed M)
        (input M r lag)) ∂averageMeasure :=
    (testing_original f (averageGradient M r)).symm.trans
      (testing.integral_comp_comm (NativeWindowHistoryAnnihilationRows.gradient_integrable M r)).symm
  have source:=prepared_annihilation_stress_bound M time r
  change _≤3*(∫point : Torus,f point*averageGradient M r point) at source
  rw [actual] at source
  apply (source.trans (mul_le_mul_of_nonneg_left paid (by norm_num))).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add ((NativeWindowHistoryAnnihilationControl.graph_integrable
      butterflyGainViscosity M r).const_mul (eta/3))
    (gradPaid.const_mul (preparedCreationBudget horizon (eta/3))),integral_const_mul,integral_const_mul]
  have gradRead:(∫lag,curlPair (modes M) (input M r lag).1
      (input M r lag).1 ∂averageMeasure)=
      NativeWindowTraceWholeHistory.gradient M r := rfl
  exact (congrArg₂ (fun x y : ℝ => 3*((eta/3)*x+
      preparedCreationBudget horizon (eta/3)*y))
    (NativeWindowHistoryAnnihilationControl.laplacian_square butterflyGainViscosity M r).symm
    gradRead).trans (by unfold preparedAnnihilationBudget; ring)

theorem prepared_annihilation_relative (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
      ∀r : H,
        ‖annihilation stackedShortCurrent M time r‖^2≤
          eta*‖laplacianAction butterflyGainViscosity M r‖^2+C*‖r‖^2 := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let B:=preparedAnnihilationBudget horizon delta
  let C:=B^2/(2*eta)
  refine ⟨C,by dsimp only [C]; positivity,fun M time inside r => ?_⟩
  have source:=prepared_annihilation_bound horizon delta nonnegative delta0 M time inside r
  have gradient:=NativeWindowMetricGraphHistory.gradient_bound butterflyGainViscosity M r
  have scaled:=mul_le_mul_of_nonneg_left gradient
    (preparedAnnihilationBudget_nonnegative horizon delta delta0)
  have mixed : ‖annihilation stackedShortCurrent M time r‖^2≤
      delta*‖laplacianAction butterflyGainViscosity M r‖^2+
      B*‖r‖*‖laplacianAction butterflyGainViscosity M r‖ := by
    nlinarith only [source,scaled]
  exact NativeStageNineWindowEnergy.relative_from_mixed _ _ _ eta B positive mixed
end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
