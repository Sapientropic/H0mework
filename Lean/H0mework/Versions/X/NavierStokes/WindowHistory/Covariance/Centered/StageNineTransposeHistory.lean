import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineTransposeGraph
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixHistory

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (include_inner)
open NativeFiniteActionResolvent (pairing)
open NativeWholeResolvent (restrictCLM)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
variable {nu : Viscosity}

def transposeMetricFiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWholeResolvent.wholePhysical →L[ℝ] NativeWholeResolvent.wholePhysical :=
  NativeWindowHistoryOseen.lift M (LinearMap.toContinuousLinearMap
    (NativeStageNineFullMatrixPotential.transposeTest seed time
      (modes M) (modes M) F radius))

def transposeMetricAction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowTraceWholeHistory.H →L[ℝ] NativeWindowTraceWholeHistory.H :=
  (transposeMetricFiber seed time M F radius).compLpL 2 averageMeasure

theorem transpose_action_dual (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (x y : NativeWindowTraceWholeHistory.H) :
    inner ℝ x (transposeMetricAction seed time M F radius y)=
      inner ℝ y (fullMetricAction seed time M F radius x) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(transposeMetricFiber seed time M F radius).coeFn_compLpL y,
    (fullMetricFiber seed time M F radius).coeFn_compLpL x]
      with shift left right
  change inner ℝ (x shift)
    (((transposeMetricFiber seed time M F radius).compLpL 2 averageMeasure y) shift)=_
  rw [left]
  change inner ℝ (x shift) (transposeMetricFiber seed time M F radius (y shift))=
    inner ℝ (y shift)
      (((fullMetricFiber seed time M F radius).compLpL 2 averageMeasure x) shift)
  rw [right]
  change inner ℝ (x shift) (NativeWindowHistoryOseen.lift M
    (LinearMap.toContinuousLinearMap
      (NativeStageNineFullMatrixPotential.transposeTest seed time
        (modes M) (modes M) F radius)) (y shift))=
    inner ℝ (y shift) (NativeWindowHistoryOseen.lift M
      (LinearMap.toContinuousLinearMap
        (NativeWindowAugmentedFixedOperator.test seed time
          (modes M) (modes M) F radius)) (x shift))
  simp only [NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply]
  rw [real_inner_comm,include_inner (modes M) (modes_zero M),
    real_inner_comm,include_inner (modes M) (modes_zero M)]
  change pairing (modes M)
    (NativeStageNineFullMatrixPotential.transposeTest seed time
      (modes M) (modes M) F radius
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (y shift)))
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (x shift))=
    pairing (modes M)
      (NativeWindowAugmentedFixedOperator.test seed time
        (modes M) (modes M) F radius
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (x shift)))
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (y shift))
  rw [NativeResolventAdjoint.pairing_symmetric (modes M)
    (NativeStageNineFullMatrixPotential.transposeTest seed time
      (modes M) (modes M) F radius
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (y shift))) _,
    NativeResolventAdjoint.pairing_symmetric (modes M)
      (NativeWindowAugmentedFixedOperator.test seed time
        (modes M) (modes M) F radius
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (x shift))) _]
  exact NativeStageNineFullMatrixPotential.transposeTest_dual seed time
    (modes M) (modes M) F radius _ _

theorem prepared_transpose_metric_graph (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
        ∀v : NativeWindowTraceWholeHistory.H,
          ‖transposeMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v‖^2≤
            C*(‖laplacianAction butterflyGainViscosity M v‖^2+‖v‖^2) ∧
          -2*butterflyGainViscosity.coeff*inner ℝ
            (transposeMetricAction stackedShortCurrent time M
              (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
                outerRadius) radius v)
            (laplacianAction butterflyGainViscosity M v)≤
            -butterflyGainViscosity.coeff^2*
              ‖laplacianAction butterflyGainViscosity M v‖^2+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩ :=
    NativeStageNineFullMatrixPotential.prepared_transpose_test_graph horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius M time inside v => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let op:=NativeStageNineFullMatrixPotential.transposeTest stackedShortCurrent time
    (modes M) (modes M) F radius
  have paid:=finite_graph_lift butterflyGainViscosity M op C C0
    (source radius above outerRadius (modes M) (modes_zero M)
      (modes_closed M) time inside) v
  exact paid
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
