import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixHistory
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedMatrixGraph

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
noncomputable section

theorem prepared_full_metric_graph (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
        ∀v : NativeWindowTraceWholeHistory.H,
          ‖fullMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v‖^2≤
            C*(‖laplacianAction butterflyGainViscosity M v‖^2+‖v‖^2) ∧
          -2*butterflyGainViscosity.coeff*inner ℝ
            (fullMetricAction stackedShortCurrent time M
              (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
                outerRadius) radius v)
            (laplacianAction butterflyGainViscosity M v)≤
            -butterflyGainViscosity.coeff^2*
              ‖laplacianAction butterflyGainViscosity M v‖^2+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩ :=
    NativeStageNineFullMatrixPotential.prepared_full_test_graph horizon nonnegative
  exact ⟨low,C,C0,metric_graph_of_test stackedShortCurrent
    (Icc (-2 : ℝ) horizon) low C C0 source⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
