import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineTransposePotential
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixGraph

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow (integerWaveFrequencyCube)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open NativeFiniteActionResolvent (physicalSpace coefficients pairing)
open NativeWindowOperatorGreen (laplacian)
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger (FiniteModeNegClosed)
noncomputable section

theorem prepared_transpose_test_graph (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
        ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
        ∀time∈Icc (-2 : ℝ) horizon,∀v : physicalSpace M,
          ‖coefficients M (transposeTest stackedShortCurrent time M M
            (integerWaveFrequencyCube outerRadius) radius v)‖^2≤
            C*(‖coefficients M (laplacian M zero closed butterflyGainViscosity v)‖^2+
              ‖coefficients M v‖^2) ∧
          -2*butterflyGainViscosity.coeff*pairing M
            (transposeTest stackedShortCurrent time M M
              (integerWaveFrequencyCube outerRadius) radius v)
            (laplacian M zero closed butterflyGainViscosity v)≤
            -butterflyGainViscosity.coeff^2*
              ‖coefficients M (laplacian M zero closed butterflyGainViscosity v)‖^2+
              C*‖coefficients M v‖^2 := by
  obtain ⟨low,B,B0,field⟩ := prepared_field_bound horizon nonnegative
  obtain ⟨C,C0,paid⟩ := transposePotential_relative_of_field stackedShortCurrent
    (Icc (-2 : ℝ) horizon) low B B0 field
    (butterflyGainViscosity.coeff/4) (by positivity [butterflyGainViscosity.coeff_pos])
  refine ⟨low,graphCap butterflyGainViscosity C,
    graphCap_nonnegative butterflyGainViscosity C,
    fun radius above outerRadius M zero closed time inside v => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  let T:=transposeTest stackedShortCurrent time M M F radius
  let P:=transposePotential stackedShortCurrent time M F radius
  have split:=transposeTest_split stackedShortCurrent time M F radius zero closed v
  have source:=paid radius above outerRadius M zero closed time inside v
  exact ⟨graph_upper_of_split M zero closed T P v C split source,
    graph_heat_of_split M zero closed T P v C split source⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
