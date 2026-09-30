import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixGraph
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedMatrixPotential

set_option autoImplicit false
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

theorem prepared_full_test_graph (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
        ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
        ∀time∈Icc (-2 : ℝ) horizon,∀v : physicalSpace M,
          ‖coefficients M (NativeWindowAugmentedFixedOperator.test
            stackedShortCurrent time M M (integerWaveFrequencyCube outerRadius) radius v)‖^2≤
            C*(‖coefficients M (laplacian M zero closed butterflyGainViscosity v)‖^2+
              ‖coefficients M v‖^2) ∧
          -2*butterflyGainViscosity.coeff*pairing M
            (NativeWindowAugmentedFixedOperator.test stackedShortCurrent time M M
              (integerWaveFrequencyCube outerRadius) radius v)
            (laplacian M zero closed butterflyGainViscosity v)≤
            -butterflyGainViscosity.coeff^2*
              ‖coefficients M (laplacian M zero closed butterflyGainViscosity v)‖^2+
              C*‖coefficients M v‖^2 := by
  obtain ⟨low,C,_,paid⟩ := prepared_potential_relative horizon nonnegative
    (butterflyGainViscosity.coeff/4) (by positivity [butterflyGainViscosity.coeff_pos])
  obtain ⟨D,D0,graph⟩ := test_graph_of_relative stackedShortCurrent
    (Icc (-2 : ℝ) horizon) low C paid
  exact ⟨low,D,D0,graph⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
