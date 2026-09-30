import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixPotential
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.PreparationControl

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow (integerWaveFrequencyCube)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem prepared_field_bound (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃B : ℝ,0≤B ∧
      ∀radius≥low,∀outerRadius (time : ℝ),time∈Icc (-2 : ℝ) horizon →
        ∀output input : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate,
          ‖NativeWindowAugmentedSourceForm.matrixField stackedShortCurrent time
            (integerWaveFrequencyCube outerRadius) radius output input‖≤B := by
  obtain ⟨low,paid⟩ := NativeWindowPreparedPrimitiveControl.correctionJet_small
    0 horizon nonnegative 1 (by norm_num)
  let S:=NativeWindowPreparedSobolevWindow.budget 0 horizon
  let B:=S+1
  have S0 : 0≤S := by
    have inside : (0 : ℝ)∈Icc (-2 : ℝ) horizon := ⟨by norm_num,nonnegative⟩
    have source := NativeWindowPreparedAugmentedControl.stressJet_bound
      0 0 0 horizon nonnegative inside 0 0
    exact (norm_nonneg _).trans source
  refine ⟨low,B,by dsimp only [B]; linarith,fun radius above outerRadius time inside output input => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  have correction : ‖NativeWindowPressureStrainHistory.correction
      stackedShortCurrent F radius time output input‖≤1 := by
    simpa only [NativeWindowJointNormalForm.correctionJet_zero] using
      (paid radius above F time inside output input).le
  have stress : ‖NativeWindowStressHeatSource.physical
      (NativeWindowFiniteGramFourier.stress stackedShortCurrent time F output input)‖≤S := by
    have original := NativeWindowPreparedAugmentedControl.stressJet_bound
      outerRadius 0 time horizon nonnegative inside output input
    rw [NativeWindowPreparedAugmentedControl.stressJet_zero
      outerRadius time inside.1 output input] at original
    exact original
  change ‖NativeWindowStressHeatSource.physical
      (NativeWindowFiniteGramFourier.stress stackedShortCurrent time F output input)+
        NativeWindowPressureStrainHistory.correction
          stackedShortCurrent F radius time output input‖≤B
  exact (norm_add_le _ _).trans (add_le_add stress correction)

theorem prepared_potential_relative (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius
        (M : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector),
        ∀zero : 0∉M,
        ∀closed : ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.FiniteModeNegClosed M,
        ∀time∈Icc (-2 : ℝ) horizon,
        ∀v : NativeFiniteActionResolvent.physicalSpace M,
          ‖NativeFiniteActionResolvent.coefficients M
            (potential stackedShortCurrent time M
              (integerWaveFrequencyCube outerRadius) radius v)‖≤
            epsilon*‖NativeFiniteActionResolvent.coefficients M
              (NativeWindowOperatorGreen.laplacian M zero closed butterflyGainViscosity v)‖+
              C*‖NativeFiniteActionResolvent.coefficients M v‖ := by
  obtain ⟨low,B,B0,field⟩ := prepared_field_bound horizon nonnegative
  obtain ⟨C,C0,paid⟩ := potential_relative_of_field stackedShortCurrent
    (Icc (-2 : ℝ) horizon) low B B0 field epsilon positive
  exact ⟨low,C,C0,paid⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
