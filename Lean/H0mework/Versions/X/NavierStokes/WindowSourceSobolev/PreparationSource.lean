import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Window
import H0mework.Versions.X.NavierStokes.WindowSourcePreparation.InitialSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPreparedSobolevSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeUnheatedStressProduct (H1 density density_nonnegative gradientMass)
open NativeWindowFiniteStressConvergence (source finiteAt cap cap_nonnegative full full_row)
open NativeWindowPreparationInitial (velocity)
open NativeWindowSobolevStress (quarter)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section
variable {nu : Viscosity}

theorem initial_row : wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst = velocity := by
  rw [← NativeWindowPreparationSource.window_initial stackedShortCurrent (-2) le_rfl]
  rfl

theorem initial_H1 : H1 velocity := by
  apply (NativeWindowPreparationInitial.square_moments 1).of_nonneg_of_le (density_nonnegative velocity)
  intro wave
  have square : NativeUnheatedStressProduct.amplitude velocity wave^2 = complexCoordinateAmplitudeSq (velocity wave) := by
    exact ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.euclideanCoordinateRow_norm_sq _
  rw [density,square]
  simpa only [Nat.mul_one] using mul_le_mul_of_nonneg_right
    (NativeFullOrderSynthesis.normSq_le_frequencySize_sq wave) (complexCoordinateAmplitudeSq_nonneg _)

theorem source_nonpositive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (before : time ≤ 0) :
    source seed time = source seed 0 := by
  unfold source
  rw [NativeWindowPreparationSource.complete_nonpositive seed time before]

theorem finiteAt_nonpositive (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (before : time ≤ 0) : finiteAt seed F time = finiteAt seed F 0 := by
  unfold finiteAt
  rw [← NativeUnifiedCompleteSource.velocity_read,NativeWindowPreparationSource.complete_nonpositive seed time before]
  rw [NativeUnifiedCompleteSource.velocity_read]

theorem source_initial : source stackedShortCurrent 0 =
    full (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst (by rw [initial_row]; exact initial_H1) := by
  have regular : H1 (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst) := by
    rw [initial_row]
    exact initial_H1
  rw [source,dif_pos regular]

theorem source_row_ae : ∀ᵐ time : ℝ, ∀ wave,
    source stackedShortCurrent time wave = quarter wave • NativeCompleteStressCarrier.tensor
      (NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source stackedShortCurrent time).snd wave) := by
  filter_upwards [NativeWindowFiniteStressConvergence.source_row_ae stackedShortCurrent] with time positive wave
  by_cases before : time ≤ 0
  · rw [source_nonpositive stackedShortCurrent time before,
      NativeWindowPreparationSource.complete_nonpositive stackedShortCurrent time before,source_initial,full_row]
    rw [← NativeWindowPreparationSource.window_initial stackedShortCurrent (-2) le_rfl,
      NativeWindowPreparationSource.initial_stress,NativeHigherTimeJets.mixedFlux_diagonal]
  · exact positive (le_of_not_ge before) wave

theorem source_tendsto_ae : ∀ᵐ time : ℝ,
    Tendsto (fun radius => finiteAt stackedShortCurrent
      (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius) time)
      atTop (𝓝 (source stackedShortCurrent time)) := by
  filter_upwards [NativeWindowFiniteStressConvergence.source_tendsto_ae stackedShortCurrent] with time positive
  by_cases before : time ≤ 0
  · simp only [finiteAt_nonpositive stackedShortCurrent _ time before,source_nonpositive stackedShortCurrent time before]
    have regular : NativeWholeH1Mixed.H1 (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl) := by
      change H1 (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst)
      rw [initial_row]
      exact initial_H1
    simpa only [finiteAt,NativeUnheatedSourceGradient.physical,NativeUnifiedCompleteSource.velocity_read,source_initial] using!
      NativeWindowFiniteStressConvergence.strong_tendsto (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl) regular
  · exact positive (le_of_not_ge before)

def initialBound : ℝ := cap*gradientMass velocity

theorem initial_bound_nonnegative : 0 ≤ initialBound :=
  mul_nonneg cap_nonnegative (tsum_nonneg (density_nonnegative velocity))

theorem initial_bound : ‖source stackedShortCurrent 0‖ ≤ initialBound ∧
    ∀ F : Finset IntegerWavevector, ‖finiteAt stackedShortCurrent F 0‖ ≤ initialBound := by
  have regular : NativeWholeH1Mixed.H1 (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl) := by
    change H1 (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst)
    rw [initial_row]
    exact initial_H1
  have mass : NativeWholeH1Mixed.gradientMass (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl) =
      gradientMass velocity := by
    change gradientMass (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst) = _
    rw [initial_row]
  constructor
  · rw [source_initial]
    have paid := NativeWindowSobolevProduct.state_bound _ _ (wholeVelocity_zero _) (wholeVelocity_zero _)
      regular regular
    change ‖full (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst regular‖ ≤ _ at paid
    exact paid.trans_eq (by
      change 6*Real.sqrt NativeUnheatedRieszKernel.constant*
        (NativeWholeH1Mixed.gradientMass (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl)+
          NativeWholeH1Mixed.gradientMass (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl)) = _
      rw [mass]
      unfold initialBound cap
      ring)
  · intro F
    have paid := NativeWindowFiniteStressConvergence.finite_bound
      (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl) regular F
    rw [mass] at paid
    simpa only [finiteAt,NativeUnheatedSourceGradient.physical,NativeUnifiedCompleteSource.velocity_read] using! paid

def envelope (time : ℝ) : ℝ := if time ≤ 0 then initialBound else cap*NativeUnheatedSourceGradient.mass stackedShortCurrent time

theorem envelope_nonnegative (time : ℝ) : 0 ≤ envelope time := by
  unfold envelope
  split_ifs
  · exact initial_bound_nonnegative
  · exact mul_nonneg cap_nonnegative (NativeUnheatedSourceGradient.mass_nonnegative _ _)

theorem source_bound_ae : ∀ᵐ time : ℝ, ‖source stackedShortCurrent time‖ ≤ envelope time ∧
    ∀ F : Finset IntegerWavevector, ‖finiteAt stackedShortCurrent F time‖ ≤ envelope time := by
  filter_upwards [NativeWindowFiniteStressConvergence.source_bound_ae stackedShortCurrent] with time positive
  by_cases before : time ≤ 0
  · simp only [envelope,if_pos before,source_nonpositive stackedShortCurrent time before,
      finiteAt_nonpositive stackedShortCurrent _ time before]
    exact initial_bound
  · simpa only [envelope,if_neg before] using positive (le_of_not_ge before)

theorem mass_initial : NativeUnheatedSourceGradient.mass stackedShortCurrent 0 = gradientMass velocity := by
  rw [← NativeUnheatedSourceGradient.physical_mass stackedShortCurrent 0 le_rfl]
  change gradientMass (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst) = _
  rw [initial_row]

theorem envelope_nonnegative_time (time : ℝ) (nonnegative : 0 ≤ time) :
    envelope time = cap*NativeUnheatedSourceGradient.mass stackedShortCurrent time := by
  by_cases before : time ≤ 0
  · have zero : time = 0 := le_antisymm before nonnegative
    subst time
    simp only [envelope,le_refl,if_true,mass_initial,initialBound]
  · simp only [envelope,if_neg before]

theorem envelope_integrable (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    IntegrableOn envelope (Icc (-1 : ℝ) (horizon+2)) := by
  have left : IntegrableOn envelope (Icc (-1 : ℝ) 0) := by
    have paid : IntegrableOn (fun _ : ℝ => initialBound) (Icc (-1 : ℝ) 0) (volume : Measure ℝ) :=
      continuous_const.integrableOn_Icc
    exact paid.congr_fun (fun time inside => by simp only [envelope,if_pos inside.2]) measurableSet_Icc
  have right : IntegrableOn envelope (Icc (0 : ℝ) (horizon+2)) := by
    have paid : IntegrableOn (fun time => cap*NativeUnheatedSourceGradient.mass stackedShortCurrent time)
        (Icc (0 : ℝ) (horizon+2)) :=
      (NativeUnheatedSourceGradient.mass_integrable stackedShortCurrent (horizon+2) (by linarith)).const_mul cap
    exact paid.congr_fun (fun time inside => (envelope_nonnegative_time time inside.1).symm) measurableSet_Icc
  apply (left.union right).mono_set
  intro time inside
  by_cases before : time ≤ 0
  · exact Or.inl ⟨inside.1,before⟩
  · exact Or.inr ⟨le_of_not_ge before,inside.2⟩

theorem source_measurable : AEStronglyMeasurable (source stackedShortCurrent) (volume : Measure ℝ) :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun radius => (NativeWindowFiniteStressConvergence.finiteAt_continuous stackedShortCurrent
      (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius)).aestronglyMeasurable)
    source_tendsto_ae

theorem source_integrable (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    IntegrableOn (source stackedShortCurrent) (Icc (-1 : ℝ) (horizon+2)) := by
  apply (envelope_integrable horizon nonnegative).mono' source_measurable.restrict
  filter_upwards [ae_restrict_of_ae source_bound_ae] with time paid
  exact paid.1

theorem finiteAt_integrable (horizon : ℝ) (nonnegative : 0 ≤ horizon) (F : Finset IntegerWavevector) :
    IntegrableOn (finiteAt stackedShortCurrent F) (Icc (-1 : ℝ) (horizon+2)) := by
  apply (envelope_integrable horizon nonnegative).mono'
    (NativeWindowFiniteStressConvergence.finiteAt_continuous stackedShortCurrent F).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_of_ae source_bound_ae] with time paid
  exact paid.2 F

end
end SaturationMonoid.NavierStokes.NativeWindowPreparedSobolevSource
