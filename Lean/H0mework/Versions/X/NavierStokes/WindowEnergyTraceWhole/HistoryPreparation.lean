import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffOperatorTime
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceWhole.Control
import H0mework.Versions.X.NavierStokes.WindowHistoryOseen.Equation
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchyInitialMoments

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPreparedEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeResolventAdjoint
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceWholeHistory (H finiteHistory metricAction constant)
open NativeWindowStageNineSource (coefficient)
open NativeWindowStageNineInitialMoments (massBudget gradientBudget initial_mass initial_gradient)
open NativeWindowAugmentedCoercivity (productCap)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

def initial (M : ℕ) (directions : List Coordinate) : H :=
  constant (includeCLM (modes M) (modes_closed M) (coefficient stackedShortCurrent M directions 0))

theorem initial_source (M : ℕ) : initial M []=finiteHistory stackedShortCurrent (-2) M := by
  apply Lp.ext
  filter_upwards [NativeWindowTraceWholeHistory.constant_ae
    (includeCLM (modes M) (modes_closed M) (coefficient stackedShortCurrent M [] 0)),
    NativeWindowHistoryOseen.history_original stackedShortCurrent M (-2),
    NativeWindowTraceEndpointWindow.average_interval] with shift first last support
  rw [show initial M [] shift=includeCLM (modes M) (modes_closed M) (coefficient stackedShortCurrent M [] 0) from first,last]
  simp only [NativeWindowHistoryOseen.velocityPath,NativeWindowTraceAdjoint.value,coefficient,NativeWindowStageNineWords.word,LinearMap.id_apply,
    NativeWindowHierarchyPairWindow.state_before stackedShortCurrent (-2-shift) (by linarith [support.1])]

theorem constant_pairing (seed : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent butterflyGainViscosity)
    (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (v : physicalSpace (modes M)) :
    inner ℝ (constant (includeCLM (modes M) (modes_closed M) v))
      (metricAction seed frame M F R (constant (includeCLM (modes M) (modes_closed M) v)))=
        pairing (modes M) v (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R v) := by
  rw [NativeWindowTraceWholeHistory.metric_pairing]
  have same : (fun shift => pairing (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (constant (includeCLM (modes M) (modes_closed M) v) shift))
      (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (constant (includeCLM (modes M) (modes_closed M) v) shift)))) =ᵐ[averageMeasure]
      fun _ => pairing (modes M) v (NativeWindowTraceCutOperator.test seed frame (modes M) (modes M) F R v) := by
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae (includeCLM (modes M) (modes_closed M) v)] with shift original
    rw [original,restrict_include]
  rw [integral_congr_ae same]
  simp

def budget (B : ℝ) (directions : List Coordinate) : ℝ :=
  massBudget directions+(butterflyGainViscosity.coeff*(2*Real.pi)^2+3*B*productCap)*gradientBudget directions

private theorem initial_payment (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame B : ℝ) (B0 : 0 ≤ B)
    (bounded : ‖NativeWindowTraceCutTime.fieldJet stackedShortCurrent F R 0 frame‖ ≤ B)
    (closed : FiniteModeNegClosed F) (directions : List Coordinate) :
    inner ℝ (initial M directions) (metricAction stackedShortCurrent frame M F R (initial M directions)) ≤ budget B directions := by
  let v := coefficient stackedShortCurrent M directions 0
  let G := NativeUnheatedStressProduct.gradientMass (complexSharpSupportProjection (modes M) v.1)
  have G0 : 0 ≤ G := tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative _)
  have tested := NativeWindowTraceCutTime.quadratic_bound stackedShortCurrent (modes M) F R 0 frame v (modes_zero M) (modes_closed M) closed
  have square : NativeWindowTraceCutTime.quadraticJet stackedShortCurrent (modes M) F R 0 frame v ≤ 3*B*productCap*G := by
    apply (le_abs_self _).trans (tested.trans _)
    apply mul_le_mul_of_nonneg_right _ G0
    apply mul_le_mul_of_nonneg_right _ (by unfold productCap; positivity)
    exact mul_le_mul_of_nonneg_left bounded (by norm_num)
  have coefficient0 : 0 ≤ butterflyGainViscosity.coeff*(2*Real.pi)^2+3*B*productCap := by
    unfold productCap
    positivity [butterflyGainViscosity.coeff_pos]
  have mass := initial_mass M directions
  have gradient := mul_le_mul_of_nonneg_left (initial_gradient M directions) coefficient0
  change pairing (modes M) v v ≤ massBudget directions at mass
  change (butterflyGainViscosity.coeff*(2*Real.pi)^2+3*B*productCap)*G ≤ _ at gradient
  change inner ℝ (constant (includeCLM (modes M) (modes_closed M) v))
    (metricAction stackedShortCurrent frame M F R (constant (includeCLM (modes M) (modes_closed M) v))) ≤ _
  rw [constant_pairing,NativeWindowTraceCutTime.actual_pairing,NativeWindowAugmentedCoercivity.spectral_diagonal _ _ (modes_zero M),
    NativeWindowAugmentedTestProduct.curl_original _ _ (modes_zero M)]
  change pairing (modes M) v v+butterflyGainViscosity.coeff*((2*Real.pi)^2*G)+
    NativeWindowTraceCutTime.quadraticJet stackedShortCurrent (modes M) F R 0 frame v ≤ budget B directions
  dsimp only [budget]
  linarith only [mass,gradient,square]

theorem source_all_word_bound (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ B : ℝ,0 ≤ B ∧∀ R ≥ low,∀ cutoff ≥ low,∀ M,∀ frame ∈ Icc 0 horizon,∀ directions : List Coordinate,
      inner ℝ (initial M directions)
        (metricAction stackedShortCurrent frame M (integerWaveFrequencyCube cutoff) R (initial M directions)) ≤ budget B directions := by
  obtain ⟨low,B,B0,paid⟩ := NativeWindowTraceCutTime.source_field_bound stackedShortCurrent horizon nonnegative 0
  exact ⟨low,B,B0,fun R above cutoff covered M frame inside directions => initial_payment M (integerWaveFrequencyCube cutoff)
    R frame B B0 (paid R above cutoff covered frame inside) (NativeWindowFiniteGramFourier.cube_closed cutoff) directions⟩

theorem prepared_source_bound (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,∀ R ≥ low,∀ cutoff ≥ low,∀ M,∀ frame ∈ Icc 0 horizon,
      inner ℝ (finiteHistory stackedShortCurrent (-2) M)
        (metricAction stackedShortCurrent frame M (integerWaveFrequencyCube cutoff) R (finiteHistory stackedShortCurrent (-2) M)) ≤ C := by
  obtain ⟨low,B,_,paid⟩ := source_all_word_bound horizon nonnegative
  refine ⟨low,budget B [],fun R above cutoff covered M frame inside => ?_⟩
  have read := paid R above cutoff covered M frame inside []
  simpa only [initial_source] using read

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPreparedEnergy
