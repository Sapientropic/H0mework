import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HierarchyInitialMoments
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.PreparationControl

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStageNineInitialEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWindowStressOseenTest (evaluate)
open NativeWindowAugmentedFixedOperator (test)
open NativeWindowAugmentedTestProduct (product_bound projected_gradient_le curl_original)
open NativeWindowAugmentedCoercivity (productCap)
open NativeWindowAugmentedTimeForm (matrixJet quadraticJet)
open NativeWindowStageNineSource (coefficient)
open NativeWindowStageNineInitialMoments
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fieldBudget : ℝ := NativeWindowPreparedSobolevWindow.budget 0 0+1

theorem fieldBudget_nonnegative : 0≤fieldBudget := by
  have paid := (norm_nonneg _).trans (NativeWindowPreparedAugmentedControl.stressJet_bound 0 0 (-2) 0 le_rfl ⟨le_rfl,by norm_num⟩ 0 0)
  unfold fieldBudget
  linarith

def gradientCoefficient : ℝ := butterflyGainViscosity.coeff*(2*Real.pi)^2+9*fieldBudget*productCap

theorem gradientCoefficient_nonnegative : 0≤gradientCoefficient := by
  unfold gradientCoefficient productCap
  positivity [butterflyGainViscosity.coeff_pos,fieldBudget_nonnegative]

def wordBudget (directions : List Coordinate) : ℝ := massBudget directions+gradientCoefficient*gradientBudget directions

theorem wordBudget_nonnegative (directions : List Coordinate) : 0≤wordBudget directions := by
  have mass0 : 0 ≤ massBudget directions := by
    apply le_trans (b := pairing (modes 0) (coefficient stackedShortCurrent 0 directions 0) (coefficient stackedShortCurrent 0 directions 0))
    · change (0 : ℝ) ≤ inner ℝ (coefficients (modes 0) (coefficient stackedShortCurrent 0 directions 0))
        (coefficients (modes 0) (coefficient stackedShortCurrent 0 directions 0))
      rw [real_inner_self_eq_norm_sq]
      positivity
    · exact initial_mass 0 directions
  have grad0 : 0≤gradientBudget directions :=
    (tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative _)).trans (initial_gradient 0 directions)
  exact add_nonneg mass0 (mul_nonneg gradientCoefficient_nonnegative grad0)

theorem source_word_initial_bound : ∃ low : ℕ,∀ radius≥low,∀ outerRadius M,∀ directions : List Coordinate,
    pairing (modes M) (coefficient stackedShortCurrent M directions 0)
      (test stackedShortCurrent (-2) (modes M) (modes M) (integerWaveFrequencyCube outerRadius) radius
        (coefficient stackedShortCurrent M directions 0))≤wordBudget directions := by
  obtain ⟨low,small⟩ := NativeWindowPreparedPrimitiveControl.correctionJet_small 0 0 le_rfl 1 (by norm_num)
  refine ⟨low,fun radius above outerRadius M directions => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let v := coefficient stackedShortCurrent M directions 0
  let G := NativeUnheatedStressProduct.gradientMass (complexSharpSupportProjection (modes M) v.1)
  have fieldBound (output input : Coordinate) : ‖matrixJet stackedShortCurrent F radius 0 (-2) output input‖≤fieldBudget := by
    rw [NativeWindowAugmentedTimeForm.matrixJet,← NativeWindowPreparedAugmentedControl.stressJet_original outerRadius 0 (-2) le_rfl]
    exact (norm_add_le _ _).trans (add_le_add
      (NativeWindowPreparedAugmentedControl.stressJet_bound outerRadius 0 (-2) 0 le_rfl ⟨le_rfl,by norm_num⟩ output input)
      (small radius above F (-2) ⟨le_rfl,by norm_num⟩ output input).le)
  have row (output input : Coordinate) : |inner ℝ (matrixJet stackedShortCurrent F radius 0 (-2) output input)
      (NativeWindowStressHeatSource.physical (evaluate (modes M) F output v*evaluate (modes M) F input v))|≤
        fieldBudget*productCap*G := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound (modes M) F v (modes_zero M) (modes_closed M)
      (NativeWindowFiniteGramFourier.cube_closed outerRadius) output input).trans
        (mul_le_mul_of_nonneg_left (projected_gradient_le (modes M) F v) (by positivity))
    exact (mul_le_mul (fieldBound output input) tested (norm_nonneg _) fieldBudget_nonnegative).trans_eq (by unfold productCap; ring)
  have matrix : |quadraticJet stackedShortCurrent (modes M) F radius 0 (-2) v|≤9*fieldBudget*productCap*G := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ => row output input)
    exact paid.trans_eq (by simp; ring)
  rw [NativeWindowAugmentedTimeForm.actual_pairing,NativeWindowAugmentedCoercivity.spectral_diagonal _ _ (modes_zero M),
    curl_original _ _ (modes_zero M)]
  have first := initial_mass M directions
  have last := mul_le_mul_of_nonneg_left (initial_gradient M directions) gradientCoefficient_nonnegative
  have signed := (le_abs_self _).trans matrix
  dsimp only [gradientCoefficient] at last
  dsimp only [wordBudget,gradientCoefficient]
  linarith only [first,last,signed]

def budget (order : ℕ) : ℝ := ∑ index : FixedMatterSpatialWordIndex order,wordBudget index.toList

theorem source_initial_energy : ∃ low : ℕ,∀ order : ℕ,0≤budget order ∧
    ∀ radius≥low,∀ outerRadius M,
      NativeWindowStageNineWords.energy stackedShortCurrent order (-2) (modes M) (integerWaveFrequencyCube outerRadius) radius
        (fun index => coefficient stackedShortCurrent M index.toList 0)≤budget order := by
  obtain ⟨low,paid⟩ := source_word_initial_bound
  exact ⟨low,fun order => ⟨Finset.sum_nonneg (fun index _ => wordBudget_nonnegative index.toList),fun radius above outerRadius M =>
    Finset.sum_le_sum (fun index _ => paid radius above outerRadius M index.toList)⟩⟩

end
end SaturationMonoid.NavierStokes.NativeWindowStageNineInitialEnergy
