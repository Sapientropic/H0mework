import H0mework.NavierStokes.WindowEnergyPreparation.Write
import H0mework.NavierStokes.WindowSourcePreparation.InitialStress
import H0mework.NavierStokes.WindowSourcePreparation.ForcingSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowStressPreparationInitial
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeFullOrderAction NativeFullOrderSynthesis NativePhysicalFourier NativePhysicalContinuous
open NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativePhysicalHistoryInitialAction (momentum)
open NativeWindowPreparationInitial (velocity tensorProduct Tensor)
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section

private theorem projected_square_le (raw : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (order : ℕ) (wave : IntegerWavevector) :
    frequencySize wave^(2*order)*complexCoordinateAmplitudeSq (complexSharpSupportProjection F raw wave) ≤
      frequencySize wave^(2*order)*complexCoordinateAmplitudeSq (raw wave) := by
  by_cases inside : wave ∈ F
  · simp only [complexSharpSupportProjection_apply,if_pos inside,le_refl]
  · simp only [complexSharpSupportProjection_apply,if_neg inside]
    have zero : complexCoordinateAmplitudeSq (0 : ComplexCoordinateVector) = 0 := by simp [complexCoordinateAmplitudeSq]
    rw [zero,mul_zero]
    exact mul_nonneg (pow_nonneg (frequencySize_pos wave).le _) (complexCoordinateAmplitudeSq_nonneg _)

private theorem projected_square_summable (raw : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (order : ℕ) (paid : Summable fun wave => frequencySize wave^(2*order)*complexCoordinateAmplitudeSq (raw wave)) :
    Summable fun wave => frequencySize wave^(2*order)*
      complexCoordinateAmplitudeSq (complexSharpSupportProjection F raw wave) :=
  paid.of_nonneg_of_le (fun wave => mul_nonneg (pow_nonneg (frequencySize_pos wave).le _)
    (complexCoordinateAmplitudeSq_nonneg _)) (projected_square_le raw F order)

def initialField (F : Finset IntegerWavevector) : PhysicalSpace → PhysicalSpace :=
  spatialField (complexSharpSupportProjection F velocity)

def initialRate (F : Finset IntegerWavevector) : PhysicalSpace → PhysicalSpace :=
  spatialField (complexSharpSupportProjection F momentum)

theorem initialField_smooth (F : Finset IntegerWavevector) : ContDiff ℝ ∞ (initialField F) :=
  spatialField_smooth_of_square _ fun order => projected_square_summable velocity F order
    (NativeWindowPreparationInitial.square_moments order)

theorem initialRate_smooth (F : Finset IntegerWavevector) : ContDiff ℝ ∞ (initialRate F) :=
  spatialField_smooth_of_square _ fun order => projected_square_summable momentum F order
    (NativeWindowPreparationForce.square_moments order)

theorem initialField_bound (F : Finset IntegerWavevector) (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (initialField F) point‖ ≤ NativeWindowPreparationInitial.budget order := by
  apply (spatialField_bound_of_square _ (fun order => projected_square_summable velocity F order
    (NativeWindowPreparationInitial.square_moments order)) order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2*Real.pi)^order)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply add_le_add_left
  rw [← NativeWindowPreparationInitial.square_budget]
  exact (projected_square_summable velocity F _ (NativeWindowPreparationInitial.square_moments _)).tsum_le_tsum
    (projected_square_le velocity F _) (NativeWindowPreparationInitial.square_moments _)

theorem initialRate_bound (F : Finset IntegerWavevector) (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (initialRate F) point‖ ≤ NativeWindowPreparationForce.budget order := by
  apply (spatialField_bound_of_square _ (fun order => projected_square_summable momentum F order
    (NativeWindowPreparationForce.square_moments order)) order point).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (2*Real.pi)^order)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply add_le_add_left
  exact ((projected_square_summable momentum F _ (NativeWindowPreparationForce.square_moments _)).tsum_le_tsum
    (projected_square_le momentum F _) (NativeWindowPreparationForce.square_moments _)).trans
      (NativeWindowPreparationForce.square_bound _)

theorem initialField_original (F : Finset IntegerWavevector) (coordinate : Coordinate) (point : PhysicalSpace) :
    NativeWindowStressHeatTime.field stackedShortCurrent F coordinate 0 (circlePoint point) =
      initialField F point coordinate := by
  rw [NativeWindowStressHeatTime.field_original,NativeWindowFiniteGramFourier.read_original]
  change continuousField (complexSharpSupportProjection F
    (wholeVelocity (NativeUnifiedCompleteSource.source stackedShortCurrent 0).fst)) (circlePoint point) coordinate = _
  rw [← NativeWindowPreparationSource.window_initial stackedShortCurrent (-2) le_rfl]
  rfl

theorem initialRate_row (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeWindowStressPreparationField.row wave coordinate
      (momentumCLM butterflyGainViscosity (NativeUnifiedCompleteSource.source stackedShortCurrent 0)) =
        momentum wave coordinate := by
  by_cases zero : wave = 0
  · subst wave
    change integerWaveNormSq 0^2 • wholeVelocity
      (momentumCLM butterflyGainViscosity (NativeUnifiedCompleteSource.source stackedShortCurrent 0)) 0 coordinate = _
    simp only [wholeVelocity_zero,Pi.zero_apply,smul_zero]
    rw [NativePhysicalHistoryInitialAction.momentum_source,biotSavartVelocityCoefficient_zero,Pi.zero_apply]
  · change integerWaveNormSq wave^2 • wholeVelocity
      (momentumCLM butterflyGainViscosity (NativeUnifiedCompleteSource.source stackedShortCurrent 0)) wave coordinate = _
    rw [wholeVelocity_nonzero _ ⟨wave,zero⟩ coordinate,
      NativeWindowPreparationForce.full_initial_action ⟨wave,zero⟩]
    change integerWaveNormSq wave^2 • ((integerWaveNormSq wave)⁻¹^2 • momentum wave coordinate) = _
    rw [smul_smul,← mul_pow,mul_inv_cancel₀ (integerWaveNormSq_pos zero).ne',one_pow,one_smul]

theorem initialRate_original (F : Finset IntegerWavevector) (coordinate : Coordinate) (point : PhysicalSpace) :
    NativeWindowStressPreparationField.fullRate stackedShortCurrent F coordinate 0 (circlePoint point) =
      initialRate F point coordinate := by
  change _ = (scalarContinuous (complexSharpSupportProjection F momentum) coordinate (circlePoint point)).re
  unfold NativeWindowStressPreparationField.fullRate NativeWindowStressPreparationField.read
  simp only [ContinuousLinearMap.comp_apply,sum_apply]
  unfold scalarContinuous
  rw [tsum_eq_sum (s := F)]
  · change ((∑ wave ∈ F, NativeWindowStressPreparationField.row wave coordinate
        (momentumCLM butterflyGainViscosity (NativeUnifiedCompleteSource.source stackedShortCurrent 0)) •
          UnitAddTorus.mFourier wave) (circlePoint point)).re = _
    apply congrArg (fun value : C(Torus,ℂ) => (value (circlePoint point)).re)
    apply Finset.sum_congr rfl
    intro wave inside
    simp only [complexSharpSupportProjection_apply,if_pos inside]
    rw [initialRate_row]
  · intro wave outside
    simp only [complexSharpSupportProjection_apply,if_neg outside,Pi.zero_apply]
    exact zero_smul ℂ (UnitAddTorus.mFourier wave)

def pair (F : Finset IntegerWavevector) (point : PhysicalSpace) : Tensor :=
  -tensorProduct (initialRate F point) (initialField F point)-
    tensorProduct (initialField F point) (initialRate F point)

theorem pair_original (F : Finset IntegerWavevector) (output input : Coordinate) (point : PhysicalSpace) :
    pair F point (output,input) =
      NativeWindowStressPreparationWrite.fullPairRate stackedShortCurrent F output input 0 (circlePoint point) := by
  simp only [pair,PiLp.sub_apply,PiLp.neg_apply,NativeWindowPreparationInitial.tensorProduct_apply,
    NativeWindowStressPreparationWrite.fullPairRate,ContinuousMap.add_apply,ContinuousMap.mul_apply,
    initialRate_original,initialField_original]
  ring

theorem pair_smooth (F : Finset IntegerWavevector) : ContDiff ℝ ∞ (pair F) :=
  ((tensorProduct.contDiff.comp (initialRate_smooth F)).clm_apply (initialField_smooth F)).neg.sub
    ((tensorProduct.contDiff.comp (initialField_smooth F)).clm_apply (initialRate_smooth F))

def pairBudget (order : ℕ) : ℝ := ‖tensorProduct‖ * ∑ rank ∈ Finset.range (order+1),
  (order.choose rank : ℝ)*(NativeWindowPreparationForce.budget rank*NativeWindowPreparationInitial.budget (order-rank)+
    NativeWindowPreparationInitial.budget rank*NativeWindowPreparationForce.budget (order-rank))

theorem pair_bound (F : Finset IntegerWavevector) (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (pair F) point‖ ≤ pairBudget order := by
  have regular (first last : PhysicalSpace → PhysicalSpace) (a : ContDiff ℝ ∞ first) (b : ContDiff ℝ ∞ last) :=
    tensorProduct.norm_iteratedFDeriv_le_of_bilinear a b point
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have left := regular _ _ (initialRate_smooth F) (initialField_smooth F)
  have right := regular _ _ (initialField_smooth F) (initialRate_smooth F)
  change ‖iteratedFDeriv ℝ order (-(fun point => tensorProduct (initialRate F point) (initialField F point))-
      (fun point => tensorProduct (initialField F point) (initialRate F point))) point‖ ≤ _
  have firstSmooth : ContDiff ℝ order (-(fun point => tensorProduct (initialRate F point) (initialField F point))) := by
    exact ((tensorProduct.contDiff.comp (initialRate_smooth F)).clm_apply (initialField_smooth F)).neg.of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have lastSmooth : ContDiff ℝ order (fun point => tensorProduct (initialField F point) (initialRate F point)) := by
    exact ((tensorProduct.contDiff.comp (initialField_smooth F)).clm_apply (initialRate_smooth F)).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  rw [iteratedFDeriv_sub firstSmooth lastSmooth,iteratedFDeriv_neg]
  apply (norm_sub_le _ _).trans
  rw [Pi.neg_apply,norm_neg]
  apply (add_le_add left right).trans
  simp only [pairBudget,← mul_add,← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg tensorProduct)
  apply Finset.sum_le_sum
  intro rank _
  have U0 := initialField_bound F rank point
  have U1 := initialField_bound F (order-rank) point
  have M0 := initialRate_bound F rank point
  have M1 := initialRate_bound F (order-rank) point
  have nonneg (n : ℕ) : 0 ≤ NativeWindowPreparationInitial.budget n :=
    (norm_nonneg _).trans (initialField_bound F n point)
  have nonnegM (n : ℕ) : 0 ≤ NativeWindowPreparationForce.budget n :=
    (norm_nonneg _).trans (initialRate_bound F n point)
  have paid := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul M0 U1 (norm_nonneg _) (nonnegM rank))
    (mul_le_mul U0 M1 (norm_nonneg _) (nonneg rank))) (Nat.cast_nonneg (order.choose rank))
  simpa only [mul_add,mul_assoc] using paid

end
end SaturationMonoid.NavierStokes.NativeWindowStressPreparationInitial
