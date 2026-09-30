import H0mework.Versions.X.NavierStokes.SourceHeat.GaussianPhase
import H0mework.Versions.X.NavierStokes.NativeAction.Pairing
import H0mework.Versions.X.NavierStokes.PhysicalTranslation.Field

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder
namespace SaturationMonoid.NavierStokes.NativeHeatTranslationData
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeStressSource
open NativeStressPairingCarrier NativeCofinalStressPositivity NativeHeatGaussianPhase
noncomputable section

def translateLP {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (offset : PhysicalSpace) (wave : Index → IntegerWavevector) (value : lp (fun _ : Index => E) 2) :
    lp (fun _ : Index => E) 2 :=
  ⟨fun index => character offset (wave index) • value index,
    (lp.memℓp value).mono' (fun index => by rw [norm_smul, character_norm, one_mul])⟩

theorem translateLP_row {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (offset : PhysicalSpace) (wave : Index → IntegerWavevector) (value : lp (fun _ : Index => E) 2)
    (index : Index) : translateLP offset wave value index = character offset (wave index) • value index := rfl

theorem translateLP_norm {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (offset : PhysicalSpace) (wave : Index → IntegerWavevector) (value : lp (fun _ : Index => E) 2) :
    ‖translateLP offset wave value‖ = ‖value‖ := by
  apply le_antisymm <;> apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) <;> intro index
  all_goals rw [translateLP_row, norm_smul, character_norm, one_mul]

theorem translateLP_measurable {Index E : Type*} [Countable Index] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (wave : Index → IntegerWavevector) (value : lp (fun _ : Index => E) 2) (μ : Measure PhysicalSpace) :
    AEStronglyMeasurable (fun offset => translateLP offset wave value) μ := by
  classical
  let partialSum (observed : Finset Index) (offset : PhysicalSpace) : lp (fun _ : Index => E) 2 :=
    ∑ index ∈ observed, lp.single 2 index (character offset (wave index) • value index)
  have measurable (observed : Finset Index) : AEStronglyMeasurable (partialSum observed) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro index _
    exact ((lp.singleContinuousLinearMap ℂ (fun _ : Index => E) 2 index).continuous.comp
      ((character_continuous (wave index)).smul continuous_const)).aestronglyMeasurable
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Index)) measurable
  exact Eventually.of_forall fun offset => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num)
    (translateLP offset wave value)

theorem mean_row (offset : PhysicalSpace) (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    wholeVelocity (translateLP offset Subtype.val value) wave = character offset wave • wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp
  · funext coordinate
    rw [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave, zero⟩, wholeVelocity_nonzero _ ⟨wave, zero⟩,
      translateLP_row, PiLp.smul_apply]

theorem physical_translation (offset : PhysicalSpace) (value : WholeRestartVelocityEndpointState)
    (coordinate : Coordinate) :
    NativePhysicalTranslation.translate (NativeFullOrderSynthesis.circlePoint offset)
      (NativePhysicalFourier.scalarField (wholeVelocity value) coordinate) =
      NativePhysicalFourier.scalarField (wholeVelocity (translateLP offset Subtype.val value)) coordinate := by
  apply (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.injective
  apply lp.ext
  funext wave
  rw [UnitAddTorus.mFourierBasis_repr, NativePhysicalTranslation.translate_fourier,
    UnitAddTorus.mFourierBasis_repr, NativePhysicalFourier.scalarField_fourier,
    NativePhysicalFourier.scalarField_fourier, mean_row, Pi.smul_apply]
  rfl

def translate (offset : PhysicalSpace) (value : FullSpace) : FullSpace :=
  WithLp.toLp 2 (translateLP offset Subtype.val value.fst, translateLP offset id value.snd)

theorem translate_norm (offset : PhysicalSpace) (value : FullSpace) : ‖translate offset value‖ = ‖value‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖translateLP offset Subtype.val value.fst‖ ^ 2 + ‖translateLP offset id value.snd‖ ^ 2 = _
  rw [translateLP_norm, translateLP_norm]

theorem translate_measurable (value : FullSpace) (μ : Measure PhysicalSpace) :
    AEStronglyMeasurable (fun offset => translate offset value) μ := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp_aestronglyMeasurable
    ((translateLP_measurable Subtype.val value.fst μ).prodMk (translateLP_measurable id value.snd μ))

theorem stress_row (offset : PhysicalSpace) (value : FullSpace) (wave : IntegerWavevector)
    (output input : Coordinate) :
    NativeCompleteStressCarrier.read (translate offset value).snd wave output input =
      character offset wave * NativeCompleteStressCarrier.read value.snd wave output input := by
  change (NativeCompleteStressCarrier.weight wave)⁻¹ •
    (translateLP offset id value.snd wave) (output,input) = _
  rw [translateLP_row, PiLp.smul_apply]
  change (NativeCompleteStressCarrier.weight wave)⁻¹ • (character offset wave • value.snd wave (output,input)) = _
  rw [smul_comm]
  rfl

theorem mean_reality (offset : PhysicalSpace) (value : FullSpace)
    (reality : WholeRestartVelocityEndpointReality value.fst) :
    WholeRestartVelocityEndpointReality (translate offset value).fst := by
  intro wave coordinate
  have same : wholeVelocity (translate offset value).fst (nonzeroIntegerWavevectorNeg wave).1 coordinate =
      star (wholeVelocity (translate offset value).fst wave.1 coordinate) := by
    change wholeVelocity (translateLP offset Subtype.val value.fst) (-wave.1) coordinate =
      star (wholeVelocity (translateLP offset Subtype.val value.fst) wave.1 coordinate)
    rw [mean_row, mean_row, character_neg]
    have original := congrFun (wholeVelocity_reality value.fst reality wave.1) coordinate
    change wholeVelocity value.fst (-wave.1) coordinate = star (wholeVelocity value.fst wave.1 coordinate) at original
    simp only [Pi.smul_apply, smul_eq_mul, original, star_mul]
    ring
  simpa only [wholeVelocity_nonzero] using same

theorem quadratic_row (offset : PhysicalSpace) (value : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    quadraticFlux (wholeVelocity (translateLP offset Subtype.val value)) wave output input =
      character offset wave * quadraticFlux (wholeVelocity value) wave output input := by
  unfold quadraticFlux
  simp_rw [mean_row, Pi.smul_apply, smul_eq_mul]
  rw [mul_neg, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro first
  have phases : character offset first * character offset (wave - first) = character offset wave := by
    rw [← character_add]
    congr 1
    abel
  calc
    _ = (character offset first * character offset (wave - first)) *
        (wholeVelocity value first input * wholeVelocity value (wave - first) output) := by ring
    _ = _ := by rw [phases]

theorem covariance_row (offset : PhysicalSpace) (value : FullSpace) (left right : Index) :
    covariance (translate offset value).fst (NativeCompleteStressCarrier.read (translate offset value).snd) left right =
      character offset (left.1 - right.1) * covariance value.fst (NativeCompleteStressCarrier.read value.snd) left right := by
  unfold NativeStressPairingCarrier.covariance
  rw [stress_row]
  change -(character offset (left.1 - right.1) * _ -
    quadraticFlux (wholeVelocity (translateLP offset Subtype.val value.fst)) _ _ _) = _
  rw [quadratic_row]
  ring

theorem covariance_positive (offset : PhysicalSpace) (value : FullSpace)
    (positive : (covariance value.fst (NativeCompleteStressCarrier.read value.snd)).PosSemidef) :
    (covariance (translate offset value).fst (NativeCompleteStressCarrier.read (translate offset value).snd)).PosSemidef := by
  let original : NativePositiveKernelCarrier.Kernel Index :=
    ⟨covariance value.fst (NativeCompleteStressCarrier.read value.snd), positive⟩
  let vectors (index : Index) := star (character offset index.1) • NativePositiveKernelCarrier.vector original index
  have gram := gram_posSemidef vectors
  convert! gram using 1
  ext left right
  rw [covariance_row, character_sub, Matrix.gram_apply]
  simp only [vectors, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star,
    NativePositiveKernelCarrier.vector_inner]
  change _ = star (character offset right.1) * (character offset left.1 * covariance value.fst _ left right)
  ring

end
end SaturationMonoid.NavierStokes.NativeHeatTranslationData
