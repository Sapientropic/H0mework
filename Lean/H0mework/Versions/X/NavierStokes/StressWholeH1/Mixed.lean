import H0mework.Versions.X.NavierStokes.StressMovingSource.ProductPhysical
import H0mework.Versions.X.NavierStokes.StressAction.StressDynamicsBilinear
import H0mework.Versions.X.NavierStokes.StressAction.CompleteStressAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeH1Mixed

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open NativeFiniteActionResolvent NativeWholeResolvent NativeEndpointVelocityCarrier NativeResolventCompactness
open NativeTimeJetCarrier NativeHigherTimeJets NativeMovingCriticalProduct NativeMovingCriticalProductScalar

noncomputable section

def modes (radius : ℕ) := puncturedIntegerWaveFrequencyCube radius

theorem modes_zero (radius : ℕ) : 0 ∉ modes radius := zero_not_mem_puncturedIntegerWaveFrequencyCube radius

theorem modes_closed (radius : ℕ) : FiniteModeNegClosed (modes radius) :=
  fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member

def restrict (radius : ℕ) : wholePhysical →L[ℝ] physicalSpace (modes radius) :=
  restrictCLM (modes radius) (modes_zero radius) (modes_closed radius)

theorem restrict_row (radius : ℕ) (value : wholePhysical) (wave : IntegerWavevector) :
    (restrict radius value).1 wave = if wave ∈ modes radius then wholeVelocity value.1 wave else 0 :=
  complexSharpSupportProjection_apply _ _ _

theorem restrict_tendsto (value : wholePhysical) :
    Tendsto (fun radius => (restrict radius value).1) atTop (𝓝 (wholeVelocity value.1)) :=
  complexSharpSupportProjection_puncturedFrequencyCube_tendsto _ (wholeVelocity_zero value.1)

def gradientDensity (value : wholePhysical) (wave : IntegerWavevector) : ℝ :=
  integerWaveNormSq wave * amplitude (wholeVelocity value.1) wave ^ 2

def gradientMass (value : wholePhysical) : ℝ := ∑' wave, gradientDensity value wave

def H1 (value : wholePhysical) : Prop := Summable (gradientDensity value)

theorem gradient_nonnegative (value : wholePhysical) (wave : IntegerWavevector) :
    0 ≤ gradientDensity value wave := mul_nonneg (integerWaveNormSq_nonneg wave) (sq_nonneg _)

theorem fractional_mass_bound (radius : ℕ) (value : wholePhysical) (regular : H1 value) :
    mass (modes radius) NativeMovingCriticalProductWeights.weight (amplitude (restrict radius value).1) ≤
      gradientMass value := by
  refine (fractional_mass_le_gradient (modes radius) (modes_zero radius) (restrict radius value)).trans ?_
  have same : mass (modes radius) integerWaveNormSq (amplitude (restrict radius value).1) =
      ∑ wave ∈ modes radius, gradientDensity value wave := by
    apply Finset.sum_congr rfl
    intro wave member
    simp only [gradientDensity, amplitude, restrict_row, if_pos member]
  rw [same]
  exact regular.sum_le_tsum _ (fun wave _ => gradient_nonnegative value wave)

def row (first last : wholePhysical) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (mixedFlux (wholeVelocity first.1) (wholeVelocity last.1) wave)

def finiteRow (radius : ℕ) (first last : wholePhysical) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (mixedFlux (restrict radius first).1 (restrict radius last).1 wave)

theorem row_tendsto (first last : wholePhysical) (wave : IntegerWavevector) :
    Tendsto (fun radius => finiteRow radius first last wave) atTop (𝓝 (row first last wave)) := by
  have continuity : Continuous (fun pair : ComplexVorticityHilbertState × ComplexVorticityHilbertState =>
      NativeCompleteStressBilinear.mixedCLM pair.1 pair.2) :=
    (NativeCompleteStressBilinear.mixedCLM.continuous.comp continuous_fst).clm_apply continuous_snd
  have tensor := continuity.tendsto _ |>.comp ((restrict_tendsto first).prodMk_nhds (restrict_tendsto last))
  have components : Tendsto
      (fun radius => mixedFlux (restrict radius first).1 (restrict radius last).1 wave) atTop
      (𝓝 (mixedFlux (wholeVelocity first.1) (wholeVelocity last.1) wave)) := by
    apply tendsto_pi_nhds.mpr
    intro output
    apply tendsto_pi_nhds.mpr
    intro input
    have read := (NativeCompleteStressCarrier.readCLM wave output input).continuous.tendsto _ |>.comp tensor
    simpa only [Function.comp_def, NativeCompleteStressBilinear.mixedCLM_apply, NativeCompleteStressCarrier.readCLM_apply,
      NativeCompleteStressBilinear.mixed_read] using read
  exact (projectedDivergenceCLM wave).continuous.tendsto _ |>.comp components

def negativeDensity (first last : wholePhysical) (wave : IntegerWavevector) : ℝ :=
  (integerWaveViscousMultiplier wave)⁻¹ * ‖euclideanCoordinateRow (row first last wave)‖ ^ 2

def finiteNegativeDensity (radius : ℕ) (first last : wholePhysical) (wave : IntegerWavevector) : ℝ :=
  (integerWaveViscousMultiplier wave)⁻¹ * ‖euclideanCoordinateRow (finiteRow radius first last wave)‖ ^ 2

theorem finite_bound (radius : ℕ) (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    (∑ wave ∈ modes radius, finiteNegativeDensity radius first last wave) ≤
      NativeMovingCriticalProductWeights.constant * gradientMass first * gradientMass last := by
  have convolved := NativeMovingCriticalProductWeights.convolution_control (modes radius) (modes_zero radius)
    (amplitude (restrict radius first).1) (amplitude (restrict radius last).1)
  have rows : (∑ wave ∈ modes radius, finiteNegativeDensity radius first last wave) ≤
      ∑ wave ∈ modes radius,
        convolution (modes radius) (amplitude (restrict radius first).1) (amplitude (restrict radius last).1) wave ^ 2 := by
    apply Finset.sum_le_sum
    intro wave member
    exact projected_row_bound (modes radius) (modes_zero radius) _ _ wave member
  refine (rows.trans convolved).trans ?_
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (fractional_mass_bound radius first firstH1)
      NativeMovingCriticalProductWeights.constant_nonnegative)
    (fractional_mass_bound radius last lastH1)
    (Finset.sum_nonneg fun wave _ => mul_nonneg (NativeMovingCriticalProductWeights.weight_nonnegative wave) (sq_nonneg _))
    (mul_nonneg NativeMovingCriticalProductWeights.constant_nonnegative (tsum_nonneg (gradient_nonnegative first)))

theorem density_nonnegative (first last : wholePhysical) (wave : IntegerWavevector) :
    0 ≤ negativeDensity first last wave :=
  mul_nonneg (inv_nonneg.mpr (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))) (sq_nonneg _)

theorem finite_density_nonnegative (radius : ℕ) (first last : wholePhysical) (wave : IntegerWavevector) :
    0 ≤ finiteNegativeDensity radius first last wave :=
  mul_nonneg (inv_nonneg.mpr (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))) (sq_nonneg _)

theorem observed_bound (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last)
    (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed, negativeDensity first last wave) ≤
      NativeMovingCriticalProductWeights.constant * gradientMass first * gradientMass last := by
  have component (wave : IntegerWavevector) : Tendsto
      (fun radius => finiteNegativeDensity radius first last wave) atTop (𝓝 (negativeDensity first last wave)) := by
    have coordinate := NativeCompleteStressAction.euclideanCLM.continuous.tendsto _ |>.comp (row_tendsto first last wave)
    exact (coordinate.norm.pow 2).const_mul _
  apply le_of_tendsto (tendsto_finsetSum observed (fun wave _ => component wave))
  have included : ∀ᶠ radius in atTop, ∀ wave ∈ observed, wave ∈ insert 0 (modes radius) := by
    apply (eventually_all_finset observed).mpr
    intro wave _
    by_cases zero : wave = 0
    · exact Eventually.of_forall fun _ => by simp [zero]
    · exact (nonzero_integerWave_eventually_mem_puncturedFrequencyCube wave zero).mono
        (fun _ member => Finset.mem_insert_of_mem member)
  filter_upwards [included] with radius inside
  have finite := Finset.sum_le_sum_of_subset_of_nonneg inside
    (fun wave _ _ => finite_density_nonnegative radius first last wave)
  have same : (∑ wave ∈ insert 0 (modes radius), finiteNegativeDensity radius first last wave) =
      ∑ wave ∈ modes radius, finiteNegativeDensity radius first last wave := by
    rw [Finset.sum_insert (modes_zero radius)]
    simp [finiteNegativeDensity, integerWaveViscousMultiplier]
  exact (finite.trans_eq same).trans (finite_bound radius first last firstH1 lastH1)

theorem negative_summable (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    Summable (negativeDensity first last) :=
  summable_of_sum_le (density_nonnegative first last) (observed_bound first last firstH1 lastH1)

theorem negative_mass_bound (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    (∑' wave, negativeDensity first last wave) ≤
      NativeMovingCriticalProductWeights.constant * gradientMass first * gradientMass last :=
  Real.tsum_le_of_sum_le (density_nonnegative first last) (observed_bound first last firstH1 lastH1)

def negativeRow (first last : wholePhysical) (wave : Wave) : ComplexCoordinateEuclidean :=
  (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ • euclideanCoordinateRow (row first last wave.1)

theorem negative_row_sq (first last : wholePhysical) (wave : Wave) :
    ‖negativeRow first last wave‖ ^ 2 = negativeDensity first last wave.1 := by
  have nonnegative : 0 ≤ integerWaveViscousMultiplier wave.1 :=
    mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave.1)
  rw [negativeRow, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt nonnegative]
  rfl

/-- The literal projected mixed divergence, with its physical inverse-gradient weight. -/
def negativeAction (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) : State :=
  ⟨negativeRow first last, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact ((negative_summable first last firstH1 lastH1).subtype (fun wave => wave ≠ 0)).congr
      (fun wave => (negative_row_sq first last wave).symm)⟩

theorem negativeAction_bound (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    ‖negativeAction first last firstH1 lastH1‖ ^ 2 ≤
      NativeMovingCriticalProductWeights.constant * gradientMass first * gradientMass last := by
  rw [norm_sq_sum]
  change (∑' wave : Wave, ‖negativeRow first last wave‖ ^ 2) ≤ _
  simp_rw [negative_row_sq]
  exact (Summable.tsum_subtype_le (negativeDensity first last) (fun wave => wave ≠ 0)
    (density_nonnegative first last) (negative_summable first last firstH1 lastH1)).trans
      (negative_mass_bound first last firstH1 lastH1)

end
end SaturationMonoid.NavierStokes.NativeWholeH1Mixed
