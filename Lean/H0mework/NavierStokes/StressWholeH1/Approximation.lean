import H0mework.NavierStokes.StressWholeH1.Mixed

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeH1Approximation

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeEndpointVelocityCarrier
open NativeWholeH1Mixed NativeMovingCriticalProduct NativeTimeJetCarrier NativeHigherTimeJets

noncomputable section

def project (radius : ℕ) (value : wholePhysical) : wholePhysical :=
  includeCLM (modes radius) (modes_closed radius) (restrict radius value)

theorem project_whole (radius : ℕ) (value : wholePhysical) :
    wholeVelocity (project radius value).1 = (restrict radius value).1 :=
  NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (physical_supported _ 0 (modes_zero radius))

theorem H1_project (radius : ℕ) (value : wholePhysical) : H1 (project radius value) := by
  apply summable_of_ne_finset_zero (s := modes radius)
  intro wave outside
  simp [gradientDensity, amplitude, project_whole, restrict_row, outside, euclideanCoordinateRow]

theorem H1_sub (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) : H1 (first - last) := by
  change Summable (fun wave => integerWaveNormSq wave * amplitude (wholeVelocity first.1) wave ^ 2) at firstH1
  change Summable (fun wave => integerWaveNormSq wave * amplitude (wholeVelocity last.1) wave ^ 2) at lastH1
  have generated := summable_wholeStateVorticityGradientDensity_sub
    (wholeVelocity first.1) (wholeVelocity last.1)
    (by simpa only [amplitude, euclideanCoordinateRow_norm_sq] using firstH1)
    (by simpa only [amplitude, euclideanCoordinateRow_norm_sq] using lastH1)
  change Summable (fun wave => integerWaveNormSq wave * amplitude (wholeVelocityCLM (first.1 - last.1)) wave ^ 2)
  rw [map_sub]
  simpa only [wholeVelocityCLM_apply, amplitude, euclideanCoordinateRow_norm_sq] using generated

theorem project_mass (radius : ℕ) (value : wholePhysical) :
    gradientMass (project radius value) = ∑ wave ∈ modes radius, gradientDensity value wave := by
  rw [gradientMass, tsum_eq_sum (s := modes radius) (fun wave outside => by
    simp [gradientDensity, amplitude, project_whole, restrict_row, outside, euclideanCoordinateRow])]
  apply Finset.sum_congr rfl
  intro wave inside
  simp only [gradientDensity, amplitude, project_whole, restrict_row, if_pos inside]

theorem project_mass_le (radius : ℕ) (value : wholePhysical) (regular : H1 value) :
    gradientMass (project radius value) ≤ gradientMass value := by
  rw [project_mass]
  exact regular.sum_le_tsum _ (fun wave _ => gradient_nonnegative value wave)

theorem project_mass_tendsto (value : wholePhysical) (regular : H1 value) :
    Tendsto (fun radius => gradientMass (project radius value)) atTop (𝓝 (gradientMass value)) := by
  have generated := regular.hasSum.comp integerWaveFrequencyCube_tendsto_atTop
  apply generated.congr'
  apply Eventually.of_forall
  intro radius
  change (∑ wave ∈ integerWaveFrequencyCube radius, gradientDensity value wave) = gradientMass (project radius value)
  rw [project_mass]
  symm
  apply Finset.sum_subset (Finset.erase_subset 0 (integerWaveFrequencyCube radius))
  intro wave inside outside
  have zero : wave = 0 := by simpa only [modes, puncturedIntegerWaveFrequencyCube, Finset.mem_erase, inside, and_true, not_not] using outside
  simp [gradientDensity, zero]

theorem difference_mass (radius : ℕ) (value : wholePhysical) (regular : H1 value) :
    gradientMass (value - project radius value) = gradientMass value - gradientMass (project radius value) := by
  have rows (wave : IntegerWavevector) : gradientDensity (value - project radius value) wave =
      gradientDensity value wave - gradientDensity (project radius value) wave := by
    change integerWaveNormSq wave * amplitude (wholeVelocityCLM (value.1 - (project radius value).1)) wave ^ 2 = _
    rw [map_sub]
    simp only [wholeVelocityCLM_apply, gradientDensity, amplitude, project_whole, restrict_row, lp.coeFn_sub, Pi.sub_apply]
    by_cases inside : wave ∈ modes radius <;> simp [inside, euclideanCoordinateRow]
  simp only [gradientMass, rows]
  exact regular.tsum_sub (H1_project radius value)

theorem difference_mass_tendsto (value : wholePhysical) (regular : H1 value) :
    Tendsto (fun radius => gradientMass (value - project radius value)) atTop (𝓝 0) := by
  simpa only [difference_mass _ value regular, sub_self] using
    (tendsto_const_nhds (x := gradientMass value)).sub (project_mass_tendsto value regular)

theorem row_sub_left (first other last : wholePhysical) (wave : IntegerWavevector) :
    row (first - other) last wave = row first last wave - row other last wave := by
  have tensors : mixedFlux (wholeVelocity (first - other).1) (wholeVelocity last.1) wave =
      mixedFlux (wholeVelocity first.1) (wholeVelocity last.1) wave -
        mixedFlux (wholeVelocity other.1) (wholeVelocity last.1) wave := by
    ext output input
    change mixedFluxLinear wave output input (wholeVelocityCLM (first.1 - other.1)) (wholeVelocity last.1) = _
    rw [map_sub, map_sub]
    rfl
  unfold row
  rw [tensors, map_sub]

theorem row_sub_right (first last other : wholePhysical) (wave : IntegerWavevector) :
    row first (last - other) wave = row first last wave - row first other wave := by
  have tensors : mixedFlux (wholeVelocity first.1) (wholeVelocity (last - other).1) wave =
      mixedFlux (wholeVelocity first.1) (wholeVelocity last.1) wave -
        mixedFlux (wholeVelocity first.1) (wholeVelocity other.1) wave := by
    ext output input
    change mixedFluxLinear wave output input (wholeVelocity first.1) (wholeVelocityCLM (last.1 - other.1)) = _
    rw [map_sub, map_sub]
    rfl
  unfold row
  rw [tensors, map_sub]

theorem negative_sub_left (first other last : wholePhysical) (firstH1 : H1 first)
    (otherH1 : H1 other) (lastH1 : H1 last) :
    negativeAction (first - other) last (H1_sub first other firstH1 otherH1) lastH1 =
      negativeAction first last firstH1 lastH1 - negativeAction other last otherH1 lastH1 := by
  apply lp.ext
  funext wave
  change _ • euclideanCoordinateRow (row (first - other) last wave.1) = _
  rw [row_sub_left]
  change _ • (euclideanCoordinateRow (row first last wave.1) - euclideanCoordinateRow (row other last wave.1)) = _
  rw [smul_sub]
  rfl

theorem negative_sub_right (first last other : wholePhysical) (firstH1 : H1 first)
    (lastH1 : H1 last) (otherH1 : H1 other) :
    negativeAction first (last - other) firstH1 (H1_sub last other lastH1 otherH1) =
      negativeAction first last firstH1 lastH1 - negativeAction first other firstH1 otherH1 := by
  apply lp.ext
  funext wave
  change _ • euclideanCoordinateRow (row first (last - other) wave.1) = _
  rw [row_sub_right]
  change _ • (euclideanCoordinateRow (row first last wave.1) - euclideanCoordinateRow (row first other wave.1)) = _
  rw [smul_sub]
  rfl

theorem normSquare_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (family : ℕ → E) (bound : ℕ → ℝ) (controlled : ∀ radius, ‖family radius‖ ^ 2 ≤ bound radius)
    (vanishes : Tendsto bound atTop (𝓝 0)) : Tendsto family atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun radius => Real.le_sqrt_of_sq_le (controlled radius))
  simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0 |>.comp vanishes

/-- Canonical restrictions converge in the complete negative-one action norm. -/
theorem negativeAction_project_tendsto (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    Tendsto (fun radius => negativeAction (project radius first) (project radius last)
      (H1_project radius first) (H1_project radius last)) atTop
      (𝓝 (negativeAction first last firstH1 lastH1)) := by
  let leftError radius := negativeAction (first - project radius first) last
    (H1_sub first _ firstH1 (H1_project radius first)) lastH1
  let rightError radius := negativeAction (project radius first) (last - project radius last)
    (H1_project radius first) (H1_sub last _ lastH1 (H1_project radius last))
  have leftVanishing : Tendsto leftError atTop (𝓝 0) := by
    apply normSquare_tendsto_zero leftError
      (fun radius => NativeMovingCriticalProductWeights.constant *
        gradientMass (first - project radius first) * gradientMass last)
      (fun radius => negativeAction_bound _ _ _ _)
    simpa only [mul_zero, zero_mul] using ((difference_mass_tendsto first firstH1).const_mul
      NativeMovingCriticalProductWeights.constant).mul_const (gradientMass last)
  have rightVanishing : Tendsto rightError atTop (𝓝 0) := by
    apply normSquare_tendsto_zero rightError
      (fun radius => NativeMovingCriticalProductWeights.constant *
        gradientMass first * gradientMass (last - project radius last))
    · intro radius
      refine (negativeAction_bound _ _ _ _).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (project_mass_le radius first firstH1)
          NativeMovingCriticalProductWeights.constant_nonnegative)
        (tsum_nonneg (gradient_nonnegative _))
    · simpa only [mul_zero] using (difference_mass_tendsto last lastH1).const_mul
        (NativeMovingCriticalProductWeights.constant * gradientMass first)
  have convergence := (tendsto_const_nhds (x := negativeAction first last firstH1 lastH1)).sub
    (leftVanishing.add rightVanishing)
  simp only [add_zero, sub_zero] at convergence
  apply convergence.congr'
  apply Eventually.of_forall
  intro radius
  dsimp only [leftError, rightError]
  rw [negative_sub_left first (project radius first) last firstH1 (H1_project radius first) lastH1,
    negative_sub_right (project radius first) last (project radius last) (H1_project radius first) lastH1 (H1_project radius last)]
  abel

end
end SaturationMonoid.NavierStokes.NativeWholeH1Approximation
