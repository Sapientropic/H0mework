import H0mework.NavierStokes.Restart.VelocityWeakEndpoint
import H0mework.NavierStokes.Fourier.WholeVelocityPairDiagonalBudget
import H0mework.NavierStokes.Accumulation.ActualFourierConeAdvance

set_option autoImplicit false
open scoped ENNReal

namespace SaturationMonoid.NavierStokes.NativeEndpointVelocityCarrier

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget

noncomputable section

/-- The endpoint already stores velocity. This changes only the index and row norm. -/
def coefficients (endpoint : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if zero : wave = 0 then 0 else WithLp.ofLp (endpoint ⟨wave, zero⟩)

@[simp] theorem coefficients_zero (endpoint : WholeRestartVelocityEndpointState) :
    coefficients endpoint 0 = 0 := by simp [coefficients]

@[simp] theorem coefficients_nonzero (endpoint : WholeRestartVelocityEndpointState)
    (wave : NonzeroIntegerWavevector) :
    coefficients endpoint wave.1 = WithLp.ofLp (endpoint wave) := by
  have nonzero : wave.1 ≠ 0 := wave.2
  simp only [coefficients, dif_neg nonzero]

private theorem outside_zero (wave : IntegerWavevector)
    (outside : wave ∉ Set.range (Subtype.val : NonzeroIntegerWavevector → IntegerWavevector)) :
    wave = 0 := by
  by_contra nonzero
  exact outside ⟨⟨wave, nonzero⟩, rfl⟩

private theorem coefficients_summable (endpoint : WholeRestartVelocityEndpointState) :
    Summable (fun wave => ‖coefficients endpoint wave‖ ^ 2) := by
  apply (Subtype.val_injective.summable_iff (fun wave outside => by
    rw [outside_zero wave outside, coefficients_zero, norm_zero, zero_pow (by decide)])).mp
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun wave : NonzeroIntegerWavevector => ?_)
    (show Summable (fun wave => ‖endpoint wave‖ ^ 2) by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using endpoint.2.summable (by norm_num))
  rw [coefficients_nonzero]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (endpoint wave))).2
  intro coordinate
  exact PiLp.norm_apply_le (endpoint wave) coordinate

def wholeVelocity (endpoint : WholeRestartVelocityEndpointState) : ComplexVorticityHilbertState :=
  ⟨coefficients endpoint, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using coefficients_summable endpoint⟩

@[simp] theorem wholeVelocity_zero (endpoint : WholeRestartVelocityEndpointState) :
    wholeVelocity endpoint 0 = 0 := coefficients_zero endpoint

@[simp] theorem wholeVelocity_nonzero (endpoint : WholeRestartVelocityEndpointState)
    (wave : NonzeroIntegerWavevector) (coordinate : Coordinate) :
    wholeVelocity endpoint wave.1 coordinate = endpoint wave coordinate := by
  change coefficients endpoint wave.1 coordinate = _
  rw [coefficients_nonzero]

theorem wholeVelocity_mass (endpoint : WholeRestartVelocityEndpointState) :
    wholeVorticityEuclideanMass (wholeVelocity endpoint) = ‖endpoint‖ ^ 2 := by
  have nonzero : HasSum
      (fun wave : NonzeroIntegerWavevector =>
        vorticityRowAmplitude (wholeVelocity endpoint) wave.1 ^ 2) (‖endpoint‖ ^ 2) := by
    have sums : HasSum (fun wave => ‖endpoint wave‖ ^ 2) (‖endpoint‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) endpoint
    apply sums.congr_fun
    intro wave
    rw [vorticityRowAmplitude_sq,
      ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    change complexCoordinateAmplitudeSq (coefficients endpoint wave.1) = ‖endpoint wave‖ ^ 2
    rw [coefficients_nonzero, ← euclideanCoordinateRow_norm_sq]
    rfl
  have inclusion : Function.Injective
      (Subtype.val : NonzeroIntegerWavevector → IntegerWavevector) := Subtype.val_injective
  have full := (inclusion.hasSum_iff (f := fun wave =>
    vorticityRowAmplitude (wholeVelocity endpoint) wave ^ 2) (fun wave outside => by
    rw [outside_zero wave outside, vorticityRowAmplitude_sq, wholeVelocity_zero]
    simp [complexCoordinateVectorNormSq])).mp nonzero
  exact full.tsum_eq

theorem wholeVelocity_reality (endpoint : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality endpoint) :
    FiniteStateFourierReality (wholeVelocity endpoint) := by
  intro wave
  funext coordinate
  by_cases zero : wave = 0
  · subst wave
    simp [vectorConj, waveNeg]
  · have negative : waveNeg wave ≠ 0 := fun eq => zero ((waveNeg_eq_zero_iff wave).mp eq)
    change coefficients endpoint (waveNeg wave) coordinate =
      star (coefficients endpoint wave coordinate)
    simp only [coefficients, dif_neg negative, dif_neg zero]
    exact reality ⟨wave, zero⟩ coordinate

theorem wholeVelocity_punctured (state : ComplexVorticityHilbertState) :
    wholeVelocity (puncturedWholeVelocityEuclideanState state) =
      wholeBiotSavartVelocityState state := by
  apply lp.ext
  funext wave
  by_cases zero : wave = 0
  · subst wave
    simp [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient]
  · funext coordinate
    rw [wholeVelocity_nonzero _ ⟨wave, zero⟩]
    rfl

theorem wholeVelocity_norm_le (endpoint : WholeRestartVelocityEndpointState) :
    ‖wholeVelocity endpoint‖ ≤ ‖endpoint‖ := by
  have square :=
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance.wholeState_norm_sq_le_wholeVorticityEuclideanMass
      (wholeVelocity endpoint)
  rw [wholeVelocity_mass] at square
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp square

def wholeVelocityCLM : WholeRestartVelocityEndpointState →L[ℝ] ComplexVorticityHilbertState :=
  LinearMap.mkContinuous
    { toFun := wholeVelocity
      map_add' := by
        intro left right
        apply lp.ext
        funext wave coordinate
        change coefficients (left + right) wave coordinate =
          coefficients left wave coordinate + coefficients right wave coordinate
        by_cases zero : wave = 0 <;> simp [coefficients, zero]
      map_smul' := by
        intro scalar endpoint
        apply lp.ext
        funext wave coordinate
        by_cases zero : wave = 0 <;> simp [wholeVelocity, coefficients, zero] }
    1 (fun endpoint => by
      change ‖wholeVelocity endpoint‖ ≤ 1 * ‖endpoint‖
      simpa only [one_mul] using wholeVelocity_norm_le endpoint)

@[simp] theorem wholeVelocityCLM_apply (endpoint : WholeRestartVelocityEndpointState) :
    wholeVelocityCLM endpoint = wholeVelocity endpoint := rfl

end
end SaturationMonoid.NavierStokes.NativeEndpointVelocityCarrier
