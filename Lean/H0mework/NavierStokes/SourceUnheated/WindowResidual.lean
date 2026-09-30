import H0mework.NavierStokes.SourceUnheated.WindowStress
import H0mework.NavierStokes.NativeAction.Correction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedWindowResidual
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeEndpointVelocityCarrier NativeCompleteStressCarrier NativeCompleteStressAction
open NativeForwardWindowJets NativeForwardWindowEvolution NativeHigherTimeJets NativeUnheatedStressProduct
noncomputable section
variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) := wholeVelocity (velocityJet seed order time)

theorem velocity_H1 (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    H1 (velocity seed order time) := by
  change Summable (fun wave => integerWaveNormSq wave * ‖euclideanCoordinateRow
    (wholeVelocity (velocityJet seed order time) wave)‖ ^ 2)
  simp_rw [euclideanCoordinateRow_norm_sq]
  exact NativeUnheatedWindowGradient.whole_gradient_summable seed order time valid

def mixedState (seed : GeneratedWholeRestartCurrent nu) (first last : ℕ) (time : ℝ) (valid : -1 ≤ time) : Space :=
  unweighted (velocity seed first time) (velocity seed last time) (wholeVelocity_zero _) (wholeVelocity_zero _)
    (velocity_H1 seed first time valid) (velocity_H1 seed last time valid)


theorem velocity_mass_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    gradientMass (velocity seed order time) ≤ NativeUnheatedWindowGradient.gradientBudget seed order time := by
  change (∑' wave, integerWaveNormSq wave * ‖euclideanCoordinateRow
    (wholeVelocity (velocityJet seed order time) wave)‖ ^ 2) ≤ _
  simp_rw [euclideanCoordinateRow_norm_sq]
  exact NativeUnheatedWindowGradient.whole_gradient_mass_bound seed order time valid

theorem mixedState_bound (seed : GeneratedWholeRestartCurrent nu) (first last : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    ‖mixedState seed first last time valid‖ ≤ 3 * Real.sqrt constant *
      (NativeUnheatedWindowGradient.gradientBudget seed first time + NativeUnheatedWindowGradient.gradientBudget seed last time) := by
  have first0 := NativeUnheatedWindowGradient.gradientBudget_nonnegative seed first time valid
  have last0 := NativeUnheatedWindowGradient.gradientBudget_nonnegative seed last time valid
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have normed := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (mixedState seed first last time valid)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at normed
  rw [normed]
  have paid := (tensor_summable _ _ (wholeVelocity_zero _) (wholeVelocity_zero _)
    (velocity_H1 seed first time valid) (velocity_H1 seed last time valid)).tsum_le_of_sum_le
    (tensor_observed_control _ _ (wholeVelocity_zero _) (wholeVelocity_zero _)
      (velocity_H1 seed first time valid) (velocity_H1 seed last time valid))
  apply paid.trans
  have masses := mul_le_mul (velocity_mass_bound seed first time valid) (velocity_mass_bound seed last time valid)
    (tsum_nonneg (density_nonnegative _)) first0
  have enlarged := mul_le_mul_of_nonneg_left masses (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) constant_nonnegative)
  rw [mul_assoc (9 * constant)]
  apply enlarged.trans
  have product : NativeUnheatedWindowGradient.gradientBudget seed first time * NativeUnheatedWindowGradient.gradientBudget seed last time ≤
      (NativeUnheatedWindowGradient.gradientBudget seed first time + NativeUnheatedWindowGradient.gradientBudget seed last time) ^ 2 := by
    nlinarith [mul_nonneg first0 last0]
  exact (mul_le_mul_of_nonneg_left product (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) constant_nonnegative)).trans_eq (by
    simp only [mul_pow, Real.sq_sqrt constant_nonnegative]
    ring)

def coefficients (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : NativeFluidStressFourierState :=
  NativeUnheatedWindowStress.stress seed order time - mixedTimeSum (velocity seed) (velocity seed) order time

def state (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) : Space :=
  NativeUnheatedWindowStress.state seed order time valid -
    ∑ rank ∈ Finset.range (order+1), (order.choose rank : ℝ) • mixedState seed rank (order-rank) time valid

theorem state_row (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    state seed order time valid wave (output,input) = coefficients seed order time wave output input := by
  let evaluate : Space →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate × Coordinate => ℂ) (output,input)).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave)
  change evaluate (state seed order time valid) = _
  rw [state, map_sub, map_sum]
  simp only [map_smul]
  change NativeUnheatedWindowStress.stress seed order time wave output input -
    (∑ rank ∈ Finset.range (order+1), (order.choose rank : ℝ) •
      mixedFlux (velocity seed rank time) (velocity seed (order-rank) time) wave output input) = _
  simp only [coefficients, Pi.sub_apply, mixedTimeSum, Complex.real_smul, Complex.ofReal_natCast]

theorem coefficients_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    coefficients seed 0 time = NativeCompleteCorrectionRead.residual (NativeForwardWindowSource.source seed time) := by
  funext wave output input
  simp only [coefficients, mixedTimeSum, Pi.sub_apply, Nat.zero_add, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.cast_one, one_mul, tsub_zero, mixedFlux_diagonal,
    NativeUnheatedWindowStress.stress, jet_zero, NativeCompleteCorrectionRead.residual, velocity, velocityJet]

theorem coefficients_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivAt (fun actual => coefficients seed order actual wave output input)
      (coefficients seed (order+1) time wave output input) time := by
  have next (rank : ℕ) (_ : rank ≤ order) : HasDerivWithinAt (velocity seed rank) (velocity seed (rank+1) time) univ time :=
    (wholeVelocityCLM.hasFDerivAt.comp_hasDerivAt time (velocityJet_hasDerivAt seed rank time)).hasDerivWithinAt
  have quadratic := (mixedTimeSum_hasDerivWithinAt (velocity seed) (velocity seed) order univ time next next wave output input).hasDerivAt (by simp)
  let read : FullSpace →L[ℝ] ℂ := (readCLM wave output input).comp
    (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)
  exact (read.hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed order time)).sub quadratic

theorem coefficients_iteratedDeriv (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    iteratedDeriv order (fun actual => NativeCompleteCorrectionRead.residual
      (NativeForwardWindowSource.source seed actual) wave output input) time = coefficients seed order time wave output input := by
  induction order generalizing time with
  | zero => rw [iteratedDeriv_zero, coefficients_zero]
  | succ order previous =>
      rw [iteratedDeriv_succ]
      have same : iteratedDeriv order (fun actual => NativeCompleteCorrectionRead.residual
          (NativeForwardWindowSource.source seed actual) wave output input) =
          fun actual => coefficients seed order actual wave output input := funext fun actual => by
        exact previous actual
      rw [same]
      exact (coefficients_hasDerivAt seed order time wave output input).deriv


def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : ℝ :=
  NativeUnheatedWindowStress.budget seed order time + ∑ rank ∈ Finset.range (order+1),
    (order.choose rank : ℝ) * (3 * Real.sqrt constant * (NativeUnheatedWindowGradient.gradientBudget seed rank time +
      NativeUnheatedWindowGradient.gradientBudget seed (order-rank) time))

theorem state_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    ‖state seed order time valid‖ ≤ budget seed order time := by
  apply (norm_sub_le _ _).trans
  apply add_le_add (NativeUnheatedWindowStress.state_bound seed order time valid)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro rank _
  rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (mixedState_bound seed rank (order-rank) time valid) (Nat.cast_nonneg _)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def componentSequence (value : Space) (entry : Coordinate × Coordinate) : NativePhysicalFourier.ScalarSequence :=
  ⟨fun wave => value wave entry, (lp.memℓp value).mono' fun wave => PiLp.norm_apply_le (value wave) entry⟩

def physicalField (value : Space) (entry : Coordinate × Coordinate) : NativePhysicalFourier.ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (componentSequence value entry)

theorem physicalField_fourier (value : Space) (entry : Coordinate × Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (physicalField value entry) wave = value wave entry := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact congrArg (fun sequence : NativePhysicalFourier.ScalarSequence => sequence wave)
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.apply_symm_apply (componentSequence value entry))

theorem physicalField_bound (value : Space) (entry : Coordinate × Coordinate) : ‖physicalField value entry‖ ≤ ‖value‖ := by
  rw [physicalField, LinearIsometryEquiv.norm_map]
  exact lp.norm_mono (by norm_num) fun wave => PiLp.norm_apply_le (value wave) entry

theorem stress_physical_fourier (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    UnitAddTorus.mFourierCoeff (physicalField (NativeUnheatedWindowStress.state seed order time valid) (output,input)) wave =
      read (jet seed order time).snd wave output input := by
  rw [physicalField_fourier, NativeUnheatedWindowStress.state_row]

theorem stress_physical_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (entry : Coordinate × Coordinate) :
    ‖physicalField (NativeUnheatedWindowStress.state seed order time valid) entry‖ ≤ NativeUnheatedWindowStress.budget seed order time :=
  (physicalField_bound _ _).trans (NativeUnheatedWindowStress.state_bound seed order time valid)

theorem residual_physical_fourier (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input : Coordinate) :
    UnitAddTorus.mFourierCoeff (physicalField (state seed order time valid) (output,input)) wave =
      iteratedDeriv order (fun actual => NativeCompleteCorrectionRead.residual
        (NativeForwardWindowSource.source seed actual) wave output input) time := by
  rw [physicalField_fourier, state_row, coefficients_iteratedDeriv]


theorem residual_physical_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) (valid : -1 ≤ time)
    (entry : Coordinate × Coordinate) : ‖physicalField (state seed order time valid) entry‖ ≤ budget seed order time :=
  (physicalField_bound _ _).trans (state_bound seed order time valid)

end
end SaturationMonoid.NavierStokes.NativeUnheatedWindowResidual
