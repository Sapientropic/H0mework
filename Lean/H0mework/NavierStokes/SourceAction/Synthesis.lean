import H0mework.NavierStokes.PhysicalReadout.Continuous
import H0mework.NavierStokes.SourceAction.Convolution
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeFullOrderSynthesis

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel
open NativePhysicalFourier NativePhysicalContinuous NativeFullOrderAction

noncomputable section

def circlePoint (point : PhysicalSpace) : Torus := fun coordinate => (point coordinate : UnitAddCircle)

def spatialField (velocity : ComplexVorticityHilbertState) (point : PhysicalSpace) : PhysicalSpace :=
  continuousField velocity (circlePoint point)

def profile (time : ℝ) : ℂ := Complex.exp (time * Complex.I)

theorem profile_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) profile := by
  unfold profile
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem profile_deriv (time : ℝ) : HasDerivAt profile (Complex.I * profile time) time := by
  have actual := ((Complex.ofRealCLM.hasFDerivAt.hasDerivAt).mul_const Complex.I).cexp (x := time)
  unfold profile
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, mul_one, mul_comm] using actual

theorem profile_iteratedDeriv (order : ℕ) :
    iteratedDeriv order profile = fun time => Complex.I ^ order * profile time := by
  induction order with
  | zero => simp
  | succ order ih =>
    rw [iteratedDeriv_succ, ih]
    funext time
    rw [((profile_deriv time).const_mul (Complex.I ^ order)).deriv]
    simp only [pow_succ]
    ring

theorem profile_iterated_norm (order : ℕ) (time : ℝ) :
    ‖iteratedFDeriv ℝ order profile time‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, profile_iteratedDeriv]
  simp [profile, norm_pow, Complex.norm_exp]

def phase (wave : IntegerWavevector) : PhysicalSpace →L[ℝ] ℝ :=
  (2 * Real.pi) • ∑ coordinate : Coordinate, (wave coordinate : ℝ) •
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) coordinate

theorem phase_apply (wave : IntegerWavevector) (point : PhysicalSpace) :
    phase wave point = 2 * Real.pi * ∑ coordinate : Coordinate, (wave coordinate : ℝ) * point coordinate := by
  simp [phase]

theorem phase_norm_le (wave : IntegerWavevector) :
    ‖phase wave‖ ≤ 2 * Real.pi * frequencySize wave := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [frequencySize_nonneg wave])
  intro point
  rw [phase_apply, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have bound : |∑ coordinate : Coordinate, (wave coordinate : ℝ) * point coordinate| ≤
      (∑ coordinate : Coordinate, |(wave coordinate : ℝ)|) * ‖point‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro coordinate _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le point coordinate) (abs_nonneg _)
  have enlarged : (∑ coordinate : Coordinate, |(wave coordinate : ℝ)|) * ‖point‖ ≤
      frequencySize wave * ‖point‖ := by
    unfold frequencySize
    nlinarith [norm_nonneg point]
  have scaled := mul_le_mul_of_nonneg_left (bound.trans enlarged) (by positivity : 0 ≤ 2 * Real.pi)
  simpa only [mul_assoc, Real.norm_eq_abs] using scaled

theorem monomial_phase (wave : IntegerWavevector) (point : PhysicalSpace) :
    UnitAddTorus.mFourier wave (circlePoint point) = profile (phase wave point) := by
  unfold UnitAddTorus.mFourier circlePoint
  simp only [ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  unfold profile
  rw [phase_apply]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

def monomial (wave : IntegerWavevector) (point : PhysicalSpace) : ℂ :=
  UnitAddTorus.mFourier wave (circlePoint point)

theorem monomial_smooth (wave : IntegerWavevector) : ContDiff ℝ (↑(⊤ : ℕ∞)) (monomial wave) := by
  have same : monomial wave = profile ∘ phase wave := funext (monomial_phase wave)
  rw [same]
  exact profile_smooth.comp (phase wave).contDiff

theorem monomial_iterated_bound (wave : IntegerWavevector) (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (monomial wave) point‖ ≤ (2 * Real.pi * frequencySize wave) ^ order := by
  have same : monomial wave = profile ∘ phase wave := funext (monomial_phase wave)
  rw [same, (phase wave).iteratedFDeriv_comp_right profile_smooth point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply ((iteratedFDeriv ℝ order profile (phase wave point)).norm_compContinuousLinearMap_le
    (fun _ => phase wave)).trans
  rw [profile_iterated_norm]
  simp only [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (phase_norm_le wave) order

def value (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) (z : ℂ) : PhysicalSpace :=
  WithLp.toLp 2 fun coordinate => (velocity wave coordinate * z).re

theorem value_norm_le (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) (z : ℂ) :
    ‖value velocity wave z‖ ≤ amplitude velocity wave * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (vorticityRowAmplitude_nonneg _ _) (norm_nonneg _))).mp
  rw [mul_pow]
  change ‖value velocity wave z‖ ^ 2 ≤ vorticityRowAmplitude velocity wave ^ 2 * ‖z‖ ^ 2
  rw [vorticityRowAmplitude_sq, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    EuclideanSpace.norm_sq_eq]
  unfold complexCoordinateAmplitudeSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro coordinate _
  change ‖(velocity wave coordinate * z).re‖ ^ 2 ≤ _
  rw [Complex.normSq_eq_norm_sq, ← mul_pow, ← norm_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (Complex.abs_re_le_norm _)

def valueCLM (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ℂ →L[ℝ] PhysicalSpace :=
  LinearMap.mkContinuous
    { toFun := value velocity wave
      map_add' := by
        intro a b
        apply PiLp.ext
        intro coordinate
        change (velocity wave coordinate * (a + b)).re = _
        simp [mul_add, value]
      map_smul' := by
        intro scalar z
        apply PiLp.ext
        intro coordinate
        change (velocity wave coordinate * (scalar • z)).re = _
        simp [value, Complex.real_smul, mul_comm, mul_assoc]
        ring }
    (amplitude velocity wave) (value_norm_le velocity wave)

theorem valueCLM_norm_le (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ‖valueCLM velocity wave‖ ≤ amplitude velocity wave :=
  ContinuousLinearMap.opNorm_le_bound _ (vorticityRowAmplitude_nonneg _ _) (value_norm_le velocity wave)

def mode (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    PhysicalSpace → PhysicalSpace := valueCLM velocity wave ∘ monomial wave

theorem mode_eq (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) (point : PhysicalSpace) :
    mode velocity wave point = realMode velocity wave (circlePoint point) := rfl

theorem mode_smooth (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (mode velocity wave) :=
  (valueCLM velocity wave).contDiff.comp (monomial_smooth wave)

def jetMajorant (velocity : ComplexVorticityHilbertState) (order : ℕ) (wave : IntegerWavevector) : ℝ :=
  (2 * Real.pi) ^ order * (frequencySize wave ^ order * amplitude velocity wave)

theorem mode_iterated_bound (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector)
    (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (mode velocity wave) point‖ ≤ jetMajorant velocity order wave := by
  unfold mode
  rw [(valueCLM velocity wave).iteratedFDeriv_comp_left (monomial_smooth wave).contDiffAt
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply ((valueCLM velocity wave).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ order (monomial wave) point)).trans
  apply (mul_le_mul (valueCLM_norm_le velocity wave) (monomial_iterated_bound wave order point)
    (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)).trans_eq
  unfold jetMajorant
  rw [mul_pow]
  ring

theorem spatialField_eq_tsum (velocity : ComplexVorticityHilbertState)
    (paid : Summable (amplitude velocity)) :
    spatialField velocity = fun point => ∑' wave, mode velocity wave point := by
  funext point
  unfold spatialField
  rw [continuousField_eq_tsum velocity paid]
  exact (ContinuousMap.evalCLM ℝ (circlePoint point)).map_tsum (realMode_summable velocity paid)

theorem spatialField_smooth (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * amplitude velocity wave) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField velocity) := by
  have paid : Summable (amplitude velocity) := by simpa only [pow_zero, one_mul] using moments 0
  rw [spatialField_eq_tsum velocity paid]
  exact contDiff_tsum (N := (⊤ : ℕ∞)) (mode_smooth velocity)
    (fun order _ => (moments order).mul_left ((2 * Real.pi) ^ order))
    (fun order wave point _ => mode_iterated_bound velocity wave order point)

theorem spatialField_iterated_eq (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * amplitude velocity wave)
    (order : ℕ) (point : PhysicalSpace) :
    iteratedFDeriv ℝ order (spatialField velocity) point =
      ∑' wave, iteratedFDeriv ℝ order (mode velocity wave) point := by
  have paid : Summable (amplitude velocity) := by simpa only [pow_zero, one_mul] using moments 0
  rw [spatialField_eq_tsum velocity paid]
  exact iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) (mode_smooth velocity)
    (fun order _ => (moments order).mul_left ((2 * Real.pi) ^ order))
    (fun order wave point _ => mode_iterated_bound velocity wave order point) le_top point

theorem spatialField_iterated_bound (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * amplitude velocity wave)
    (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (spatialField velocity) point‖ ≤
      (2 * Real.pi) ^ order * ∑' wave, frequencySize wave ^ order * amplitude velocity wave := by
  rw [spatialField_iterated_eq velocity moments order point]
  have paid := (moments order).mul_left ((2 * Real.pi) ^ order)
  apply (norm_tsum_le_tsum_norm (paid.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun wave => mode_iterated_bound velocity wave order point))).trans
  calc
    _ ≤ ∑' wave, jetMajorant velocity order wave :=
      (paid.of_nonneg_of_le (fun _ => norm_nonneg _) (fun wave => mode_iterated_bound velocity wave order point)).tsum_le_tsum
        (fun wave => mode_iterated_bound velocity wave order point) paid
    _ = _ := tsum_mul_left

theorem frequencySize_pos (wave : IntegerWavevector) : 0 < frequencySize wave := by
  unfold frequencySize
  positivity

theorem normSq_le_frequencySize_sq (wave : IntegerWavevector) :
    integerWaveNormSq wave ≤ frequencySize wave ^ 2 := by
  have scalar := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset Coordinate))
    (f := fun coordinate => |(wave coordinate : ℝ)|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at scalar
  have positive : 0 ≤ ∑ coordinate : Coordinate, |(wave coordinate : ℝ)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold integerWaveNormSq frequencySize
  nlinarith

def decay (wave : IntegerWavevector) : ℝ := (frequencySize wave ^ 2)⁻¹ ^ 2

theorem decay_summable : Summable decay := by
  have kernel := summable_integerWaveCriticalKernel.update 0 1
  apply kernel.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro wave
  by_cases zero : wave = 0
  · subst wave
    simp [frequencySize]
  · rw [Function.update_of_ne zero]
    unfold integerWaveCriticalKernel
    apply pow_le_pow_left₀ (inv_nonneg.mpr (sq_nonneg _))
    exact inv_anti₀ (integerWaveNormSq_pos zero) (normSq_le_frequencySize_sq wave)

theorem moment_pair_bound (velocity : ComplexVorticityHilbertState) (order : ℕ) (wave : IntegerWavevector) :
    frequencySize wave ^ order * amplitude velocity wave ≤
      (frequencySize wave ^ (2 * (order + 2)) * complexCoordinateAmplitudeSq (velocity wave) + decay wave) / 2 := by
  let f := frequencySize wave
  let a := amplitude velocity wave
  have positive : 0 < f := frequencySize_pos wave
  have pair : f ^ order * a = (f ^ (order + 2) * a) * (f ^ 2)⁻¹ := by
    rw [pow_add]
    field_simp
  have square := sq_nonneg (f ^ (order + 2) * a - (f ^ 2)⁻¹)
  have amplitudeSquare : a ^ 2 = complexCoordinateAmplitudeSq (velocity wave) := by
    exact (vorticityRowAmplitude_sq velocity wave).trans
      (complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq _).symm
  change f ^ order * a ≤ (f ^ (2 * (order + 2)) * complexCoordinateAmplitudeSq (velocity wave) + (f ^ 2)⁻¹ ^ 2) / 2
  rw [pair]
  have highSquare : (f ^ (order + 2) * a) ^ 2 =
      f ^ (2 * (order + 2)) * complexCoordinateAmplitudeSq (velocity wave) := by
    rw [mul_pow, amplitudeSquare, ← pow_mul, Nat.mul_comm (order + 2) 2]
  nlinarith

theorem summable_moment_of_square (velocity : ComplexVorticityHilbertState) (order : ℕ)
    (paid : Summable fun wave => frequencySize wave ^ (2 * (order + 2)) *
      complexCoordinateAmplitudeSq (velocity wave)) :
    Summable fun wave => frequencySize wave ^ order * amplitude velocity wave := by
  apply ((paid.add decay_summable).div_const 2).of_nonneg_of_le
  · intro wave
    exact mul_nonneg (pow_nonneg (frequencySize_pos wave).le _) (vorticityRowAmplitude_nonneg _ _)
  · exact moment_pair_bound velocity order

theorem moment_le_square_payment (velocity : ComplexVorticityHilbertState) (order : ℕ)
    (paid : Summable fun wave => frequencySize wave ^ (2 * (order + 2)) *
      complexCoordinateAmplitudeSq (velocity wave)) :
    (∑' wave, frequencySize wave ^ order * amplitude velocity wave) ≤
      ((∑' wave, frequencySize wave ^ (2 * (order + 2)) * complexCoordinateAmplitudeSq (velocity wave)) +
        ∑' wave, decay wave) / 2 := by
  have bound := (summable_moment_of_square velocity order paid).tsum_le_tsum
    (moment_pair_bound velocity order) ((paid.add decay_summable).div_const 2)
  simpa only [tsum_div_const, Summable.tsum_add paid decay_summable] using bound

theorem spatialField_smooth_of_square (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (velocity wave)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField velocity) :=
  spatialField_smooth velocity fun order => summable_moment_of_square velocity order (moments (order + 2))

theorem spatialField_bound_of_square (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (velocity wave))
    (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order (spatialField velocity) point‖ ≤
      (2 * Real.pi) ^ order *
        (((∑' wave, frequencySize wave ^ (2 * (order + 2)) * complexCoordinateAmplitudeSq (velocity wave)) +
          ∑' wave, decay wave) / 2) := by
  apply (spatialField_iterated_bound velocity
    (fun order => summable_moment_of_square velocity order (moments (order + 2))) order point).trans
  exact mul_le_mul_of_nonneg_left
    (moment_le_square_payment velocity order (moments (order + 2))) (by positivity)

theorem mode_word_eq (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector)
    (order : ℕ) (point : PhysicalSpace) (directions : Fin order → PhysicalSpace) :
    iteratedFDeriv ℝ order (mode velocity wave) point directions =
      value velocity wave ((∏ index, phase wave (directions index)) •
        (Complex.I ^ order * UnitAddTorus.mFourier wave (circlePoint point))) := by
  have hOrder : (order : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)
  unfold mode
  rw [(valueCLM velocity wave).iteratedFDeriv_comp_left (monomial_smooth wave).contDiffAt hOrder]
  change value velocity wave ((iteratedFDeriv ℝ order (monomial wave) point) directions) = _
  have same : monomial wave = profile ∘ phase wave := funext (monomial_phase wave)
  rw [same, (phase wave).iteratedFDeriv_comp_right profile_smooth point hOrder]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, profile_iteratedDeriv, monomial_phase]

def evaluateJet (order : ℕ) (directions : Fin order → PhysicalSpace) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => PhysicalSpace) PhysicalSpace →L[ℝ] PhysicalSpace :=
  LinearMap.mkContinuous
    { toFun := fun jet => jet directions
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ index, ‖directions index‖) fun jet => by
      change ‖jet directions‖ ≤ (∏ index, ‖directions index‖) * ‖jet‖
      simpa only [mul_comm] using jet.le_opNorm directions

theorem spatialField_word_eq (velocity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * amplitude velocity wave)
    (order : ℕ) (point : PhysicalSpace) (directions : Fin order → PhysicalSpace) :
    iteratedFDeriv ℝ order (spatialField velocity) point directions =
      ∑' wave, value velocity wave ((∏ index, phase wave (directions index)) •
        (Complex.I ^ order * UnitAddTorus.mFourier wave (circlePoint point))) := by
  have derivatives : Summable fun wave => iteratedFDeriv ℝ order (mode velocity wave) point :=
    ((moments order).mul_left ((2 * Real.pi) ^ order)).of_norm_bounded
      (fun wave => mode_iterated_bound velocity wave order point)
  have written := (evaluateJet order directions).map_tsum derivatives
  rw [spatialField_iterated_eq velocity moments order point]
  change (evaluateJet order directions) (∑' wave, iteratedFDeriv ℝ order (mode velocity wave) point) = _
  rw [written]
  apply tsum_congr
  intro wave
  exact mode_word_eq velocity wave order point directions

end
end SaturationMonoid.NavierStokes.NativeFullOrderSynthesis
