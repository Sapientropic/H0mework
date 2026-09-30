import H0mework.NavierStokes.WindowSourceGreen.FormTest
import H0mework.NavierStokes.UnheatedWriterSobolev.Velocity
import H0mework.NavierStokes.UnheatedWriterTree.HeatKernel
import H0mework.NavierStokes.WindowSchurFirst.Jet

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowGreenSourceForm
open NativeUnheatedTreeRieszKernel (Wave)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeWindowGreenProduct NativeUnheatedSexticLatticePower NativeEndpointVelocityCarrier
open NativeForwardWindowEvolution NativePhysicalFourier
noncomputable section
variable {nu : Viscosity}

def sourceKernel : Kernel where
  value k p := (2*(2*Real.pi))*NativeUnheatedTreeRieszKernel.kernel k p
  cap := (2*(2*Real.pi))^2*NativeUnheatedRieszKernel.constant
  cap_nonnegative := by positivity [NativeUnheatedRieszKernel.constant_nonnegative]
  nonnegative k p := mul_nonneg (by positivity) (NativeUnheatedTreeRieszKernel.kernel_nonnegative k p)
  squares k F := by
    simp only [mul_pow,← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (NativeUnheatedTreeRieszKernel.kernel_square_sum k F) (by positivity)

theorem radical_sub (k p : Wave) : radical (k-p) ≤ 2*radical k*radical p := by
  have sub : mass (k-p) ≤ 2*(mass k+mass p) := by
    simpa only [sub_eq_add_neg,mass,integerWaveNormSq,Pi.neg_apply,Int.cast_neg,neg_sq] using
      NativeUnheatedTreeHeatKernel.mass_add k (-p)
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity [radical_positive k,radical_positive p])
  rw [mul_pow,mul_pow,radical_fourth,radical_fourth,radical_fourth]
  nlinarith [mass_one k,mass_one p,mul_nonneg (sub_nonneg.mpr (mass_one k)) (sub_nonneg.mpr (mass_one p))]

theorem inverse_kernel (k p : Wave) : density 3 p*density 1 (k-p) ≤
    2*NativeUnheatedTreeRieszKernel.kernel k p := by
  have paid := radical_sub k p
  apply (mul_le_mul_iff_right₀ (show 0 < radical p^3*radical (k-p)^2 by positivity [radical_positive p,radical_positive (k-p)])).mp
  convert! paid using 1 <;> simp only [NativeUnheatedTreeRieszKernel.kernel,density] <;>
    field_simp [(radical_positive p).ne',(radical_positive (k-p)).ne']

def productKernel (direction : Coordinate) (k p : Wave) : ℂ :=
  (density 3 p*density 3 (k-p)) • NativePhysicalGradient.multiplier (k-p) direction

theorem productKernel_bound (direction : Coordinate) (k p : Wave) : ‖productKernel direction k p‖ ≤ sourceKernel.value k p := by
  have component : ((k-p) direction : ℝ)^2 ≤ integerWaveNormSq (k-p) :=
    Finset.single_le_sum (fun coordinate _ => sq_nonneg (((k-p) coordinate : ℝ))) (Finset.mem_univ direction)
  have multiplier : ‖NativePhysicalGradient.multiplier (k-p) direction‖ ≤ (2*Real.pi)*radical (k-p)^2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity [radical_positive (k-p)])).mp
    have same : ((2*Real.pi)*radical (k-p)^2)^2 = (2*Real.pi)^2*mass (k-p) := by
      rw [mul_pow,← pow_mul,show (2 : ℕ)*2=4 from rfl,radical_fourth]
    rw [NativePhysicalGradient.multiplier_norm_sq,same]
    exact mul_le_mul_of_nonneg_left (component.trans (by unfold mass; linarith)) (sq_nonneg _)
  rw [productKernel,norm_smul,Real.norm_of_nonneg (mul_nonneg (density_positive 3 p).le (density_positive 3 (k-p)).le)]
  apply (mul_le_mul_of_nonneg_left multiplier (mul_nonneg (density_positive 3 p).le (density_positive 3 (k-p)).le)).trans
  have simplify : (density 3 p*density 3 (k-p))*((2*Real.pi)*radical (k-p)^2) =
      (2*Real.pi)*(density 3 p*density 1 (k-p)) := by
    unfold density
    field_simp [(radical_positive (k-p)).ne']
  rw [simplify]
  exact (mul_le_mul_of_nonneg_left (inverse_kernel k p) (by positivity : 0 ≤ 2*Real.pi)).trans_eq (by dsimp only [sourceKernel]; ring)

def velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) := wholeVelocity (velocityJet seed 0 time)

theorem input_square_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (coordinate : Coordinate) (k : Wave) :
    ‖(radical k^3 : ℝ) • velocity seed time k coordinate‖^2 ≤ NativeWindowSobolevVelocity.wholeDensity seed 0 time k := by
  have component : ‖velocity seed time k coordinate‖^2 ≤ complexCoordinateAmplitudeSq (velocity seed time k) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)
  have factor : (radical k^3)^2 = mass k*Real.sqrt (mass k) := by
    rw [show (radical k^3)^2=radical k^4*radical k^2 by ring,radical_fourth,radical_square]
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,factor]
  exact mul_le_mul_of_nonneg_left component (by positivity [mass_positive k])

def input (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) (coordinate : Coordinate) : ComplexSpace :=
  ⟨fun k => (radical k^3 : ℝ) • velocity seed time k coordinate, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (NativeWindowSobolevVelocity.whole_summable seed 0 time valid).of_nonneg_of_le
      (fun _ => sq_nonneg _) (input_square_bound seed time coordinate))⟩

theorem input_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (coordinate : Coordinate) : ‖input seed time valid coordinate‖^2 ≤ NativeWindowSobolevVelocity.budget seed 0 horizon := by
  rw [NativeWindowGreenTestForm.norm_square]
  exact ((NativeWindowGreenTestForm.square_summable (input seed time valid coordinate)).tsum_le_tsum
    (input_square_bound seed time coordinate) (NativeWindowSobolevVelocity.whole_summable seed 0 time valid)).trans
    (NativeWindowSobolevVelocity.whole_bound_on_interval seed 0 time horizon valid before)

def coefficient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) (direction : Coordinate) : ComplexSpace :=
  (1/4 : ℝ) • ∑ coordinate : Coordinate, complexValue sourceKernel (productKernel direction) (productKernel_bound direction)
    (input seed time valid coordinate) (input seed time valid coordinate)

theorem coefficient_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) (k : Wave) : coefficient seed time valid direction k =
      (1/4 : ℝ) • ∑ coordinate : Coordinate, ∑' p,
        velocity seed time p coordinate*NativePhysicalGradient.multiplier (k-p) direction*velocity seed time (k-p) coordinate := by
  change (1/4 : ℝ) • (∑ coordinate : Coordinate, complexRow (productKernel direction)
    (input seed time valid coordinate) (input seed time valid coordinate) k) = _
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  apply tsum_congr
  intro p
  change ((density 3 p*density 3 (k-p)) • NativePhysicalGradient.multiplier (k-p) direction)*
    ((radical p^3 : ℝ) • velocity seed time p coordinate)*
      ((radical (k-p)^3 : ℝ) • velocity seed time (k-p) coordinate) = _
  simp only [density,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow]
  field_simp [(show (radical p : ℂ) ≠ 0 by exact_mod_cast (radical_positive p).ne'),
    (show (radical (k-p) : ℂ) ≠ 0 by exact_mod_cast (radical_positive (k-p)).ne')]

def coefficientBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  (3/4 : ℝ)*Real.sqrt sourceKernel.cap*max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon)

theorem coefficient_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (valid : -1 < time)
    (before : time ≤ horizon) (direction : Coordinate) : ‖coefficient seed time valid direction‖ ≤ coefficientBudget seed horizon := by
  have each (coordinate : Coordinate) : ‖complexValue sourceKernel (productKernel direction) (productKernel_bound direction)
      (input seed time valid coordinate) (input seed time valid coordinate)‖ ≤
      Real.sqrt sourceKernel.cap*max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon) := by
    have paid := complexValue_norm sourceKernel (productKernel direction) (productKernel_bound direction)
      (input seed time valid coordinate) (input seed time valid coordinate)
    rw [mul_assoc,← pow_two] at paid
    exact paid.trans (mul_le_mul_of_nonneg_left ((input_bound seed time horizon valid before coordinate).trans
      (le_max_right _ _)) (Real.sqrt_nonneg sourceKernel.cap))
  rw [coefficient,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num : (0 : ℝ) ≤ 1/4)).trans
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun coordinate _ => each coordinate)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at bound
  exact (mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 1/4)).trans_eq (by unfold coefficientBudget; ring)

open MeasureTheory UnitAddTorus NativeWindowHistoryFirstJet
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def physicalCoefficient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) (point : Torus) : ℂ :=
  (1/4 : ℝ) • ∑ coordinate : Coordinate,
    scalarField (velocity seed time) coordinate point*physicalJet seed time valid.le direction coordinate point

theorem physicalCoefficient_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) : Integrable (physicalCoefficient seed time valid direction) := by
  exact (integrable_finsetSum Finset.univ (fun coordinate _ => NativeFourierProduct.product_integrable
    (scalarField (velocity seed time) coordinate) (physicalJet seed time valid.le direction coordinate))).smul (1/4 : ℝ)

theorem coefficient_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (direction : Coordinate) (k : Wave) : coefficient seed time valid direction k =
      mFourierCoeff (physicalCoefficient seed time valid direction) k := by
  have each (coordinate : Coordinate) : mFourierCoeff (fun point => scalarField (velocity seed time) coordinate point*
      physicalJet seed time valid.le direction coordinate point) k =
        ∑' p, velocity seed time p coordinate*NativePhysicalGradient.multiplier (k-p) direction*velocity seed time (k-p) coordinate := by
    rw [NativeFourierProduct.product_coeff]
    simp only [scalarField_fourier,physicalJet_fourier,velocity,velocityJet,NativeForwardWindowJets.jet_zero,mul_assoc]
  have modulated (coordinate : Coordinate) : Integrable (fun point : Torus => mFourier (-k) point*
      (scalarField (velocity seed time) coordinate point*physicalJet seed time valid.le direction coordinate point)) :=
    (NativeFourierProduct.product_integrable _ _).bdd_mul (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun point => ((mFourier (-k)).norm_coe_le_norm point).trans_eq mFourier_norm)
  rw [coefficient_read]
  simp_rw [← each]
  simp only [mFourierCoeff,physicalCoefficient,smul_eq_mul]
  rw [← integral_finsetSum _ (fun coordinate _ => modulated coordinate)]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with point
  simp only [Finset.mul_sum,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowGreenSourceForm
