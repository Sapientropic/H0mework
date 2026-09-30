import H0mework.Versions.X.NavierStokes.WindowPhysics.HeatMultiplier
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowSpacetimeFourier

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open NativeFullOrderAction NativeFullOrderSynthesis

noncomputable section

abbrev Spacetime := ℝ × PhysicalSpace

theorem multiplier_decay (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (wave : IntegerWavevector) :
    frequencySize wave ^ order * finiteStateVorticityHeatMultiplier nu.coeff lag wave ≤
      NativeHeatSpatialMultiplier.budget nu lag (order + 4) * decay wave := by
  have positiveFrequency := frequencySize_pos wave
  calc
    _ = (frequencySize wave ^ (order + 4) * finiteStateVorticityHeatMultiplier nu.coeff lag wave) * decay wave := by
      unfold decay
      rw [pow_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (NativeHeatSpatialMultiplier.multiplier_bound nu lag positive (order + 4) wave) (sq_nonneg _)

theorem heated_coefficient_bound (nu : Viscosity) (lag : ℝ≥0) (positive : 0 < lag)
    (loss order : ℕ) (wave : IntegerWavevector) (z : ℂ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ‖z‖ ≤ frequencySize wave ^ loss * bound) :
    frequencySize wave ^ order * ‖finiteStateVorticityHeatMultiplier nu.coeff lag wave • z‖ ≤
      (NativeHeatSpatialMultiplier.budget nu lag (order + loss + 4) * bound) * decay wave := by
  rw [norm_smul, Real.norm_of_nonneg (finiteStateVorticityHeatMultiplier_nonneg _ _ _)]
  calc
    _ ≤ frequencySize wave ^ order *
        (finiteStateVorticityHeatMultiplier nu.coeff lag wave * (frequencySize wave ^ loss * bound)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left bounded (finiteStateVorticityHeatMultiplier_nonneg _ _ _))
        (pow_nonneg (frequencySize_nonneg wave) _)
    _ = (frequencySize wave ^ (order + loss) * finiteStateVorticityHeatMultiplier nu.coeff lag wave) * bound := by
      rw [pow_add]
      ring
    _ ≤ _ := by
      simpa only [mul_right_comm] using
        mul_le_mul_of_nonneg_right (multiplier_decay nu lag positive (order + loss) wave) nonnegative

variable (coefficient : ℕ → IntegerWavevector → ℝ → ℂ)
    (evolves : ∀ n wave time, HasDerivAt (coefficient n wave) (coefficient (n + 1) wave time) time)

include evolves in
theorem coefficient_iterated (order : ℕ) (wave : IntegerWavevector) :
    iteratedDeriv order (coefficient 0 wave) = coefficient order wave := by
  induction order with
  | zero => rw [iteratedDeriv_zero]
  | succ order previous =>
      rw [iteratedDeriv_succ, previous]
      funext time
      exact (evolves order wave time).deriv

include evolves in
theorem coefficient_smooth (wave : IntegerWavevector) : ContDiff ℝ ∞ (coefficient 0 wave) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro order _
  rw [coefficient_iterated coefficient evolves]
  exact fun time => (evolves order wave time).differentiableAt

def timeCoefficient (wave : IntegerWavevector) (pair : Spacetime) : ℂ := coefficient 0 wave pair.1

include evolves in
theorem timeCoefficient_smooth (wave : IntegerWavevector) : ContDiff ℝ ∞ (timeCoefficient coefficient wave) :=
  (coefficient_smooth coefficient evolves wave).comp contDiff_fst

include evolves in
theorem timeCoefficient_bound (wave : IntegerWavevector) (order : ℕ) (pair : Spacetime) :
    ‖iteratedFDeriv ℝ order (timeCoefficient coefficient wave) pair‖ ≤ ‖coefficient order wave pair.1‖ := by
  let projection : Spacetime →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ PhysicalSpace
  change ‖iteratedFDeriv ℝ order (coefficient 0 wave ∘ projection) pair‖ ≤ _
  rw [projection.iteratedFDeriv_comp_right (coefficient_smooth coefficient evolves wave) pair
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [projection, ContinuousLinearMap.norm_fst, Finset.prod_const_one, mul_one]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, coefficient_iterated coefficient evolves]
  exact le_rfl

def spaceMonomial (wave : IntegerWavevector) (pair : Spacetime) : ℂ := monomial wave pair.2

theorem spaceMonomial_smooth (wave : IntegerWavevector) : ContDiff ℝ ∞ (spaceMonomial wave) :=
  (monomial_smooth wave).comp contDiff_snd

theorem spaceMonomial_bound (wave : IntegerWavevector) (order : ℕ) (pair : Spacetime) :
    ‖iteratedFDeriv ℝ order (spaceMonomial wave) pair‖ ≤ (2 * Real.pi * frequencySize wave) ^ order := by
  let projection : Spacetime →L[ℝ] PhysicalSpace := ContinuousLinearMap.snd ℝ ℝ PhysicalSpace
  change ‖iteratedFDeriv ℝ order (monomial wave ∘ projection) pair‖ ≤ _
  rw [projection.iteratedFDeriv_comp_right (monomial_smooth wave) pair
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [projection, ContinuousLinearMap.norm_snd, Finset.prod_const_one, mul_one]
  exact monomial_iterated_bound wave order pair.2

def scalarMode (wave : IntegerWavevector) (pair : Spacetime) : ℂ :=
  timeCoefficient coefficient wave pair * spaceMonomial wave pair

def modeBudget (bound : ℕ → ℕ → ℝ) (order : ℕ) : ℝ :=
  ∑ rank ∈ Finset.range (order + 1), (order.choose rank : ℝ) * (2 * Real.pi) ^ (order - rank) * bound rank (order - rank)

include evolves in
theorem scalarMode_smooth (wave : IntegerWavevector) : ContDiff ℝ ∞ (scalarMode coefficient wave) :=
  (timeCoefficient_smooth coefficient evolves wave).mul (spaceMonomial_smooth wave)

include evolves in
theorem scalarMode_bound (bound : ℕ → ℕ → ℝ)
    (bounded : ∀ rank order wave time, frequencySize wave ^ order * ‖coefficient rank wave time‖ ≤ bound rank order * decay wave)
    (order : ℕ) (wave : IntegerWavevector) (pair : Spacetime) :
    ‖iteratedFDeriv ℝ order (scalarMode coefficient wave) pair‖ ≤ modeBudget bound order * decay wave := by
  apply (norm_iteratedFDeriv_mul_le (timeCoefficient_smooth coefficient evolves wave)
    (spaceMonomial_smooth wave) pair (n := order)
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).trans
  rw [modeBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro rank _
  have timeBound := timeCoefficient_bound coefficient evolves wave rank pair
  have spaceBound := spaceMonomial_bound wave (order - rank) pair
  calc
    _ ≤ (order.choose rank : ℝ) * (2 * Real.pi) ^ (order - rank) *
        (frequencySize wave ^ (order - rank) * ‖coefficient rank wave pair.1‖) := by
      have scaled := mul_le_mul_of_nonneg_left
        (mul_le_mul timeBound spaceBound (norm_nonneg _) (norm_nonneg _)) (Nat.cast_nonneg (order.choose rank))
      convert! scaled using 1
      · ring
      · rw [mul_pow]
        ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bounded rank (order - rank) wave pair.1)
        (mul_nonneg (Nat.cast_nonneg (order.choose rank)) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _))

def scalarField (pair : Spacetime) : ℂ := ∑' wave, scalarMode coefficient wave pair

include evolves in
theorem scalarField_smooth (bound : ℕ → ℕ → ℝ)
    (bounded : ∀ rank order wave time, frequencySize wave ^ order * ‖coefficient rank wave time‖ ≤ bound rank order * decay wave) :
    ContDiff ℝ ∞ (scalarField coefficient) := by
  exact contDiff_tsum (N := (⊤ : ℕ∞)) (scalarMode_smooth coefficient evolves)
    (fun order _ => decay_summable.mul_left (modeBudget bound order))
    (fun order wave point _ => scalarMode_bound coefficient evolves bound bounded order wave point)

theorem compact_all_order_Lp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : Spacetime → E) (smooth : ContDiff ℝ ∞ field) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  have continuous := smooth.continuous_iteratedFDeriv (m := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  obtain ⟨ceiling, ceilingBound⟩ := (compact.image continuous.norm).bddAbove
  let bound := max ceiling 0
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have bounded : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order field point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact (ceilingBound ⟨point, inside, rfl⟩).trans (le_max_left _ _)
  exact ⟨bound, le_max_right _ _, MemLp.of_bound continuous.aestronglyMeasurable.restrict bound bounded,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bounded⟩

end
end SaturationMonoid.NavierStokes.NativeWindowSpacetimeFourier
