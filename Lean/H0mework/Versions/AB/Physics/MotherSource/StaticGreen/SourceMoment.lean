import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.TranslatedDecay
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.ConvolutionBound

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb GlobalSource SourceFiniteData ContinuousGradient
noncomputable section

theorem spatialHeat_neg (parameter : ℝ) (point : Point) : spatialHeat parameter (-point) = spatialHeat parameter point := by
  simp only [spatialHeat, distance_sq, Pi.neg_apply, neg_sq]

def momentParameter (term : Term) : ℝ := Real.sqrt ((term.exponent : ℝ)/24)

def termMomentBound (term : Term) (order : MultiIndex) : ℝ :=
  (termBound term order : ℝ)*Real.exp ((term.exponent : ℝ)/2*‖termCentre term‖^2)*
    Real.exp (1/(2*((term.exponent : ℝ)/12)))

theorem heat_moment_bound (parameter : ℝ) (positive : 0 < parameter) (point : Point) :
    ‖point‖*spatialHeat parameter point ≤
      Real.exp (1/(2*parameter^2))*spatialHeat (Real.sqrt (parameter^2/2)) point := by
  have tail := monomial_gaussian_tail (sq_pos_of_pos positive) 1 (distance point)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul,
    abs_of_nonneg (distance_nonnegative point)] at tail
  apply (mul_le_mul_of_nonneg_right (pi_norm_le_distance point) (spatialHeat_positive parameter point).le).trans
  convert tail using 1 <;> try rfl
  simp only [spatialHeat, Real.sq_sqrt (show 0 ≤ parameter^2/2 by positivity)]

theorem term_moment_tail (term : Term) (positive : 0 < term.exponent) (order : MultiIndex) (point : Point) :
    ‖point‖*‖value term order point‖ ≤ termMomentBound term order*spatialHeat (momentParameter term) point := by
  have exponent : (0 : ℝ) < (term.exponent : ℝ) := by exact_mod_cast positive
  have translated := translated_term_bound term positive order 0 0 (-point) (by simp)
  simp only [zero_sub, neg_neg, translatedTermEnvelope, zero_add, spatialHeat_neg] at translated
  have multiplied := mul_le_mul_of_nonneg_left translated (norm_nonneg point)
  have heat := heat_moment_bound (Real.sqrt ((term.exponent : ℝ)/12))
    (Real.sqrt_pos.mpr (by positivity)) point
  rw [Real.sq_sqrt (show 0 ≤ (term.exponent : ℝ)/12 by positivity)] at heat
  have parameter : (term.exponent : ℝ)/12/2 = (term.exponent : ℝ)/24 := by ring
  rw [parameter] at heat
  have scale := mul_le_mul_of_nonneg_left heat
    (show 0 ≤ (termBound term order : ℝ)*Real.exp ((term.exponent : ℝ)/2*‖termCentre term‖^2) by positivity)
  rw [Real.norm_eq_abs]
  unfold termMomentBound momentParameter
  nlinarith

theorem term_moment_bound_nonnegative (term : Term) (order : MultiIndex) : 0 ≤ termMomentBound term order := by
  unfold termMomentBound
  positivity

theorem term_moment_integrable (term : Term) (positive : 0 < term.exponent) (order : MultiIndex) :
    Integrable (fun point : Point => ‖point‖*‖value term order point‖) := by
  have heat : Integrable (spatialHeat (momentParameter term)) :=
    spatialHeat_integrable _ (Real.sqrt_pos.mpr (div_pos (by exact_mod_cast positive) (by norm_num)))
  apply (heat.const_mul (termMomentBound term order)).mono' ?_
    (Filter.Eventually.of_forall (fun point => ?_))
  · exact (continuous_norm.mul (value_contDiff term order 0).continuous.norm).aestronglyMeasurable
  · simpa only [norm_mul, norm_norm] using term_moment_tail term positive order point

theorem term_moment_uniform (term : Term) (positive : 0 < term.exponent) (order : MultiIndex) (point : Point) :
    ‖point‖*‖value term order point‖ ≤ termMomentBound term order :=
  (term_moment_tail term positive order point).trans
    (mul_le_of_le_one_right (term_moment_bound_nonnegative term order) (spatialHeat_le_one _ _))

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
