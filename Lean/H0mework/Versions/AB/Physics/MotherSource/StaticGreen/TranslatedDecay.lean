import H0mework.Physics.MotherSource.StaticGreen.HeatBounds
import H0mework.Chemistry.LAlanineBandGlobalSource.Decay.Term
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Source

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb GlobalSource SourceFiniteData ContinuousGradient
noncomputable section

theorem coordinate_square_bound (point : Point) : (∑ i : Fin 3, point i^2) ≤ 3*‖point‖^2 := by
  have bound (i : Fin 3) : point i^2 ≤ ‖point‖^2 := by
    have coordinate := norm_le_pi_norm point i
    simpa only [Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (norm_nonneg (point i)) coordinate 2)
  calc
    _ ≤ ∑ _i : Fin 3, ‖point‖^2 := Finset.sum_le_sum (fun i _ => bound i)
    _ = _ := by simp

def translatedTermEnvelope (term : Term) (order : MultiIndex) (radius : ℝ) (point : Point) : ℝ :=
  (termBound term order : ℝ)*Real.exp ((term.exponent : ℝ)/2*(radius+‖termCentre term‖)^2)*
    spatialHeat (Real.sqrt ((term.exponent : ℝ)/12)) point

theorem translated_term_bound (term : Term) (positive : 0 < term.exponent)
    (order : MultiIndex) (radius : ℝ) (position point : Point) (inside : ‖position‖ ≤ radius) :
    |value term order (position-point)| ≤ translatedTermEnvelope term order radius point := by
  have alphaPositive : (0 : ℝ) < (term.exponent : ℝ) := by exact_mod_cast positive
  have radiusNonnegative : 0 ≤ radius := (norm_nonneg position).trans inside
  have bound : ‖point‖ ≤ ‖position-point-termCentre term‖ + (radius+‖termCentre term‖) := by
    have triangle := norm_sub_le (position-termCentre term) (position-point-termCentre term)
    have equality : (position-termCentre term)-(position-point-termCentre term) = point := by abel
    rw [equality] at triangle
    have centre := norm_sub_le position (termCentre term)
    linarith
  have squared := pow_le_pow_left₀ (norm_nonneg point) bound 2
  have sumBound : (∑ i : Fin 3, point i^2) ≤
      6*‖position-point-termCentre term‖^2 + 6*(radius+‖termCentre term‖)^2 := by
    have coordinate := coordinate_square_bound point
    nlinarith [sq_nonneg (‖position-point-termCentre term‖-(radius+‖termCentre term‖))]
  have scaled := mul_le_mul_of_nonneg_left sumBound (show 0 ≤ (term.exponent : ℝ)/12 by positivity)
  have exponent : -((term.exponent : ℝ)/2)*‖position-point-termCentre term‖^2 ≤
      (term.exponent : ℝ)/2*(radius+‖termCentre term‖)^2 - (term.exponent : ℝ)/12*(∑ i : Fin 3, point i^2) := by
    nlinarith
  calc
    _ ≤ (termBound term order : ℝ)*Real.exp (-((term.exponent : ℝ)/2)*‖position-point-termCentre term‖^2) :=
      term_gaussian_tail term positive order (position-point)
    _ ≤ (termBound term order : ℝ)*Real.exp
        ((term.exponent : ℝ)/2*(radius+‖termCentre term‖)^2 - (term.exponent : ℝ)/12*(∑ i : Fin 3, point i^2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent) (termBound term order).coe_nonneg
    _ = translatedTermEnvelope term order radius point := by
      unfold translatedTermEnvelope spatialHeat
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ (term.exponent : ℝ)/12 by positivity), distance_sq]
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem translated_envelope_integrable (term : Term) (positive : 0 < term.exponent)
    (order : MultiIndex) (radius : ℝ) : Integrable (translatedTermEnvelope term order radius) := by
  have parameter : 0 < Real.sqrt ((term.exponent : ℝ)/12) :=
    Real.sqrt_pos.mpr (div_pos (by exact_mod_cast positive) (by norm_num))
  exact (spatialHeat_integrable _ parameter).const_mul _

theorem translated_envelope_bound (term : Term) (order : MultiIndex) (radius : ℝ) (point : Point) :
    ‖translatedTermEnvelope term order radius point‖ ≤
      (termBound term order : ℝ)*Real.exp ((term.exponent : ℝ)/2*(radius+‖termCentre term‖)^2) := by
  unfold translatedTermEnvelope
  have nonnegative : 0 ≤ (termBound term order : ℝ)*Real.exp ((term.exponent : ℝ)/2*(radius+‖termCentre term‖)^2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg nonnegative (spatialHeat_positive _ point).le)]
  exact mul_le_of_le_one_right nonnegative (spatialHeat_le_one _ point)

theorem translated_envelope_kernel_integrable (term : Term) (positive : 0 < term.exponent)
    (order : MultiIndex) (radius : ℝ) :
    Integrable (fun point => translatedTermEnvelope term order radius point*kernel point) :=
  integrable_mul_kernel _ (translated_envelope_integrable term positive order radius) _
    (translated_envelope_bound term order radius)

def translatedOrbitalEnvelope (terms : List Term) (order : MultiIndex) (radius : ℝ) (point : Point) : ℝ :=
  (terms.map (fun term => translatedTermEnvelope term order radius point)).sum

theorem translated_envelope_nonnegative (term : Term) (order : MultiIndex) (radius : ℝ) (point : Point) :
    0 ≤ translatedTermEnvelope term order radius point := by
  unfold translatedTermEnvelope
  exact mul_nonneg (mul_nonneg (termBound term order).coe_nonneg (Real.exp_pos _).le)
    (spatialHeat_positive _ point).le

theorem translated_orbital_nonnegative (terms : List Term) (order : MultiIndex) (radius : ℝ) (point : Point) :
    0 ≤ translatedOrbitalEnvelope terms order radius point := by
  unfold translatedOrbitalEnvelope
  exact List.sum_nonneg (by simpa using fun term (_member : term ∈ terms) => translated_envelope_nonnegative term order radius point)

theorem translated_orbital_bound (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (order : MultiIndex) (radius : ℝ) (position point : Point) (inside : ‖position‖ ≤ radius) :
    |orbital terms order (position-point)| ≤ translatedOrbitalEnvelope terms order radius point := by
  induction terms with
  | nil => simp [orbital, translatedOrbitalEnvelope]
  | cons term rest induction =>
    simp only [orbital, translatedOrbitalEnvelope, List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add
      (translated_term_bound term (positive term (by simp)) order radius position point inside)
      (induction (fun other member => positive other (by simp [member]))))

theorem translated_orbital_kernel_integrable (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (order : MultiIndex) (radius : ℝ) :
    Integrable (fun point => translatedOrbitalEnvelope terms order radius point*kernel point) := by
  induction terms with
  | nil => simp [translatedOrbitalEnvelope]
  | cons term rest induction =>
    have result := (translated_envelope_kernel_integrable term (positive term (by simp)) order radius).add
      (induction (fun other member => positive other (by simp [member])))
    convert result using 1 <;> try rfl
    funext point
    simp only [translatedOrbitalEnvelope, List.map_cons, List.sum_cons, Pi.add_apply, add_mul]

def translatedSourceEnvelope (left right : MultiIndex) (radius : ℝ) (point : Point) : ℝ :=
  ∑ first : Basis, ∑ second : Basis,
    |(densityMatrix first second : ℝ)| *(sourceOrbitalBound left first : ℝ)*
      translatedOrbitalEnvelope (sourceTerms second) right radius point

theorem translated_source_bound (left right : MultiIndex) (radius : ℝ)
    (position point : Point) (inside : ‖position‖ ≤ radius) :
    |bilinear sourceTerms densityMatrix left right (position-point)| ≤
      translatedSourceEnvelope left right radius point := by
  unfold bilinear translatedSourceEnvelope
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro first _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro second _
  rw [abs_mul, abs_mul]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (source_orbital_uniform_bound left first (position-point)) (abs_nonneg _))
    (translated_orbital_bound (sourceTerms second) (source_exponents_positive second) right radius position point inside)
    (abs_nonneg _) (by positivity)

theorem translated_source_kernel_integrable (left right : MultiIndex) (radius : ℝ) :
    Integrable (fun point => translatedSourceEnvelope left right radius point*kernel point) := by
  unfold translatedSourceEnvelope
  simp_rw [Finset.sum_mul, mul_assoc]
  apply integrable_finsetSum
  intro first _
  apply integrable_finsetSum
  intro second _
  exact ((translated_orbital_kernel_integrable (sourceTerms second) (source_exponents_positive second) right radius).const_mul _).const_mul _

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
