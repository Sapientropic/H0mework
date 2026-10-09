import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.RealFields
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl
open BasinRefinement SourceGaussianModel GlobalSource MeasureTheory
noncomputable section

def firstRemainder (terms : List Term) (jet : MultiIndex) (d x : Point) : ℝ :=
  orbital terms jet (x-d)-orbital terms jet x-directional terms jet d x

def rateRemainder (terms : List Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) : ℝ :=
  directional terms jet d (linePoint d t x)-directional terms jet d x

def curvatureEnergy (terms : List Term) (jet : MultiIndex) : ℝ :=
  ∑ k : Fin 3, gradientEnergy terms (raise jet k)

theorem gradient_energy_nonnegative (terms : List Term) (jet : MultiIndex) :
    0 ≤ gradientEnergy terms jet :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

theorem curvature_energy_nonnegative (terms : List Term) (jet : MultiIndex) :
    0 ≤ curvatureEnergy terms jet :=
  Finset.sum_nonneg (fun _ _ => gradient_energy_nonnegative _ _)

theorem first_remainder_integral (terms : List Term) (jet : MultiIndex) (d x : Point) :
    firstRemainder terms jet d x=∫ t in (0 : ℝ)..1, rateRemainder terms jet d t x := by
  unfold firstRemainder rateRemainder
  rw [orbital_line_integral]
  have regular : Continuous (fun t => directional terms jet d (linePoint d t x)) :=
    line_rate_continuous terms jet d x
  rw [intervalIntegral.integral_sub (regular.intervalIntegrable _ _) intervalIntegrable_const]
  simp only [← line_rate_directional,intervalIntegral.integral_const,sub_zero,one_smul]

theorem first_remainder_square_le (terms : List Term) (jet : MultiIndex) (d x : Point) :
    (firstRemainder terms jet d x)^2 ≤ ∫ t in (0 : ℝ)..1, (rateRemainder terms jet d t x)^2 := by
  rw [first_remainder_integral]
  apply integral_square_le
  exact (line_rate_continuous terms jet d x).sub continuous_const

theorem rate_remainder_square_le (terms : List Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) :
    (rateRemainder terms jet d t x)^2 ≤
      (∑ k : Fin 3, (d k)^2)*∑ k : Fin 3,
        (orbital terms (raise jet k) (linePoint d t x)-orbital terms (raise jet k) x)^2 := by
  have equation : rateRemainder terms jet d t x=
      -(∑ k : Fin 3, d k*(orbital terms (raise jet k) (linePoint d t x)-orbital terms (raise jet k) x)) := by
    simp only [rateRemainder,directional,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [equation,neg_sq]
  exact three_axis_schwarz d (fun k => orbital terms (raise jet k) (linePoint d t x)-orbital terms (raise jet k) x)

theorem rate_remainder_square_integrable_prod (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (d : Point) :
    Integrable (fun z : ℝ × Point => (rateRemainder terms jet d z.1 z.2)^2) (unitInterval.prod volume) := by
  have shifted := translated_square_integrable (directional terms jet d) (directional_continuous terms jet d)
    (directional_square_integrable terms positive jet d) d
  have base := (directional_square_integrable terms positive jet d).comp_snd unitInterval
  apply ((shifted.const_mul 2).add (base.const_mul 2)).mono'
  · exact ((directional_continuous terms jet d).comp (by unfold linePoint; fun_prop) |>.sub
      ((directional_continuous terms jet d).comp continuous_snd)).pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      simp only [rateRemainder,Real.norm_eq_abs,abs_pow,sq_abs,Pi.add_apply]
      nlinarith [sq_nonneg (directional terms jet d (linePoint d z.1 z.2)+directional terms jet d z.2)]

theorem rate_remainder_integral_bound (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (d : Point) (t : ℝ) :
    (∫ x : Point, (rateRemainder terms jet d t x)^2) ≤
      (∑ k : Fin 3, (d k)^2)*(∑ k : Fin 3, (t*d k)^2)*curvatureEnergy terms jet := by
  have each (k : Fin 3) : Integrable (fun x : Point =>
      (orbital terms (raise jet k) (linePoint d t x)-orbital terms (raise jet k) x)^2) :=
    translation_square_integrable terms positive (raise jet k) (fun k => t*d k)
  have upper := (integrable_finsetSum Finset.univ (fun k _ => each k)).const_mul (∑ k : Fin 3, (d k)^2)
  have lower : Integrable (fun x : Point => (rateRemainder terms jet d t x)^2) := by
    apply upper.mono'
    · exact ((directional_continuous terms jet d).comp (by unfold linePoint; fun_prop) |>.sub
        (directional_continuous terms jet d)).pow 2 |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using rate_remainder_square_le terms jet d t x
  calc
    _ ≤ ∫ x : Point, (∑ k : Fin 3, (d k)^2)*∑ k : Fin 3,
        (orbital terms (raise jet k) (linePoint d t x)-orbital terms (raise jet k) x)^2 :=
      integral_mono lower upper (rate_remainder_square_le terms jet d t)
    _ = (∑ k : Fin 3, (d k)^2)*∑ k : Fin 3, ∫ x : Point,
        (orbital terms (raise jet k) (linePoint d t x)-orbital terms (raise jet k) x)^2 := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => each k)]
    _ ≤ (∑ k : Fin 3, (d k)^2)*∑ k : Fin 3,
        (∑ k : Fin 3, (t*d k)^2)*gradientEnergy terms (raise jet k) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum (fun k _ => translation_square_bound terms positive (raise jet k) (fun k => t*d k))
      · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; simp only [curvatureEnergy,mul_assoc]

/-- Raised original Gaussian jets pay the complete quadratic translation remainder. -/
theorem translation_remainder_square_bound (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (jet : MultiIndex) (d : Point) :
    (∫ x : Point, (firstRemainder terms jet d x)^2) ≤
      (∑ k : Fin 3, (d k)^2)^2*curvatureEnergy terms jet := by
  have joint := rate_remainder_square_integrable_prod terms positive jet d
  have timeSquare : Integrable (fun x : Point => ∫ t in (0 : ℝ)..1, (rateRemainder terms jet d t x)^2) := by
    simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),unitInterval] using joint.integral_prod_right
  have remainder : Integrable (fun x : Point => (firstRemainder terms jet d x)^2) := by
    apply timeSquare.mono'
    · exact ((((orbital_contDiff terms jet 0).continuous.comp (continuous_id.sub continuous_const)).sub
        (orbital_contDiff terms jet 0).continuous).sub (directional_continuous terms jet d)).pow 2 |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using first_remainder_square_le terms jet d x
  have flip := integral_integral_swap (μ := unitInterval) (ν := (volume : Measure Point))
    (f := fun t x => (rateRemainder terms jet d t x)^2) joint
  have unitBound (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      (∫ x : Point, (rateRemainder terms jet d t x)^2) ≤
        (∑ k : Fin 3, (d k)^2)^2*curvatureEnergy terms jet := by
    have tSquare : t^2 ≤ 1 := by nlinarith [mul_nonneg (le_of_lt ht.1) (sub_nonneg.mpr ht.2)]
    have scale : (∑ k : Fin 3, (t*d k)^2) ≤ ∑ k : Fin 3, (d k)^2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right tSquare (sq_nonneg (d k))
    have price := rate_remainder_integral_bound terms positive jet d t
    calc
      _ ≤ _ := price
      _ ≤ (∑ k : Fin 3, (d k)^2)*(∑ k : Fin 3, (d k)^2)*curvatureEnergy terms jet := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left scale (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        · exact curvature_energy_nonnegative terms jet
      _ = _ := by rw [pow_two]
  calc
    _ ≤ ∫ x : Point, ∫ t in (0 : ℝ)..1, (rateRemainder terms jet d t x)^2 :=
      integral_mono remainder timeSquare (first_remainder_square_le terms jet d)
    _ = ∫ t : ℝ, ∫ x : Point, (rateRemainder terms jet d t x)^2 ∂volume ∂unitInterval := by
      simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact flip.symm
    _ ≤ ∫ _t : ℝ, (∑ k : Fin 3, (d k)^2)^2*curvatureEnergy terms jet ∂unitInterval := by
      apply integral_mono_ae joint.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact unitBound t ht
    _ = _ := by simp [unitInterval,measureReal_def]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl
