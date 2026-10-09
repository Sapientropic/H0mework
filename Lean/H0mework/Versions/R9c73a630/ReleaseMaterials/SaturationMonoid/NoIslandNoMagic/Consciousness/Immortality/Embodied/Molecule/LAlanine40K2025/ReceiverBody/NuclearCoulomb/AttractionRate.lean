import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.LocalBounds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.Integrability

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis
open MeasureTheory
noncomputable section

def jetRate (term : Term) (jet : MultiIndex) (c v x : Point) : ℝ :=
  -(∑ k : Fin 3, v k * centredValue term (raise jet k) c x)

def attractionIntegrand (left right : Term) (l r : MultiIndex) (cl cr x : Point) : ℝ :=
  centredValue left l cl x * centredValue right r cr x * SourceCoulomb.kernel x

def attractionRate (left right : Term) (l r : MultiIndex) (cl cr vl vr x : Point) : ℝ :=
  (jetRate left l cl vl x * centredValue right r cr x +
    centredValue left l cl x * jetRate right r cr vr x) * SourceCoulomb.kernel x

theorem attraction_integrand_derivative (left right : Term) (l r : MultiIndex)
    (cl cr : ℝ → Point) (vl vr : Point) (t : ℝ) (x : Point)
    (dl : ∀ k, HasDerivAt (fun s => cl s k) (vl k) t)
    (dr : ∀ k, HasDerivAt (fun s => cr s k) (vr k) t) :
    HasDerivAt (fun s => attractionIntegrand left right l r (cl s) (cr s) x)
      (attractionRate left right l r (cl t) (cr t) vl vr x) t :=
  ((centred_value_derivative left l cl vl t x dl).mul
    (centred_value_derivative right r cr vr t x dr)).mul_const (SourceCoulomb.kernel x)

theorem attraction_integrand_measurable (left right : Term) (l r : MultiIndex) (cl cr : Point) :
    AEStronglyMeasurable (attractionIntegrand left right l r cl cr) :=
  ((centred_continuous left l cl).mul (centred_continuous right r cr)).aestronglyMeasurable.mul
    SourceCoulomb.kernel_measurable.aestronglyMeasurable

theorem jet_rate_continuous (term : Term) (jet : MultiIndex) (c v : Point) :
    Continuous (jetRate term jet c v) :=
  (continuous_finsetSum _ (fun k _ => (centred_continuous term (raise jet k) c).const_mul (v k))).neg

theorem attraction_rate_measurable (left right : Term) (l r : MultiIndex) (cl cr vl vr : Point) :
    AEStronglyMeasurable (attractionRate left right l r cl cr vl vr) :=
  (((jet_rate_continuous left l cl vl).mul (centred_continuous right r cr)).add
    ((centred_continuous left l cl).mul (jet_rate_continuous right r cr vr))).aestronglyMeasurable.mul
      SourceCoulomb.kernel_measurable.aestronglyMeasurable

theorem one_side_rate_bound (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) (cl cr v x : Point) (bl : ‖cl‖ ≤ C) (br : ‖cr‖ ≤ C) (bv : ‖v‖ ≤ C) :
    ‖jetRate left l cl v x * centredValue right r cr x * SourceCoulomb.kernel x‖ ≤
      C * ∑ k : Fin 3, attractionEnvelope left right (raise l k) r C x := by
  have expression : jetRate left l cl v x * centredValue right r cr x * SourceCoulomb.kernel x =
      -(∑ k : Fin 3, v k * attractionIntegrand left right (raise l k) r cl cr x) := by
    simp only [jetRate,attractionIntegrand,neg_mul,Finset.sum_mul,mul_assoc]
  rw [expression,norm_neg]
  calc
    _ ≤ ∑ k : Fin 3, ‖v k * attractionIntegrand left right (raise l k) r cl cr x‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin 3, C * attractionEnvelope left right (raise l k) r C x := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,Real.norm_eq_abs]
      have speed : |v k| ≤ C := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm v k).trans bv
      exact mul_le_mul speed (attraction_uniform_bound left right hl hr (raise l k) r C cl cr x bl br)
        (norm_nonneg _) ((norm_nonneg v).trans bv)
    _ = _ := (Finset.mul_sum _ _ _).symm

def attractionRateEnvelope (left right : Term) (l r : MultiIndex) (C : ℝ) (x : Point) : ℝ :=
  C * ∑ k : Fin 3, (attractionEnvelope left right (raise l k) r C x +
    attractionEnvelope right left (raise r k) l C x)

theorem attraction_rate_envelope_integrable (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) : Integrable (attractionRateEnvelope left right l r C) :=
  (integrable_finsetSum _ (fun k _ =>
    (attraction_envelope_integrable left right hl hr (raise l k) r C).add
      (attraction_envelope_integrable right left hr hl (raise r k) l C))).const_mul C

theorem attraction_rate_uniform_bound (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) (cl cr vl vr x : Point)
    (bl : ‖cl‖ ≤ C) (br : ‖cr‖ ≤ C) (bvl : ‖vl‖ ≤ C) (bvr : ‖vr‖ ≤ C) :
    ‖attractionRate left right l r cl cr vl vr x‖ ≤ attractionRateEnvelope left right l r C x := by
  have split : attractionRate left right l r cl cr vl vr x =
      jetRate left l cl vl x * centredValue right r cr x * SourceCoulomb.kernel x +
      jetRate right r cr vr x * centredValue left l cl x * SourceCoulomb.kernel x := by
    unfold attractionRate
    ring
  rw [split]
  calc
    _ ≤ ‖jetRate left l cl vl x * centredValue right r cr x * SourceCoulomb.kernel x‖ +
        ‖jetRate right r cr vr x * centredValue left l cl x * SourceCoulomb.kernel x‖ := norm_add_le _ _
    _ ≤ C * (∑ k : Fin 3, attractionEnvelope left right (raise l k) r C x) +
        C * (∑ k : Fin 3, attractionEnvelope right left (raise r k) l C x) :=
      add_le_add (one_side_rate_bound left right hl hr l r C cl cr vl x bl br bvl)
        (one_side_rate_bound right left hr hl r l C cr cl vr x br bl bvr)
    _ = _ := by rw [attractionRateEnvelope,Finset.sum_add_distrib,mul_add]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
