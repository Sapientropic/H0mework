import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.Envelope
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Pair

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis
open MeasureTheory
noncomputable section

theorem envelope_continuous (term : Term) (jet : MultiIndex) (C : ℝ) :
    Continuous (envelope term jet C) := by
  unfold envelope
  fun_prop

def pairEnvelope (left right : Term) (l r : MultiIndex) (C : ℝ) (x : Point) : ℝ :=
  envelope left l C x * envelope right r C x

theorem pair_envelope_nonnegative (left right : Term) (l r : MultiIndex) (C : ℝ) (x : Point) :
    0 ≤ pairEnvelope left right l r C x :=
  mul_nonneg (envelope_nonnegative left l C x) (envelope_nonnegative right r C x)

theorem pair_envelope_bounded (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) (x : Point) :
    ‖pairEnvelope left right l r C x‖ ≤ envelopeScale left l C * envelopeScale right r C := by
  rw [Real.norm_eq_abs,abs_of_nonneg (pair_envelope_nonnegative left right l r C x)]
  exact mul_le_mul (envelope_bounded left hl l C x) (envelope_bounded right hr r C x)
    (envelope_nonnegative right r C x) (by unfold envelopeScale; positivity)

theorem pair_envelope_integrable (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) : Integrable (pairEnvelope left right l r C) := by
  apply (envelope_integrable right hr r C).bdd_mul (envelope_continuous left l C).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (envelope_nonnegative left l C x)] using envelope_bounded left hl l C x

theorem pair_uniform_bound (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) (cl cr x : Point) (bl : ‖cl‖ ≤ C) (br : ‖cr‖ ≤ C) :
    |centredValue left l cl x * centredValue right r cr x| ≤ pairEnvelope left right l r C x := by
  rw [abs_mul]
  exact mul_le_mul (centred_uniform_tail left hl l C cl x bl) (centred_uniform_tail right hr r C cr x br)
    (abs_nonneg _) (envelope_nonnegative left l C x)

def attractionEnvelope (left right : Term) (l r : MultiIndex) (C : ℝ) (x : Point) : ℝ :=
  pairEnvelope left right l r C x * SourceCoulomb.kernel x

theorem attraction_envelope_integrable (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) : Integrable (attractionEnvelope left right l r C) :=
  SourceCoulomb.integrable_mul_kernel _ (pair_envelope_integrable left right hl hr l r C)
    (envelopeScale left l C * envelopeScale right r C) (pair_envelope_bounded left right hl hr l r C)

theorem attraction_uniform_bound (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (C : ℝ) (cl cr x : Point) (bl : ‖cl‖ ≤ C) (br : ‖cr‖ ≤ C) :
    ‖centredValue left l cl x * centredValue right r cr x * SourceCoulomb.kernel x‖ ≤
      attractionEnvelope left right l r C x := by
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (SourceCoulomb.kernel_nonnegative x)]
  exact mul_le_mul_of_nonneg_right (pair_uniform_bound left right hl hr l r C cl cr x bl br)
    (SourceCoulomb.kernel_nonnegative x)

def coulombEnvelope (a b c d : Term) (ja jb jc jd : MultiIndex) (C : ℝ) (z : Point × Point) : ℝ :=
  pairEnvelope a b ja jb C z.1 * pairEnvelope c d jc jd C z.2 * SourceCoulomb.kernel (z.2-z.1)

theorem coulomb_envelope_integrable (a b c d : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) (hc : 0 < c.exponent) (hd : 0 < d.exponent)
    (ja jb jc jd : MultiIndex) (C : ℝ) : Integrable (coulombEnvelope a b c d ja jb jc jd C) :=
  SourceCoulomb.pair_integrable _ _ (pair_envelope_integrable a b ha hb ja jb C)
    (pair_envelope_integrable c d hc hd jc jd C)
    (envelopeScale c jc C * envelopeScale d jd C) (pair_envelope_bounded c d hc hd jc jd C)

theorem coulomb_uniform_bound (a b c d : Term)
    (ha : 0 < a.exponent) (hb : 0 < b.exponent) (hc : 0 < c.exponent) (hd : 0 < d.exponent)
    (ja jb jc jd : MultiIndex) (C : ℝ) (ca cb cc cd : Point)
    (ba : ‖ca‖ ≤ C) (bb : ‖cb‖ ≤ C) (bc : ‖cc‖ ≤ C) (bd : ‖cd‖ ≤ C) (z : Point × Point) :
    ‖(centredValue a ja ca z.1 * centredValue b jb cb z.1) *
      (centredValue c jc cc z.2 * centredValue d jd cd z.2) * SourceCoulomb.kernel (z.2-z.1)‖ ≤
      coulombEnvelope a b c d ja jb jc jd C z := by
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (SourceCoulomb.kernel_nonnegative (z.2-z.1))]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (pair_uniform_bound a b ha hb ja jb C ca cb z.1 ba bb)
      (pair_uniform_bound c d hc hd jc jd C cc cd z.2 bc bd)
      (abs_nonneg _) (pair_envelope_nonnegative a b ja jb C z.1))
    (SourceCoulomb.kernel_nonnegative (z.2-z.1))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
