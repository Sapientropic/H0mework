import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.AttractionIntegral

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis
open MeasureTheory
noncomputable section

theorem one_side_expansion (left right : Term) (l r : MultiIndex) (cl cr v : Point) :
    (fun x => jetRate left l cl v x * centredValue right r cr x * SourceCoulomb.kernel x) =
      fun x => -(∑ k : Fin 3, v k * attractionIntegrand left right (raise l k) r cl cr x) := by
  funext x
  simp only [jetRate,attractionIntegrand,neg_mul,Finset.sum_mul,mul_assoc]

theorem one_side_integrable (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (cl cr v : Point) :
    Integrable (fun x => jetRate left l cl v x * centredValue right r cr x * SourceCoulomb.kernel x) := by
  rw [one_side_expansion]
  exact (integrable_finsetSum _ (fun k _ =>
    (attraction_integrand_integrable left right hl hr (raise l k) r cl cr).const_mul (v k))).neg

theorem one_side_integral (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (cl cr v : Point) :
    (∫ x : Point, jetRate left l cl v x * centredValue right r cr x * SourceCoulomb.kernel x) =
      -(∑ k : Fin 3, v k * primitiveAttraction left right (raise l k) r cl cr) := by
  rw [one_side_expansion,integral_neg,integral_finsetSum _ (fun k _ =>
    (attraction_integrand_integrable left right hl hr (raise l k) r cl cr).const_mul (v k))]
  simp only [integral_const_mul,primitiveAttraction]

def primitiveAttractionRate (left right : Term) (l r : MultiIndex) (cl cr vl vr : Point) : ℝ :=
  -(∑ k : Fin 3, vl k * primitiveAttraction left right (raise l k) r cl cr) +
  -(∑ k : Fin 3, vr k * primitiveAttraction right left (raise r k) l cr cl)

theorem integrated_attraction_rate (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
    (l r : MultiIndex) (cl cr vl vr : Point) :
    (∫ x : Point, attractionRate left right l r cl cr vl vr x) =
      primitiveAttractionRate left right l r cl cr vl vr := by
  have split : attractionRate left right l r cl cr vl vr = fun x =>
      jetRate left l cl vl x * centredValue right r cr x * SourceCoulomb.kernel x +
      jetRate right r cr vr x * centredValue left l cl x * SourceCoulomb.kernel x := by
    funext x
    unfold attractionRate
    ring
  rw [split,integral_add (one_side_integrable left right hl hr l r cl cr vl)
    (one_side_integrable right left hr hl r l cr cl vr),
    one_side_integral left right hl hr l r cl cr vl,one_side_integral right left hr hl r l cr cl vr]
  rfl

variable (left right : Term) (hl : 0 < left.exponent) (hr : 0 < right.exponent)
  (l r : MultiIndex) (cl cr vl vr : ℝ → Point) (vlContinuous : Continuous vl) (vrContinuous : Continuous vr)
  (dl : ∀ t k, HasDerivAt (fun s => cl s k) (vl t k) t)
  (dr : ∀ t k, HasDerivAt (fun s => cr s k) (vr t k) t)

include hl hr vlContinuous vrContinuous dl dr

theorem primitive_attraction_equation (t : ℝ) :
    HasDerivAt (fun s => primitiveAttraction left right l r (cl s) (cr s))
      (primitiveAttractionRate left right l r (cl t) (cr t) (vl t) (vr t)) t := by
  have generated := (primitive_attraction_derivative left right hl hr l r cl cr vl vr vlContinuous vrContinuous dl dr t).2
  rw [integrated_attraction_rate left right hl hr] at generated
  exact generated

theorem primitive_attraction_rate_continuous :
    Continuous (fun t => primitiveAttractionRate left right l r (cl t) (cr t) (vl t) (vr t)) := by
  have leftIntegral (k : Fin 3) : Continuous (fun t => primitiveAttraction left right (raise l k) r (cl t) (cr t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (primitive_attraction_equation left right hl hr (raise l k) r cl cr vl vr vlContinuous vrContinuous dl dr t).continuousAt
  have rightIntegral (k : Fin 3) : Continuous (fun t => primitiveAttraction right left (raise r k) l (cr t) (cl t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (primitive_attraction_equation right left hr hl (raise r k) l cr cl vr vl vrContinuous vlContinuous dr dl t).continuousAt
  exact (continuous_finsetSum _ (fun k _ => ((continuous_apply k).comp vlContinuous).mul (leftIntegral k))).neg.add
    (continuous_finsetSum _ (fun k _ => ((continuous_apply k).comp vrContinuous).mul (rightIntegral k))).neg

theorem primitive_attraction_integral (a b : ℝ) :
    primitiveAttraction left right l r (cl b) (cr b) - primitiveAttraction left right l r (cl a) (cr a) =
      ∫ t in a..b, primitiveAttractionRate left right l r (cl t) (cr t) (vl t) (vr t) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_attraction_equation left right hl hr l r cl cr vl vr vlContinuous vrContinuous dl dr t)
    ((primitive_attraction_rate_continuous left right hl hr l r cl cr vl vr vlContinuous vrContinuous dl dr).intervalIntegrable _ _)).symm

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
