import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.Trajectory
import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Integrability

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open MeasureTheory SpatialContinuation
noncomputable section

theorem centred_integrable (term : Term) (positive : 0<term.exponent) (jet : MultiIndex) (c : Point) :
    Integrable (fun x => centredValue term jet c x) := by
  convert! (term_integrable term positive jet).comp_sub_right (c-fun k => (term.centre k : ℝ)) using 1
  funext x
  unfold centredValue
  congr 1
  funext k
  simp only [Pi.sub_apply]
  ring

theorem centred_continuous (term : Term) (jet : MultiIndex) (c : Point) :
    Continuous (fun x => centredValue term jet c x) := by
  unfold centredValue
  exact (value_contDiff term jet 0).continuous.comp (by fun_prop)

theorem centred_bound (term : Term) (positive : 0<term.exponent) (jet : MultiIndex) (c x : Point) :
    |centredValue term jet c x|≤(termBound term jet : ℝ) :=
  term_uniform_bound term positive jet _

theorem centred_product_integrable (left right : Term) (leftPositive : 0<left.exponent)
    (rightPositive : 0<right.exponent) (leftJet rightJet : MultiIndex) (leftCentre rightCentre : Point) :
    Integrable (fun x => centredValue left leftJet leftCentre x*centredValue right rightJet rightCentre x) :=
  (centred_integrable right rightPositive rightJet rightCentre).bdd_mul
    (centred_continuous left leftJet leftCentre).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using centred_bound left leftPositive leftJet leftCentre x)

theorem exponent_positive (i : Basis) (p : Primitive i) : 0<(primitive i p).exponent :=
  source_exponents_positive i _ (List.get_mem _ _)

variable (current : Material)

theorem primitive_product_integrable (i j : Basis) (p : Primitive i) (r : Primitive j)
    (left right : MultiIndex) (phase : Phase) (t : ℝ) :
    Integrable (fun x => primitiveJet current i p left phase t x*primitiveJet current j r right phase t x) :=
  centred_product_integrable (primitive i p) (primitive j r) (exponent_positive i p) (exponent_positive j r)
    left right (centre current i p phase t) (centre current j r phase t)

theorem orbital_product_integrable (i j : Basis) (left right : MultiIndex) (phase : Phase) (t : ℝ) :
    Integrable (fun x => orbitalJet current i left phase t x*orbitalJet current j right phase t x) := by
  have total := integrable_finsetSum Finset.univ (fun p _ =>
    integrable_finsetSum Finset.univ (fun r _ => primitive_product_integrable current i j p r left right phase t))
  convert! total using 1
  funext x
  simp only [orbitalJet,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem primitive_rate_product_integrable (i j : Basis) (p : Primitive i) (r : Primitive j)
    (left right : MultiIndex) (phase : Phase) (t : ℝ) :
    Integrable (fun x => primitiveRate current i p left phase t x*primitiveJet current j r right phase t x) := by
  have total := (integrable_finsetSum Finset.univ (fun k _ =>
    (primitive_product_integrable current i j p r (raise left k) right phase t).const_mul
      (velocity current phase t (owner i p,k)))).neg
  simpa only [primitiveRate,neg_mul,Finset.sum_mul,mul_assoc,Pi.neg_apply] using! total

theorem orbital_rate_product_integrable (i j : Basis) (left right : MultiIndex) (phase : Phase) (t : ℝ) :
    Integrable (fun x => orbitalRate current i left phase t x*orbitalJet current j right phase t x) := by
  have total := integrable_finsetSum Finset.univ (fun p _ =>
    integrable_finsetSum Finset.univ (fun r _ => primitive_rate_product_integrable current i j p r left right phase t))
  convert! total using 1
  funext x
  simp only [orbitalRate,orbitalJet,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
