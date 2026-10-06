import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Integrability
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Matrix
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open MeasureTheory
open scoped BigOperators
noncomputable section

def ao (b : Basis) (x : Point) : ℝ := orbital (sourceTerms b) zeroJet x
def derivative (b : Basis) (a : Fin 3) (x : Point) : ℝ := orbital (sourceTerms b) (raise zeroJet a) x

theorem source_product_integrable (b c : Basis) (left right : MultiIndex) :
    Integrable (fun x => orbital (sourceTerms b) left x * orbital (sourceTerms c) right x) :=
  (source_orbital_integrable c right).bdd_mul
    (orbital_contDiff (sourceTerms b) left 0).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => source_orbital_uniform_bound left b x))

def overlap (b c : Basis) : ℝ := ∫ x : Point, ao b x * ao c x

def firstDerivative (a : Fin 3) (b c : Basis) : ℝ := ∫ x : Point, ao b x * derivative c a x

def kinetic (b c : Basis) : ℝ := (1/2 : ℝ) * ∑ a : Fin 3,
  ∫ x : Point, derivative b a x * derivative c a x

theorem overlap_symmetric (b c : Basis) : overlap b c = overlap c b := by
  unfold overlap
  congr 1
  funext x
  exact mul_comm _ _

theorem kinetic_symmetric (b c : Basis) : kinetic b c = kinetic c b := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  funext x
  exact mul_comm _ _

def expansion (coefficients : Basis → ℝ) (x : Point) : ℝ := ∑ b : Basis, coefficients b * ao b x

theorem expansion_product_integrable (left right : Basis → ℝ) :
    Integrable (fun x => expansion left x * expansion right x) := by
  have each (b c : Basis) : Integrable (fun x => (left b * right c) * (ao b x * ao c x)) :=
    (source_product_integrable b c zeroJet zeroJet).const_mul _
  convert! integrable_finsetSum Finset.univ (fun b _ =>
    integrable_finsetSum Finset.univ (fun c _ => each b c)) using 1
  funext x
  simp only [expansion,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem original_overlap_quadratic (v : Basis → ℝ) :
    ∑ b : Basis, ∑ c : Basis, v b * v c * overlap b c = ∫ x : Point, (expansion v x)^2 := by
  have each (b c : Basis) : Integrable (fun x => (v b * v c) * (ao b x * ao c x)) :=
    (source_product_integrable b c zeroJet zeroJet).const_mul _
  simp_rw [overlap, ← integral_const_mul]
  have inner (b : Basis) : (∑ c : Basis, ∫ x : Point, (v b*v c)*(ao b x*ao c x)) =
      ∫ x : Point, ∑ c : Basis, (v b*v c)*(ao b x*ao c x) :=
    (integral_finsetSum Finset.univ (fun c _ => each b c)).symm
  simp_rw [inner]
  rw [← integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => each b c))]
  congr 1
  funext x
  simp only [pow_two,expansion,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem original_overlap_nonnegative (v : Basis → ℝ) :
    0 ≤ ∑ b : Basis, ∑ c : Basis, v b * v c * overlap b c := by
  rw [original_overlap_quadratic]
  exact integral_nonneg (fun x => sq_nonneg (expansion v x))

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
