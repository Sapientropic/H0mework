import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.TranslationCalculus

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel GlobalSource
open MeasureTheory
noncomputable section

def directional (terms : List Term) (jet : MultiIndex) (d x : Point) : ℝ :=
  -(∑ k : Fin 3, d k * orbital terms (raise jet k) x)

def gradientEnergy (terms : List Term) (jet : MultiIndex) : ℝ :=
  ∑ k : Fin 3, ∫ x : Point, (orbital terms (raise jet k) x)^2

theorem line_rate_directional (terms : List Term) (jet : MultiIndex) (d : Point) (t : ℝ) (x : Point) :
    lineRate terms jet d t x = directional terms jet d (linePoint d t x) := rfl

theorem directional_continuous (terms : List Term) (jet : MultiIndex) (d : Point) :
    Continuous (directional terms jet d) := by
  unfold directional
  apply Continuous.neg
  apply continuous_finsetSum
  intro k _
  exact (orbital_contDiff terms (raise jet k) 0).continuous.const_mul (d k)

theorem base_pair_integrable (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (left right : MultiIndex) : Integrable (fun x : Point => orbital terms left x * orbital terms right x) :=
  (GlobalSource.orbital_integrable terms positive right).bdd_mul
    (orbital_contDiff terms left 0).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using! orbital_uniform_bound terms positive left x)

theorem directional_square_integrable (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) : Integrable (fun x : Point => (directional terms jet d x)^2) := by
  have each (k l : Fin 3) : Integrable (fun x : Point =>
      (d k * d l) * (orbital terms (raise jet k) x * orbital terms (raise jet l) x)) :=
    (base_pair_integrable terms positive (raise jet k) (raise jet l)).const_mul _
  convert! integrable_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ (fun l _ => each k l)) using 1
  funext x
  simp only [directional,neg_sq]
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem three_axis_schwarz (d g : Point) :
    (∑ k : Fin 3, d k * g k)^2 ≤ (∑ k : Fin 3, (d k)^2) * (∑ k : Fin 3, (g k)^2) := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (d 0 * g 1 - d 1 * g 0),sq_nonneg (d 0 * g 2 - d 2 * g 0),
    sq_nonneg (d 1 * g 2 - d 2 * g 1)]

theorem directional_energy_bound (terms : List Term) (positive : ∀ term ∈ terms, 0 < term.exponent)
    (jet : MultiIndex) (d : Point) :
    (∫ x : Point, (directional terms jet d x)^2) ≤ (∑ k : Fin 3, (d k)^2) * gradientEnergy terms jet := by
  have each (k : Fin 3) : Integrable (fun x : Point => (orbital terms (raise jet k) x)^2) := by
    simpa only [pow_two] using base_pair_integrable terms positive (raise jet k) (raise jet k)
  have upper : Integrable (fun x : Point => (∑ k : Fin 3, (d k)^2) * (∑ k : Fin 3, (orbital terms (raise jet k) x)^2)) :=
    (integrable_finsetSum Finset.univ (fun k _ => each k)).const_mul _
  calc
    _ ≤ ∫ x : Point, (∑ k : Fin 3, (d k)^2) * (∑ k : Fin 3, (orbital terms (raise jet k) x)^2) := by
      apply integral_mono (directional_square_integrable terms positive jet d) upper
      intro x
      simpa only [directional,neg_sq] using three_axis_schwarz d (fun k => orbital terms (raise jet k) x)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => each k)]
      rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
