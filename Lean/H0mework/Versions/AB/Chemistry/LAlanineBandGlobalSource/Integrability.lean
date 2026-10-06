import H0mework.Versions.AB.Chemistry.LAlanineBandGlobalSource.Source
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open scoped BigOperators
noncomputable section

theorem factor_integrable (alpha : ℚ) (positive : 0 < alpha) (power order : ℕ) :
    Integrable (factor alpha power order) :=
  gaussian_integrable (by exact_mod_cast positive) _

theorem term_integrable (term : Term) (positive : 0 < term.exponent) (d : MultiIndex) :
    Integrable (value term d) := by
  have each (axis : Fin 3) : Integrable (fun t : ℝ =>
      factor term.exponent (term.powers axis) (d axis) (t - (term.centre axis : ℝ))) :=
    (factor_integrable _ positive _ _).comp_sub_right _
  have product := (Integrable.fintype_prod each).const_mul (term.weight : ℝ)
  convert! product using 1
  funext x
  simp only [value, Fin.prod_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.prod_univ_zero, mul_one, mul_assoc]

theorem orbital_integrable (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (d : MultiIndex) :
    Integrable (orbital terms d) := by
  induction terms with
  | nil =>
    change Integrable (0 : Point → ℝ)
    exact integrable_zero Point ℝ volume
  | cons term rest ih =>
    convert! (term_integrable term (positive term (by simp)) d).add
      (ih (fun other member => positive other (by simp [member]))) using 1

theorem source_orbital_integrable (j : Basis) (d : MultiIndex) :
    Integrable (orbital (sourceTerms j) d) :=
  orbital_integrable _ (source_exponents_positive j) d

theorem source_bilinear_integrable (left right : MultiIndex) :
    Integrable (bilinear sourceTerms densityMatrix left right) := by
  unfold bilinear
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have product := (source_orbital_integrable j right).bdd_mul
    (orbital_contDiff (sourceTerms i) left 0).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => source_orbital_uniform_bound left i x))
  convert! product.const_mul (densityMatrix i j : ℝ) using 1
  funext x
  ring

theorem source_first_integrable (left right : MultiIndex) (axis : Fin 3) :
    Integrable (firstBilinear sourceTerms densityMatrix left right axis) :=
  (source_bilinear_integrable (raise left axis) right).add
    (source_bilinear_integrable left (raise right axis))

theorem sourceDensity_integrable : Integrable sourceDensity := source_bilinear_integrable zeroJet zeroJet

theorem sourceGradient_coordinate_integrable (axis : Fin 3) :
    Integrable (fun x => sourceGradient x axis) := source_first_integrable zeroJet zeroJet axis

theorem sourceHessian_coordinate_integrable (axis direction : Fin 3) :
    Integrable (fun x => sourceHessian x axis direction) :=
  (source_first_integrable (raise zeroJet axis) zeroJet direction).add
    (source_first_integrable zeroJet (raise zeroJet axis) direction)

theorem sourceGradient_integrable : Integrable sourceGradient :=
  Integrable.of_eval sourceGradient_coordinate_integrable

theorem sourceHessian_integrable : Integrable sourceHessian :=
  Integrable.of_eval (fun axis => Integrable.of_eval (sourceHessian_coordinate_integrable axis))

theorem source_second_integrable (left right : MultiIndex) (axis : Fin 3) :
    Integrable (secondBilinear sourceTerms densityMatrix left right axis) :=
  ((source_bilinear_integrable (raise (raise left axis) axis) right).add
    ((source_bilinear_integrable (raise left axis) (raise right axis)).const_mul 2)).add
      (source_bilinear_integrable left (raise (raise right axis) axis))

theorem sourceLaplacian_integrable : Integrable (laplacian sourceTerms densityMatrix) :=
  integrable_finsetSum Finset.univ (fun axis _ => source_second_integrable zeroJet zeroJet axis)

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
