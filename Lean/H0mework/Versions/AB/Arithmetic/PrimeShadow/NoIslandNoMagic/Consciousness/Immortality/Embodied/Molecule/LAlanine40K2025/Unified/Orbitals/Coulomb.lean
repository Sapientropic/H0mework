import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource SourceCoulomb
open MeasureTheory
noncomputable section

theorem source_product_bound (b c : Basis) (left right : MultiIndex) (x : Point) :
    ‖orbital (sourceTerms b) left x * orbital (sourceTerms c) right x‖ ≤
      (GlobalSource.sourceOrbitalBound left b : ℝ) * GlobalSource.sourceOrbitalBound right c := by
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact mul_le_mul (source_orbital_uniform_bound left b x) (source_orbital_uniform_bound right c x)
    (abs_nonneg _) (by positivity)

/-- The original AO functions generate the complete four-index Coulomb tensor before any state closure is chosen. -/
theorem quartet_integrable (i j k l : Basis) :
    Integrable (fun z : Point × Point => ao i z.1 * ao j z.1 * (ao k z.2 * ao l z.2) * kernel (z.2-z.1)) :=
  pair_integrable _ _ (source_product_integrable i j zeroJet zeroJet)
    (source_product_integrable k l zeroJet zeroJet)
    ((GlobalSource.sourceOrbitalBound zeroJet k : ℝ) * GlobalSource.sourceOrbitalBound zeroJet l)
    (source_product_bound k l zeroJet zeroJet)

def electronRepulsion (i j k l : Basis) : ℝ := ∫ z : Point × Point,
  ao i z.1 * ao j z.1 * (ao k z.2 * ao l z.2) * kernel (z.2-z.1)

theorem electronRepulsion_first_swap (i j k l : Basis) :
    electronRepulsion i j k l = electronRepulsion j i k l := by
  unfold electronRepulsion
  congr 1
  funext z
  ring

theorem electronRepulsion_second_swap (i j k l : Basis) :
    electronRepulsion i j k l = electronRepulsion i j l k := by
  unfold electronRepulsion
  congr 1
  funext z
  ring

theorem kernel_sub_swap (x y : Point) : kernel (x-y) = kernel (y-x) := by
  unfold kernel SourceCoulomb.distance
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem electronRepulsion_pair_swap (i j k l : Basis) :
    electronRepulsion i j k l = electronRepulsion k l i j := by
  have swapped := integral_prod_swap (μ := (volume : Measure Point)) (ν := (volume : Measure Point))
    (fun z : Point × Point => ao i z.1 * ao j z.1 * (ao k z.2 * ao l z.2) * kernel (z.2-z.1))
  unfold electronRepulsion
  simp only [Measure.volume_eq_prod]
  rw [← swapped]
  congr 1
  funext z
  dsimp only [Prod.swap]
  rw [kernel_sub_swap]
  ring

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
