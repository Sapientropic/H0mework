import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Cover
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel SourceFiniteData GlobalSource ContinuousGradient Set Filter MeasureTheory
open scoped Topology
noncomputable section

theorem basin_integral_limit {f : Point → ℝ} (integrable : Integrable f) :
    Tendsto (fun n : ℕ => ∫ x in entryPatch n, f x) atTop (𝓝 (∫ x in basin, f x)) := by
  rw [basin_eq_union]
  exact tendsto_setIntegral_of_monotone (fun n => (entryPatch_open n).measurableSet)
    entryPatch_monotone integrable.integrableOn

theorem density_integral_limit :
    Tendsto (fun n : ℕ => ∫ x in entryPatch n, sourceDensity x) atTop
      (𝓝 (∫ x in basin, sourceDensity x)) := basin_integral_limit sourceDensity_integrable

theorem laplacian_integral_limit :
    Tendsto (fun n : ℕ => ∫ x in entryPatch n, laplacian sourceTerms densityMatrix x) atTop
      (𝓝 (∫ x in basin, laplacian sourceTerms densityMatrix x)) := basin_integral_limit sourceLaplacian_integrable

theorem bilinear_integral_limit (left right : MultiIndex) :
    Tendsto (fun n : ℕ => ∫ x in entryPatch n, bilinear sourceTerms densityMatrix left right x) atTop
      (𝓝 (∫ x in basin, bilinear sourceTerms densityMatrix left right x)) :=
  basin_integral_limit (source_bilinear_integrable left right)

def pairPatch (n : ℕ) : Set (Point × Point) := entryPatch n ×ˢ entryPatch n

theorem pairPatch_monotone : Monotone pairPatch :=
  fun _ _ ordered => Set.prod_mono (entryPatch_monotone ordered) (entryPatch_monotone ordered)

theorem basin_pair_union : basin ×ˢ basin = ⋃ n : ℕ, pairPatch n := by
  ext z
  constructor
  · intro inside
    obtain ⟨i,hi⟩ := basin_eventual_entry z.1 inside.1
    obtain ⟨j,hj⟩ := basin_eventual_entry z.2 inside.2
    exact mem_iUnion.mpr ⟨max i j,entryPatch_monotone (le_max_left _ _) hi,
      entryPatch_monotone (le_max_right _ _) hj⟩
  · intro inside
    obtain ⟨n,h⟩ := mem_iUnion.mp inside
    exact ⟨entryPatch_subset_basin n h.1,entryPatch_subset_basin n h.2⟩

theorem hartree_integral_limit :
    Tendsto (fun n : ℕ => ∫ z in pairPatch n,
      sourceDensity z.1 * sourceDensity z.2 * SourceCoulomb.kernel (z.2-z.1)) atTop
      (𝓝 (∫ z in basin ×ˢ basin, sourceDensity z.1 * sourceDensity z.2 * SourceCoulomb.kernel (z.2-z.1))) := by
  rw [basin_pair_union]
  exact tendsto_setIntegral_of_monotone (fun n => (entryPatch_open n).measurableSet.prod
      (entryPatch_open n).measurableSet) pairPatch_monotone SourceCoulomb.source_hartree_integrable.integrableOn

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
