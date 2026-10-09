import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Additivity

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter MeasureTheory
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.BasinRefinement.WholeBandIQA
open scoped Topology
noncomputable section

theorem basins_disjoint_of_critical_ne (left right : AttractingSeed)
    (different : left.criticalPoint ≠ right.criticalPoint) :
    Disjoint (basin left) (basin right) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact different (tendsto_nhds_unique hx hy)

def pairRegion (left right : AttractingSeed) : Set (Point × Point) :=
  basin left ×ˢ basin right

def pairPatch (left right : AttractingSeed) (n : ℕ) : Set (Point × Point) :=
  entryPatch left n ×ˢ entryPatch right n

theorem pair_region_measurable (left right : AttractingSeed) :
    MeasurableSet (pairRegion left right) :=
  (basin_measurable left).prod (basin_measurable right)

theorem pair_patch_monotone (left right : AttractingSeed) :
    Monotone (pairPatch left right) :=
  fun _ _ ordered => Set.prod_mono
    (entryPatch_monotone left ordered) (entryPatch_monotone right ordered)

theorem pair_region_union (left right : AttractingSeed) :
    pairRegion left right = ⋃ n : ℕ, pairPatch left right n := by
  ext z
  constructor
  · intro inside
    obtain ⟨i,hi⟩ := basin_eventual_entry left z.1 inside.1
    obtain ⟨j,hj⟩ := basin_eventual_entry right z.2 inside.2
    exact mem_iUnion.mpr ⟨max i j,
      entryPatch_monotone left (le_max_left _ _) hi,
      entryPatch_monotone right (le_max_right _ _) hj⟩
  · intro inside
    obtain ⟨n,h⟩ := mem_iUnion.mp inside
    exact ⟨entryPatch_subset_basin left n h.1,
      entryPatch_subset_basin right n h.2⟩

def halfPairEnergy (left right : AttractingSeed) : ℝ :=
  (1/2 : ℝ) * ∫ z in pairRegion left right, realPairIntegrand z

def interatomicPairEnergy (left right : AttractingSeed) : ℝ :=
  halfPairEnergy left right+halfPairEnergy right left

theorem half_pair_energy_nonnegative (left right : AttractingSeed) :
    0 ≤ halfPairEnergy left right :=
  mul_nonneg (by norm_num)
    (setIntegral_nonneg (pair_region_measurable left right)
      (fun z _ => real_pair_integrand_nonnegative z))

theorem half_pair_energy_symmetric (left right : AttractingSeed) :
    halfPairEnergy left right=halfPairEnergy right left := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    (basin left) (basin right) realPairIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realPairIntegrand z.swap=realPairIntegrand z :=
    Slater.real_pair_integrand_swap z
  simp_rw [hpoint] at h
  dsimp [halfPairEnergy,pairRegion]
  rw [h]

theorem interatomic_pair_energy_twice (left right : AttractingSeed) :
    interatomicPairEnergy left right=2*halfPairEnergy left right := by
  rw [interatomicPairEnergy,← half_pair_energy_symmetric left right]
  ring

theorem interatomic_pair_energy_nonnegative (left right : AttractingSeed) :
    0 ≤ interatomicPairEnergy left right := by
  rw [interatomic_pair_energy_twice]
  exact mul_nonneg (by norm_num) (half_pair_energy_nonnegative left right)

theorem half_pair_energy_patch_limit (left right : AttractingSeed) :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in pairPatch left right n,
      realPairIntegrand z) atTop (𝓝 (halfPairEnergy left right)) := by
  have h : Tendsto (fun n : ℕ => ∫ z in pairPatch left right n,
      realPairIntegrand z) atTop
      (𝓝 (∫ z in pairRegion left right, realPairIntegrand z)) := by
    rw [pair_region_union]
    exact tendsto_setIntegral_of_monotone
      (fun n => (entryPatch_open left n).measurableSet.prod
        (entryPatch_open right n).measurableSet)
      (pair_patch_monotone left right) real_pair_integrable.integrableOn
  simpa only [halfPairEnergy] using h.const_mul (1/2 : ℝ)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
