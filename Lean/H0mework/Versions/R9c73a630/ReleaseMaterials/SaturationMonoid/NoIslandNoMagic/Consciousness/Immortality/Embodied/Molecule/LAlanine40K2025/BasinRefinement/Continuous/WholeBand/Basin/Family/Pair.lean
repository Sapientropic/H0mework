import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Separation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Slater.Additivity

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource WholeBandBasin Set Filter MeasureTheory
open LAlanine40K2025.BasinRefinement.WholeBandIQA
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open scoped Topology
noncomputable section

def crossRegion : Set (Point × Point) := atom006Basin ×ˢ WholeBandBasin.basin
def reverseRegion : Set (Point × Point) := WholeBandBasin.basin ×ˢ atom006Basin
def crossPatch (n : ℕ) : Set (Point × Point) :=
  atom006Patches n ×ˢ WholeBandBasin.entryPatch n

theorem cross_region_measurable : MeasurableSet crossRegion :=
  atom006_basin_open.measurableSet.prod WholeBandBasin.basin_measurable

theorem reverse_region_measurable : MeasurableSet reverseRegion :=
  WholeBandBasin.basin_measurable.prod atom006_basin_open.measurableSet

theorem crossPatch_monotone : Monotone crossPatch :=
  fun _ _ ordered => Set.prod_mono
    (atom006_patches_monotone ordered)
    (WholeBandBasin.entryPatch_monotone ordered)

theorem cross_region_union : crossRegion = ⋃ n : ℕ, crossPatch n := by
  ext z
  constructor
  · intro inside
    obtain ⟨i,hi⟩ := basin_eventual_entry atom006Seed z.1 inside.1
    obtain ⟨j,hj⟩ := WholeBandBasin.basin_eventual_entry z.2 inside.2
    exact mem_iUnion.mpr ⟨max i j,
      atom006_patches_monotone (le_max_left _ _) hi,
      WholeBandBasin.entryPatch_monotone (le_max_right _ _) hj⟩
  · intro inside
    obtain ⟨n,h⟩ := mem_iUnion.mp inside
    exact ⟨entryPatch_subset_basin atom006Seed n h.1,
      WholeBandBasin.entryPatch_subset_basin n h.2⟩

def crossEnergy : ℝ := (1/2 : ℝ) * ∫ z in crossRegion, realPairIntegrand z
def reverseEnergy : ℝ := (1/2 : ℝ) * ∫ z in reverseRegion, realPairIntegrand z
def interatomicEnergy : ℝ := crossEnergy+reverseEnergy

theorem cross_energy_integrable :
    IntegrableOn realPairIntegrand crossRegion ∧
      IntegrableOn realPairIntegrand reverseRegion :=
  ⟨real_pair_integrable.integrableOn,real_pair_integrable.integrableOn⟩

theorem cross_energy_nonnegative : 0 ≤ crossEnergy ∧ 0 ≤ reverseEnergy := by
  constructor
  · exact mul_nonneg (by norm_num)
      (setIntegral_nonneg cross_region_measurable
        (fun z _ => real_pair_integrand_nonnegative z))
  · exact mul_nonneg (by norm_num)
      (setIntegral_nonneg reverse_region_measurable
        (fun z _ => real_pair_integrand_nonnegative z))

theorem cross_energy_symmetric : crossEnergy=reverseEnergy := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    atom006Basin WholeBandBasin.basin realPairIntegrand
  rw [← Measure.volume_eq_prod] at h
  have hpoint (z : Point × Point) : realPairIntegrand z.swap=realPairIntegrand z :=
    Slater.real_pair_integrand_swap z
  simp_rw [hpoint] at h
  dsimp [crossEnergy,reverseEnergy,crossRegion,reverseRegion]
  rw [h]

theorem interatomic_energy_twice : interatomicEnergy=2*crossEnergy := by
  rw [interatomicEnergy,← cross_energy_symmetric]
  ring

theorem interatomic_energy_nonnegative : 0 ≤ interatomicEnergy := by
  rw [interatomic_energy_twice]
  exact mul_nonneg (by norm_num) cross_energy_nonnegative.1

theorem cross_energy_patch_limit :
    Tendsto (fun n : ℕ => (1/2 : ℝ) * ∫ z in crossPatch n,
      realPairIntegrand z) atTop (𝓝 crossEnergy) := by
  have h : Tendsto (fun n : ℕ => ∫ z in crossPatch n,
      realPairIntegrand z) atTop
      (𝓝 (∫ z in crossRegion, realPairIntegrand z)) := by
    rw [cross_region_union]
    exact tendsto_setIntegral_of_monotone
      (fun n => (entryPatch_open atom006Seed n).measurableSet.prod
        (WholeBandBasin.entryPatch_open n).measurableSet)
      crossPatch_monotone real_pair_integrable.integrableOn
  simpa only [crossEnergy] using h.const_mul (1/2 : ℝ)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
