import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Integrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel Set MeasureTheory GlobalSource ContinuousGradient WholeBandAttractor.Atom007
noncomputable section

structure BasinMaterial where
  flow : Point → ℝ → Point
  criticalPoint : Point
  neighborhood : Set Point
  basin : Set Point
  patches : ℕ → Set Point
  density : Point → ℝ
  densityIntegral : ℝ
  hartreeIntegral : ℝ

def material : BasinMaterial where
  flow := GlobalSource.flow
  criticalPoint := actualZero.point
  neighborhood := attractingNeighborhood
  basin := WholeBandBasin.basin
  patches := entryPatch
  density := sourceDensity
  densityIntegral := ∫ x in basin, sourceDensity x
  hartreeIntegral := ∫ z in basin ×ˢ basin, sourceDensity z.1 * sourceDensity z.2 * SourceCoulomb.kernel (z.2-z.1)

structure BasinClosure : Prop where
  original_zero : type_of% actual_gradient_zero
  actual_basin : ∀ x, x ∈ material.basin ↔ Filter.Tendsto (material.flow x) Filter.atTop (nhds material.criticalPoint)
  two_sided : type_of% flow_membership
  local_entry : type_of% attracting_subset_basin
  generated_cover : type_of% basin_eq_union
  actual_entry : type_of% basin_eventual_entry
  open_basin : type_of% basin_open
  positive_volume : type_of% basin_positive_volume
  increasing : type_of% entryPatch_monotone
  volume_limit : type_of% basin_volume_limit
  density_limit : type_of% density_integral_limit
  laplacian_limit : type_of% laplacian_integral_limit
  bilinear_limit : type_of% bilinear_integral_limit
  actual_pairs : type_of% basin_pair_union
  hartree_limit : type_of% hartree_integral_limit

theorem sourceGeneratedBasin : BasinClosure :=
  ⟨actual_gradient_zero,fun _ => Iff.rfl,flow_membership,attracting_subset_basin,basin_eq_union,
    basin_eventual_entry,basin_open,basin_positive_volume,entryPatch_monotone,basin_volume_limit,
    density_integral_limit,laplacian_integral_limit,bilinear_integral_limit,basin_pair_union,hartree_integral_limit⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
