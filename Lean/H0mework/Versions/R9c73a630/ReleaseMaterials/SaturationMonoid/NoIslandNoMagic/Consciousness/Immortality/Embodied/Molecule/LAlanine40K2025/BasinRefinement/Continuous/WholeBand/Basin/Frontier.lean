import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Cover
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Flow.Transport

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel GlobalSource Set
noncomputable section

theorem flow_image_basin (t : ℝ) : flowHomeomorph t '' basin = basin := by
  ext x
  constructor
  · rintro ⟨y,inside,rfl⟩
    exact (flow_membership y t).mpr inside
  · intro inside
    exact ⟨flow x (-t),(flow_membership x (-t)).mpr inside,
      by
        change flow (flow x (-t)) t = x
        simpa only [neg_neg] using flow_inverse x (-t)⟩

theorem flow_image_frontier (t : ℝ) : flowHomeomorph t '' frontier basin = frontier basin := by
  rw [(flowHomeomorph t).image_frontier,flow_image_basin]

theorem actual_frontier_retention (x : Point) (inside : x ∈ frontier basin) (t : ℝ) :
    flow x t ∈ frontier basin := by
  rw [← flow_image_frontier t]
  exact mem_image_of_mem (flowHomeomorph t) inside

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
