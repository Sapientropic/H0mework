import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.SourceA007Flow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Flow.Initial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel ContinuousGradient GlobalSource Set Filter MeasureTheory
open WholeBandAttractor.Atom007
open scoped Topology
noncomputable section

/-- The basin is generated from the original whole-space flow and actual critical point. -/
def basin : Set Point := {x | Tendsto (flow x) atTop (𝓝 actualZero.point)}

def entryPatch (n : ℕ) : Set Point := (fun x => flow x (n : ℝ)) ⁻¹' attractingNeighborhood

theorem attracting_subset_basin : attractingNeighborhood ⊆ basin := actual_convergence

theorem basin_nonempty : basin.Nonempty := attracting_nonempty.mono attracting_subset_basin

theorem shifted_limit (x : Point) (t : ℝ) :
    Tendsto (fun s : ℝ => flow x (t+s)) atTop (𝓝 actualZero.point) ↔ x ∈ basin := by
  have equality : (fun s : ℝ => flow x (t+s)) = (flow x) ∘ (fun s => s+t) := by
    funext s
    simp only [Function.comp_apply,add_comm]
  rw [equality,← tendsto_map'_iff,Filter.map_add_atTop_eq]
  rfl

theorem flow_membership (x : Point) (t : ℝ) : flow x t ∈ basin ↔ x ∈ basin := by
  have equality : flow (flow x t) = fun s : ℝ => flow x (t+s) := by
    funext s
    exact (flow_add x t s).symm
  change Tendsto (flow (flow x t)) atTop (𝓝 actualZero.point) ↔ _
  rw [equality]
  exact shifted_limit x t

theorem entryPatch_subset_basin (n : ℕ) : entryPatch n ⊆ basin := by
  intro x inside
  exact (flow_membership x n).mp (attracting_subset_basin inside)

theorem basin_positive_volume : 0 < volume basin :=
  attracting_positive_volume.trans_le (measure_mono attracting_subset_basin)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
