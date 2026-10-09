import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin
open SourceGaussianModel GlobalSource Set Filter MeasureTheory
open WholeBandAttractor.Atom007
open scoped Topology
noncomputable section

theorem critical_inside_neighborhood : actualZero.point ∈ attractingNeighborhood :=
  Metric.mem_ball_self (Attractor.neighborhood_geometry actualZero actual_zero_interior).1

theorem basin_eventual_entry (x : Point) (inside : x ∈ basin) :
    ∃ n : ℕ, x ∈ entryPatch n := by
  have eventual : ∀ᶠ t : ℝ in atTop, flow x t ∈ attractingNeighborhood :=
    inside.eventually (attracting_open.mem_nhds critical_inside_neighborhood)
  obtain ⟨a,after⟩ := eventually_atTop.mp eventual
  obtain ⟨n,beyond⟩ := exists_nat_gt a
  exact ⟨n,after n beyond.le⟩

theorem basin_eq_union : basin = ⋃ n : ℕ, entryPatch n := by
  ext x
  simp only [mem_iUnion]
  exact ⟨basin_eventual_entry x,fun ⟨n,inside⟩ => entryPatch_subset_basin n inside⟩

theorem entryPatch_open (n : ℕ) : IsOpen (entryPatch n) :=
  attracting_open.preimage (flow_initial_continuous n (Nat.cast_nonneg n))

theorem basin_open : IsOpen basin := by
  rw [basin_eq_union]
  exact isOpen_iUnion entryPatch_open

theorem basin_measurable : MeasurableSet basin := basin_open.measurableSet

theorem entryPatch_monotone : Monotone entryPatch := by
  intro m n ordered x inside
  have step := actual_positive_retention (flow x m) inside ((n : ℝ)-m) (sub_nonneg.mpr (by exact_mod_cast ordered))
  rw [← flow_add] at step
  simpa only [entryPatch,mem_preimage,add_sub_cancel] using step

theorem basin_volume_limit : Tendsto (fun n : ℕ => volume (entryPatch n)) atTop (𝓝 (volume basin)) := by
  rw [basin_eq_union]
  exact tendsto_measure_iUnion_atTop entryPatch_monotone

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
