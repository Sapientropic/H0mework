import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Flow.Initial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
open SourceGaussianModel GlobalSource Set Filter MeasureTheory
open scoped Topology
noncomputable section

structure AttractingSeed where
  criticalPoint : Point
  neighborhood : Set Point
  criticalInside : criticalPoint ∈ neighborhood
  neighborhoodOpen : IsOpen neighborhood
  positiveVolume : 0 < volume neighborhood
  retention : ∀ x ∈ neighborhood, ∀ t : ℝ, 0 ≤ t → flow x t ∈ neighborhood
  convergence : ∀ x ∈ neighborhood, Tendsto (flow x) atTop (𝓝 criticalPoint)

def basin (seed : AttractingSeed) : Set Point :=
  {x | Tendsto (flow x) atTop (𝓝 seed.criticalPoint)}

def entryPatch (seed : AttractingSeed) (n : ℕ) : Set Point :=
  (fun x => flow x (n : ℝ)) ⁻¹' seed.neighborhood

theorem neighborhood_subset_basin (seed : AttractingSeed) :
    seed.neighborhood ⊆ basin seed := seed.convergence

theorem basin_positive_volume (seed : AttractingSeed) :
    0 < volume (basin seed) :=
  seed.positiveVolume.trans_le (measure_mono (neighborhood_subset_basin seed))

theorem shifted_limit (seed : AttractingSeed) (x : Point) (t : ℝ) :
    Tendsto (fun s : ℝ => flow x (t+s)) atTop (𝓝 seed.criticalPoint) ↔
      x ∈ basin seed := by
  have equality : (fun s : ℝ => flow x (t+s)) = (flow x) ∘ (fun s => s+t) := by
    funext s
    simp only [Function.comp_apply,add_comm]
  rw [equality,← tendsto_map'_iff,Filter.map_add_atTop_eq]
  rfl

theorem flow_membership (seed : AttractingSeed) (x : Point) (t : ℝ) :
    flow x t ∈ basin seed ↔ x ∈ basin seed := by
  have equality : flow (flow x t) = fun s : ℝ => flow x (t+s) := by
    funext s
    exact (flow_add x t s).symm
  change Tendsto (flow (flow x t)) atTop (𝓝 seed.criticalPoint) ↔ _
  rw [equality]
  exact shifted_limit seed x t

theorem entryPatch_subset_basin (seed : AttractingSeed) (n : ℕ) :
    entryPatch seed n ⊆ basin seed := by
  intro x inside
  exact (flow_membership seed x n).mp (neighborhood_subset_basin seed inside)

theorem basin_eventual_entry (seed : AttractingSeed) (x : Point)
    (inside : x ∈ basin seed) : ∃ n : ℕ, x ∈ entryPatch seed n := by
  have eventual : ∀ᶠ t : ℝ in atTop, flow x t ∈ seed.neighborhood :=
    inside.eventually (seed.neighborhoodOpen.mem_nhds seed.criticalInside)
  obtain ⟨a,after⟩ := eventually_atTop.mp eventual
  obtain ⟨n,beyond⟩ := exists_nat_gt a
  exact ⟨n,after n beyond.le⟩

theorem basin_eq_union (seed : AttractingSeed) :
    basin seed = ⋃ n : ℕ, entryPatch seed n := by
  ext x
  simp only [mem_iUnion]
  exact ⟨basin_eventual_entry seed x,fun ⟨n,inside⟩ =>
    entryPatch_subset_basin seed n inside⟩

theorem entryPatch_open (seed : AttractingSeed) (n : ℕ) :
    IsOpen (entryPatch seed n) :=
  seed.neighborhoodOpen.preimage (flow_initial_continuous n (Nat.cast_nonneg n))

theorem basin_open (seed : AttractingSeed) : IsOpen (basin seed) := by
  rw [basin_eq_union]
  exact isOpen_iUnion (entryPatch_open seed)

theorem basin_measurable (seed : AttractingSeed) : MeasurableSet (basin seed) :=
  (basin_open seed).measurableSet

theorem entryPatch_monotone (seed : AttractingSeed) :
    Monotone (entryPatch seed) := by
  intro m n ordered x inside
  have step := seed.retention (flow x m) inside ((n : ℝ)-m)
    (sub_nonneg.mpr (by exact_mod_cast ordered))
  rw [← flow_add] at step
  simpa only [entryPatch,mem_preimage,add_sub_cancel] using step

theorem basin_volume_limit (seed : AttractingSeed) :
    Tendsto (fun n : ℕ => volume (entryPatch seed n)) atTop
      (𝓝 (volume (basin seed))) := by
  rw [basin_eq_union]
  exact tendsto_measure_iUnion_atTop (entryPatch_monotone seed)

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
