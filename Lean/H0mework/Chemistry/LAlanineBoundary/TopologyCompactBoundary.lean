import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Topology

namespace WholeCellBoundaryTopology

/-- Local homeomorphisms and compact-source injectivity suffice; ambient injectivity is not needed. -/
theorem frontier_image_of_local_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    (f : X → Y) (s : Set X) (compact : IsCompact s) (continuous : Continuous f)
    (injective : InjOn f s)
    (localCharts : ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y, (e : X → Y) = f ∧ x ∈ e.source) :
    frontier (f '' s) = f '' frontier s := by
  have locally_injective : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u := by
    intro x hx
    obtain ⟨e, computes, inside⟩ := localCharts x hx
    exact ⟨e.source, e.open_source.mem_nhds inside, computes ▸ e.injOn⟩
  obtain ⟨u, open_u, contains, injective_u⟩ :=
    injective.exists_isOpen_superset compact (fun x _ => continuous.continuousAt) locally_injective
  have boundary_at (x : X) (inside : x ∈ s) :
      f x ∈ frontier (f '' s) ↔ x ∈ frontier s := by
    obtain ⟨e, computes, source⟩ := localCharts x inside
    let chart := e.restrOpen u open_u
    have chart_computes : (chart : X → Y) = f := computes
    have chart_source : x ∈ chart.source := ⟨source, contains inside⟩
    have image : chart.IsImage s (f '' s) := by
      intro y hy
      rw [chart_computes]
      constructor
      · rintro ⟨z, hz, same⟩
        have zy : z = y := injective_u (contains hz) hy.2 same
        exact zy ▸ hz
      · intro hy
        exact mem_image_of_mem f hy
    simpa only [chart_computes] using image.frontier.apply_mem_iff chart_source
  apply subset_antisymm
  · intro y hy
    have member : y ∈ f '' s := by
      simpa only [(compact.image continuous).isClosed.closure_eq] using frontier_subset_closure hy
    obtain ⟨x, hx, rfl⟩ := member
    exact ⟨x, (boundary_at x hx).mp hy, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have member : x ∈ s := by
      simpa only [compact.isClosed.closure_eq] using frontier_subset_closure hx
    exact (boundary_at x member).mpr hx

end WholeCellBoundaryTopology
