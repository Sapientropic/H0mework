import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Topology

namespace WholeCellBoundaryTopology

/-- A compact embedded set transports its frontier through local ambient extensions;
the original function is only required to be continuous on that set. -/
theorem frontier_image_of_local_extensions {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    (f : X → Y) (s : Set X) (compact : IsCompact s) (continuous : ContinuousOn f s)
    (injective : InjOn f s)
    (localCharts : ∀ x ∈ s, ∃ e : OpenPartialHomeomorph X Y,
      x ∈ e.source ∧ EqOn e f (s ∩ e.source)) :
    frontier (f '' s) = f '' frontier s := by
  have boundary_at (x : X) (inside : x ∈ s) :
      f x ∈ frontier (f '' s) ↔ x ∈ frontier s := by
    obtain ⟨e, source, agrees⟩ := localCharts x inside
    let far : Set Y := f '' (s \ e.source)
    have far_compact : IsCompact far :=
      (compact.diff e.open_source).image_of_continuousOn (continuous.mono sdiff_subset)
    let target : Set Y := e.target \ far
    have target_open : IsOpen target := e.open_target.sdiff far_compact.isClosed
    have at_x : e x = f x := agrees ⟨inside, source⟩
    have avoids_far : e x ∉ far := by
      rintro ⟨z, ⟨zs, outside⟩, same⟩
      have equal : z = x := injective zs inside (same.trans at_x)
      exact outside (equal.symm ▸ source)
    let chart : OpenPartialHomeomorph X Y := (e.symm.restrOpen target target_open).symm
    have chart_source : x ∈ chart.source := ⟨source, e.map_source source, avoids_far⟩
    have image : chart.IsImage s (f '' s) := by
      intro y hy
      change y ∈ e.source ∧ e y ∈ e.target \ far at hy
      constructor
      · rintro ⟨z, zs, same⟩
        change f z = e y at same
        have source_z : z ∈ e.source := by
          by_contra outside
          exact hy.2.2 ⟨z, ⟨zs, outside⟩, same⟩
        have equal : z = y := e.injOn source_z hy.1 ((agrees ⟨zs, source_z⟩).trans same)
        exact equal ▸ zs
      · intro ys
        exact ⟨y, ys, (agrees ⟨ys, hy.1⟩).symm⟩
    have result := image.frontier.apply_mem_iff chart_source
    change e x ∈ frontier (f '' s) ↔ x ∈ frontier s at result
    rwa [at_x] at result
  apply subset_antisymm
  · intro y hy
    have member : y ∈ f '' s := by
      simpa only [(compact.image_of_continuousOn continuous).isClosed.closure_eq] using
        frontier_subset_closure hy
    obtain ⟨x, hx, rfl⟩ := member
    exact ⟨x, (boundary_at x hx).mp hy, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have member : x ∈ s := by
      simpa only [compact.isClosed.closure_eq] using frontier_subset_closure hx
    exact (boundary_at x member).mpr hx

end WholeCellBoundaryTopology
