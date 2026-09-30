import H0mework.Chemistry.LAlanineWholeCell.PartitionSource
import Mathlib.MeasureTheory.Order.UpperLower
import Mathlib.Topology.Constructions

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellPartition

open SourceGaussianModel Set MeasureTheory

noncomputable section

theorem quarter_bounds_within_full : ∀ q : Quarter, ∀ axis : Fin 3,
    fullLowerQ axis ≤ quarterLowerQ q axis ∧ quarterUpperQ q axis ≤ fullUpperQ axis := by decide +kernel

theorem quarter_s_separated : ∀ i j : Quarter, i < j → quarterUpperQ i 2 ≤ quarterLowerQ j 2 := by
  decide +kernel

theorem quarter_subset_full (q : Quarter) : quarterDomain q ⊆ fullDomain := by
  intro p hp
  exact ⟨fun axis => (Rat.cast_le.mpr (quarter_bounds_within_full q axis).1).trans (hp.1 axis),
    fun axis => (hp.2 axis).trans (Rat.cast_le.mpr (quarter_bounds_within_full q axis).2)⟩

theorem quarter_mem_iff (q : Quarter) (p : Point) :
    p ∈ quarterDomain q ↔ p ∈ fullDomain ∧
      (cutQ (lowerCut q) : ℝ) ≤ p 2 ∧ p 2 ≤ (cutQ (upperCut q) : ℝ) := by
  constructor
  · intro hp
    exact ⟨quarter_subset_full q hp, hp.1 2, hp.2 2⟩
  · rintro ⟨hp, lower, upper⟩
    constructor
    · intro axis
      by_cases h : axis = 2
      · subst axis
        exact lower
      · simpa only [quarterLower, quarterLowerQ, if_neg h, fullLower] using hp.1 axis
    · intro axis
      by_cases h : axis = 2
      · subst axis
        exact upper
      · simpa only [quarterUpper, quarterUpperQ, if_neg h, fullUpper] using hp.2 axis

theorem fullDomain_eq_iUnion_quarters : fullDomain = ⋃ q : Quarter, quarterDomain q := by
  apply subset_antisymm
  · intro p hp
    have h0 : (cutQ 0 : ℝ) ≤ p 2 := hp.1 2
    have h4 : p 2 ≤ (cutQ 4 : ℝ) := hp.2 2
    by_cases h1 : p 2 ≤ (cutQ 1 : ℝ)
    · exact mem_iUnion.mpr ⟨0, (quarter_mem_iff 0 p).mpr ⟨hp, h0, h1⟩⟩
    by_cases h2 : p 2 ≤ (cutQ 2 : ℝ)
    · exact mem_iUnion.mpr ⟨1, (quarter_mem_iff 1 p).mpr ⟨hp, (lt_of_not_ge h1).le, h2⟩⟩
    by_cases h3 : p 2 ≤ (cutQ 3 : ℝ)
    · exact mem_iUnion.mpr ⟨2, (quarter_mem_iff 2 p).mpr ⟨hp, (lt_of_not_ge h2).le, h3⟩⟩
    · exact mem_iUnion.mpr ⟨3, (quarter_mem_iff 3 p).mpr ⟨hp, (lt_of_not_ge h3).le, h4⟩⟩
  · exact iUnion_subset quarter_subset_full

theorem quarter_interior (q : Quarter) :
    interior (quarterDomain q) = Set.pi Set.univ
      (fun axis => Set.Ioo (quarterLower q axis) (quarterUpper q axis)) := by
  unfold quarterDomain
  rw [← pi_univ_Icc, interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]

theorem quarter_interiors_disjoint : Pairwise (fun i j : Quarter =>
    Disjoint (interior (quarterDomain i)) (interior (quarterDomain j))) := by
  intro i j different
  apply disjoint_left.mpr
  intro p hi hj
  rw [quarter_interior] at hi hj
  have ilo := (hi 2 (mem_univ 2)).1
  have ihi := (hi 2 (mem_univ 2)).2
  have jlo := (hj 2 (mem_univ 2)).1
  have jhi := (hj 2 (mem_univ 2)).2
  rcases lt_or_gt_of_ne different with earlier | later
  · have h : (quarterUpperQ i 2 : ℝ) ≤ (quarterLowerQ j 2 : ℝ) :=
      Rat.cast_le.mpr (quarter_s_separated i j earlier)
    change (quarterUpperQ i 2 : ℝ) > p 2 at ihi
    change (quarterLowerQ j 2 : ℝ) < p 2 at jlo
    linarith
  · have h : (quarterUpperQ j 2 : ℝ) ≤ (quarterLowerQ i 2 : ℝ) :=
      Rat.cast_le.mpr (quarter_s_separated j i later)
    change (quarterUpperQ j 2 : ℝ) > p 2 at jhi
    change (quarterLowerQ i 2 : ℝ) < p 2 at ilo
    linarith

theorem quarter_boundary_null (q : Quarter) : volume (frontier (quarterDomain q)) = 0 := by
  unfold quarterDomain
  exact Set.OrdConnected.null_frontier ordConnected_Icc

theorem full_boundary_null : volume (frontier fullDomain) = 0 := by
  unfold fullDomain
  exact Set.OrdConnected.null_frontier ordConnected_Icc

theorem quarters_ae_disjoint : Pairwise (fun i j => AEDisjoint volume (quarterDomain i) (quarterDomain j)) := by
  intro i j different
  exact (quarter_interiors_disjoint different).aedisjoint.congr
    (interior_ae_eq_of_null_frontier (quarter_boundary_null i)).symm
    (interior_ae_eq_of_null_frontier (quarter_boundary_null j)).symm

theorem quarter_measurable (q : Quarter) : MeasurableSet (quarterDomain q) := measurableSet_Icc
theorem full_measurable : MeasurableSet fullDomain := measurableSet_Icc
theorem quarter_compact (q : Quarter) : IsCompact (quarterDomain q) := isCompact_Icc
theorem full_compact : IsCompact fullDomain := isCompact_Icc

theorem quarter_nonempty (q : Quarter) : (quarterDomain q).Nonempty :=
  ⟨quarterLower q, le_rfl, fun axis => Rat.cast_le.mpr (quarter_ordered q axis).le⟩

theorem full_nonempty : fullDomain.Nonempty :=
  ⟨fullLower, le_rfl, fun axis => Rat.cast_le.mpr (full_ordered axis).le⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellPartition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
