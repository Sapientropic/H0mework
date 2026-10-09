import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.Partition.Finite

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition.UniqueIndex
open SourceGaussianModel Set MeasureTheory Function
noncomputable section

variable {ι : Type*} [Fintype ι] (regions : ι → Set Point)

/-- Membership selects a unique original region when the source regions are disjoint. -/
noncomputable def locate (x : Point) : Option ι := by
  classical
  exact if h : ∃ i, x ∈ regions i then some (Classical.choose h) else none

theorem locate_some_iff (disjoint : Pairwise (Disjoint on regions)) (i : ι) (x : Point) :
    locate regions x=some i ↔ x∈regions i := by
  constructor
  · intro selected
    by_cases h : ∃ j, x∈regions j
    · have equal : Classical.choose h=i := by
        simpa only [locate,dif_pos h,Option.some.injEq] using selected
      rw [← equal]
      exact Classical.choose_spec h
    · simp [locate,h] at selected
  · intro inside
    have h : ∃ j, x∈regions j := ⟨i,inside⟩
    have chosen : Classical.choose h=i := by
      by_contra different
      exact Set.disjoint_left.mp (disjoint different)
        (Classical.choose_spec h) inside
    simp only [locate,dif_pos h,chosen]

theorem locate_none_iff (x : Point) :
    locate regions x=none ↔ x∉⋃ i, regions i := by
  constructor
  · intro selected covered
    obtain ⟨i,inside⟩ := Set.mem_iUnion.mp covered
    have h : ∃ j, x∈regions j := ⟨i,inside⟩
    simp [locate,h] at selected
  · intro uncovered
    have h : ¬∃ i, x∈regions i := by
      simpa only [Set.mem_iUnion] using uncovered
    simp [locate,h]

theorem some_region (disjoint : Pairwise (Disjoint on regions)) (i : ι) :
    Finite.region (locate regions) (some i)=regions i := by
  ext x
  exact locate_some_iff regions disjoint i x

theorem residual_region :
    Finite.region (locate regions) none=(⋃ i, regions i)ᶜ := by
  ext x
  exact locate_none_iff regions x

theorem fibers_measurable (disjoint : Pairwise (Disjoint on regions))
    (measurable : ∀ i, MeasurableSet (regions i)) (label : Option ι) :
    MeasurableSet (Finite.region (locate regions) label) := by
  cases label with
  | none =>
      rw [residual_region]
      exact (MeasurableSet.iUnion measurable).compl
  | some i =>
      rw [some_region regions disjoint i]
      exact measurable i

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.Partition.UniqueIndex
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
