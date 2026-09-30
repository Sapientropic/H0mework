import H0mework.Chemistry.LAlanineWholeBandAdjacent.Source

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuationParameter
open WholeBandAdjacentGeometry Set
noncomputable section

theorem joint_membership (p : Point) : p ∈ jointDomain ↔
    p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (cellV 0 0 : ℝ) (cellV 1 1) ∧
      p 2 ∈ Icc (-(1/2 : ℝ)) (1/2) := by
  have leftWidth : (cellV 0 0 : ℝ) < cellV 0 1 := Rat.cast_lt.mpr (source_cells_in_segments 0).2.1
  have rightWidth : (cellV 1 0 : ℝ) < cellV 1 1 := Rat.cast_lt.mpr (source_cells_in_segments 1).2.1
  have seam : (cellV 0 1 : ℝ) = cellV 1 0 := congrArg (fun q : ℚ => (q : ℝ)) cell0_cell1_literal_seam
  constructor
  · rintro (left | right)
    · exact ⟨left.1,⟨left.2.1.1,left.2.1.2.trans (seam ▸ rightWidth.le)⟩,left.2.2⟩
    · exact ⟨right.1,⟨(leftWidth.le.trans_eq seam).trans right.2.1.1,right.2.1.2⟩,right.2.2⟩
  · rintro ⟨alpha,v,time⟩
    by_cases below : p 1 ≤ (cellV 0 1 : ℝ)
    · exact Or.inl ⟨alpha,⟨v.1,below⟩,time⟩
    · exact Or.inr ⟨alpha,⟨seam ▸ (le_of_lt (lt_of_not_ge below)),v.2⟩,time⟩

theorem joint_domain_eq_Icc : jointDomain = Icc (cellLower 0) (cellUpper 1) := by
  ext p
  rw [joint_membership]
  change (p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (cellV 0 0 : ℝ) (cellV 1 1) ∧
    p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)) ↔ (∀ i,cellLower 0 i ≤ p i) ∧ (∀ i,p i ≤ cellUpper 1 i)
  constructor
  · intro h
    constructor <;> intro i <;> fin_cases i
    · exact h.1.1
    · exact h.2.1.1
    · exact h.2.2.1
    · exact h.1.2
    · exact h.2.1.2
    · exact h.2.2.2
  · intro h
    exact ⟨⟨h.1 0,h.2 0⟩,⟨h.1 1,h.2 1⟩,⟨h.1 2,h.2 2⟩⟩

theorem joint_domain_compact : IsCompact jointDomain := by rw [joint_domain_eq_Icc]; exact isCompact_Icc
theorem joint_domain_measurable : MeasurableSet jointDomain := joint_domain_compact.isClosed.measurableSet

theorem joint_domain_uniqueDiffOn : UniqueDiffOn ℝ jointDomain := by
  have inside : (interior jointDomain).Nonempty :=
    (domain_interior_nonempty 0).mono (interior_mono subset_union_left)
  exact uniqueDiffOn_convex ((joint_domain_eq_Icc).symm ▸ convex_Icc (cellLower 0) (cellUpper 1)) inside

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
