import H0mework.Chemistry.LAlanineBandCellDifferential.Seed
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandActual Set
noncomputable section

def cell0Lower : Point := ![0, (cellV 0 0 : ℝ), -(1/2)]
def cell0Upper : Point := ![1, (cellV 0 1 : ℝ), 1/2]

theorem cell0_domain_eq_Icc : cellDomain 0 = Icc cell0Lower cell0Upper := by
  ext p
  change (p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (cellV 0 0 : ℝ) (cellV 0 1) ∧
    p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)) ↔ (∀ i, cell0Lower i ≤ p i) ∧ (∀ i, p i ≤ cell0Upper i)
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
    exact ⟨⟨h.1 0, h.2 0⟩, ⟨h.1 1, h.2 1⟩, ⟨h.1 2, h.2 2⟩⟩

theorem cell0_axis_strict (j : Fin 3) : cell0Lower j < cell0Upper j := by
  fin_cases j
  · norm_num [cell0Lower, cell0Upper]
  · exact Rat.cast_lt.mpr (source_cells_in_segments 0).2.1
  · norm_num [cell0Lower, cell0Upper]

theorem cell0_coordinate_mem (p : Cell0Point) (j : Fin 3) :
    p.val j ∈ Icc (cell0Lower j) (cell0Upper j) := by
  have inside : p.val ∈ Icc cell0Lower cell0Upper := cell0_domain_eq_Icc ▸ p.property
  exact ⟨inside.1 j, inside.2 j⟩

theorem cell0_line_inside (p : Cell0Point) (j : Fin 3) :
    MapsTo (Function.update p.val j) (Icc (cell0Lower j) (cell0Upper j)) (cellDomain 0) := by
  have inside : p.val ∈ Icc cell0Lower cell0Upper := cell0_domain_eq_Icc ▸ p.property
  intro r hr
  apply cell0_domain_eq_Icc.symm.subset
  constructor <;> intro i <;> by_cases hi : i = j
  · subst i
    simpa using hr.1
  · simpa only [Function.update_of_ne hi] using inside.1 i
  · subst i
    simpa using hr.2
  · simpa only [Function.update_of_ne hi] using inside.2 i

theorem cell0_domain_interior_nonempty : (interior (cellDomain 0)).Nonempty := by
  rw [cell0_domain_eq_Icc, ← pi_univ_Icc, interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]
  refine ⟨fun i => (cell0Lower i + cell0Upper i) / 2, ?_⟩
  intro i _
  have ordered := cell0_axis_strict i
  constructor <;> dsimp only <;> linarith

theorem cell0_domain_uniqueDiffOn : UniqueDiffOn ℝ (cellDomain 0) :=
  uniqueDiffOn_convex (cell0_domain_eq_Icc.symm ▸ convex_Icc cell0Lower cell0Upper)
    cell0_domain_interior_nonempty

theorem cell0_uniqueDiffWithinAt (p : Cell0Point) : UniqueDiffWithinAt ℝ (cellDomain 0) p.val :=
  cell0_domain_uniqueDiffOn p.val p.property

def cell0_actualParameterTime (p : Cell0Point) : Time := ⟨p.val 2, p.property.2.2⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
