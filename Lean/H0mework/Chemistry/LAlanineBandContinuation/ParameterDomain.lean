import H0mework.Chemistry.LAlanineBandContinuation.ParameterSeed
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandSource WholeBandGeometry Set
noncomputable section

def cellLower (c : FullBandCell) : Point := ![0, (cellV c 0 : ℝ), -(1/2)]
def cellUpper (c : FullBandCell) : Point := ![1, (cellV c 1 : ℝ), 1/2]

theorem domain_eq_Icc (c : FullBandCell) : cellDomain c = Icc (cellLower c) (cellUpper c) := by
  ext p
  change (p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (cellV c 0 : ℝ) (cellV c 1) ∧
    p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)) ↔ (∀ i, cellLower c i ≤ p i) ∧ (∀ i, p i ≤ cellUpper c i)
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

theorem axis_strict (c : FullBandCell) (j : Fin 3) : cellLower c j < cellUpper c j := by
  fin_cases j
  · norm_num [cellLower, cellUpper]
  · exact Rat.cast_lt.mpr (source_cells_in_segments c).2.1
  · norm_num [cellLower, cellUpper]

theorem coordinate_mem (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) (j : Fin 3) :
    p j ∈ Icc (cellLower c j) (cellUpper c j) := by
  have h : p ∈ Icc (cellLower c) (cellUpper c) := domain_eq_Icc c ▸ inside
  exact ⟨h.1 j, h.2 j⟩

theorem line_inside (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) (j : Fin 3) :
    MapsTo (Function.update p j) (Icc (cellLower c j) (cellUpper c j)) (cellDomain c) := by
  have h : p ∈ Icc (cellLower c) (cellUpper c) := domain_eq_Icc c ▸ inside
  intro r hr
  apply (domain_eq_Icc c).symm.subset
  constructor <;> intro i <;> by_cases hi : i = j
  · subst i
    simpa using hr.1
  · simpa only [Function.update_of_ne hi] using h.1 i
  · subst i
    simpa using hr.2
  · simpa only [Function.update_of_ne hi] using h.2 i

theorem domain_interior_nonempty (c : FullBandCell) : (interior (cellDomain c)).Nonempty := by
  rw [domain_eq_Icc, ← pi_univ_Icc, interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]
  refine ⟨fun i => (cellLower c i + cellUpper c i) / 2, ?_⟩
  intro i _
  have ordered := axis_strict c i
  constructor <;> dsimp only <;> linarith

theorem domain_uniqueDiffOn (c : FullBandCell) : UniqueDiffOn ℝ (cellDomain c) :=
  uniqueDiffOn_convex ((domain_eq_Icc c).symm ▸ convex_Icc (cellLower c) (cellUpper c))
    (domain_interior_nonempty c)

theorem uniqueDiffWithinAt (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) :
    UniqueDiffWithinAt ℝ (cellDomain c) p :=
  domain_uniqueDiffOn c p inside

def actualParameterTime (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) : Time := ⟨p 2, inside.2.2⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
