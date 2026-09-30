import H0mework.Chemistry.LAlanineTrueTube.ChecksIncidence
import H0mework.Chemistry.LAlanineWholeCell.ReplayInitial

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeChecks
open WholeCellPartition ContinuousParameterMap Set
noncomputable section

theorem actual_seed_initial (d : Direction) (p : Point) (inside : p ∈ fullDomain) :
    InRectangle (initialBox d 0) (initialMap 0 4 p) := by
  rw [first_initial_eq]
  exact (WholeCellReplay.full_initial_jet p inside).1

theorem source_corner_inside : fullLower ∈ fullDomain := by
  constructor
  · exact le_rfl
  · intro i
    exact Rat.cast_le.mpr (full_ordered i).le

theorem actual_initial_nonempty (d : Direction) :
    ∃ x : Point, InRectangle (initialBox d 0) x :=
  ⟨initialMap 0 4 fullLower, actual_seed_initial d fullLower source_corner_inside⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
