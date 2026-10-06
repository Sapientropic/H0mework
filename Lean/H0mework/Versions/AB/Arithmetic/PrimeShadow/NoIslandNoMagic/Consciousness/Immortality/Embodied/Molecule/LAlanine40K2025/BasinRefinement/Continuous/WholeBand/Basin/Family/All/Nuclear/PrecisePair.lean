import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PreciseWholeSpace
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Repulsion

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.PreciseTarget
open SourceFiniteData SourceCoulomb
open scoped BigOperators
noncomputable section

def nuclearRepulsion (a b : Fin 13) : ℝ :=
  Nuclear.nuclearCharge a * Nuclear.nuclearCharge b *
    kernel (centre a - centre b)

def totalRepulsion : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun p => p.1 < p.2),
    nuclearRepulsion p.1 p.2

theorem nuclear_repulsion_symmetric (a b : Fin 13) :
    nuclearRepulsion a b = nuclearRepulsion b a := by
  unfold nuclearRepulsion
  rw [show Nuclear.nuclearCharge a * Nuclear.nuclearCharge b =
      Nuclear.nuclearCharge b * Nuclear.nuclearCharge a from mul_comm _ _]
  congr 1
  unfold SourceCoulomb.kernel SourceCoulomb.distance
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show (centre b - centre a) k =
      -((centre a - centre b) k) from by
    rw [Pi.sub_apply,Pi.sub_apply,neg_sub]]
  rw [neg_sq]

def coordinateRepulsionResidual : ℝ := totalRepulsion - Nuclear.totalRepulsion

theorem total_repulsion_coordinates :
    totalRepulsion = Nuclear.totalRepulsion + coordinateRepulsionResidual := by
  unfold coordinateRepulsionResidual
  ring

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.PreciseTarget
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
