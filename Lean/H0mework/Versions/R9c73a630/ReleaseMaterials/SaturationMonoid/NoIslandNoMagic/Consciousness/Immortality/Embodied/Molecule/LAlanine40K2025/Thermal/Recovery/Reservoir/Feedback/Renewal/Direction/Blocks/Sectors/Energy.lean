import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Contraction

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
open Collision Propagation.Interface Load.Source
open scoped Matrix ComplexOrder BigOperators
noncomputable section

local instance : Fintype (Sym2 (Sym2 Basis)) := Fintype.ofFinite _

attribute [local irreducible] Weak.origin Weak.execution

def pcObservable : Current.FullJoint := Matrix.kronecker
  (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix PairController PairController ℂ))
  (1 : Matrix (Fin 2) (Fin 2) ℂ)
def pointerPCObservable : PointerJoint := Matrix.fromBlocks pcObservable 0 0 pcObservable

theorem pcObservable_preserves : Preserves reservoirOrbit pcObservable := by
  have pair := preserves_relabel (preserves_tensor source_hpc_preserves (preserves_one pcOrbit))
    (fun k : Sym2 Basis × Sym2 Basis => s(k.1,k.2))
  exact preserves_tensor_left pair (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem pointerPCObservable_preserves : Preserves pointerOrbit pointerPCObservable :=
  fromBlocks_preserves _ _ _ _ pcObservable_preserves (preserves_zero _) (preserves_zero _) pcObservable_preserves

private theorem tensor_left_energy {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι ι ℂ)
    (rho : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    energy (Matrix.kronecker (Matrix.kronecker H (1 : Matrix ι ι ℂ)) (1 : Matrix κ κ ℂ)) rho =
      energy H (Collision.systemReduce (Powered.Dynamics.systemReduce rho)) := by
  have outer := Powered.Dynamics.jointEnergy_real_eq_reduced
    (Matrix.kronecker H (1 : Matrix ι ι ℂ)) (0 : Matrix κ κ ℂ) rho
  have first : energy (Matrix.kronecker (Matrix.kronecker H (1 : Matrix ι ι ℂ)) (1 : Matrix κ κ ℂ)) rho =
      energy (Matrix.kronecker H (1 : Matrix ι ι ℂ)) (Powered.Dynamics.systemReduce rho) := by
    simpa [energy,Matrix.kronecker] using outer
  rw [first, Exchange.left_energy]

theorem pcObservable_energy (rho : Current.FullJoint) :
    energy pcObservable rho = Resource.pcEnergyOf rho := tensor_left_energy _ rho

theorem pointerPCObservable_energy (rho : PointerJoint) :
    energy pointerPCObservable rho = Resource.pcEnergyOf (bodyRead rho) := by
  have split := block_energy_split pcObservable 0 rho
  simp only [Complex.ofReal_zero, zero_smul, add_zero, zero_mul] at split
  exact split.trans (pcObservable_energy _)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
