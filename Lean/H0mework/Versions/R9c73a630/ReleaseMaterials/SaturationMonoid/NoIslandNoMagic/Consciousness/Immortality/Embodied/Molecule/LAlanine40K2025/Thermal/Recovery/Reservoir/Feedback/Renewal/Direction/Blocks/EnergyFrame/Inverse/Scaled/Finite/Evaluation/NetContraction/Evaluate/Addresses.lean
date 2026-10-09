import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Local
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Mixing
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Rotated

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

def donorPCAddress (c : Fin 2) : PairController := ((97,97),c)

theorem donorPC_label (c : Fin 2) : pcOrbit (donorPCAddress c)=pcOrbit Supply.donorIndex := rfl

theorem ordinary_PC_label (a b : Basis) (distinct : a ≠ b) (i : Fin 2 × Fin 2) : pcOrbit (orbitPC a b i)=s(a,b) :=
  (offDiagonalEquiv a b distinct i).property

theorem diagonal_PC_label (a : Basis) (c : Fin 2) : pcOrbit ((a,a),c)=s(a,a) := rfl

theorem ordinary_full_address (a b : Basis) (distinct : a ≠ b) :
    (fun i => (ordinaryFullEquiv a b distinct i).val)=roleAddress (orbitPC a b) donorPCAddress := by
  funext ⟨i,e⟩
  cases i <;> rfl

theorem diagonal_full_address (a : Basis) (different : a ≠ 97) :
    (fun i => (diagonalFullEquiv a different i).val)=roleAddress (fun c => ((a,a),c)) donorPCAddress := by
  funext ⟨i,e⟩
  cases i <;> rfl

theorem donor_full_address :
    (fun i => (donorFullEquiv i).val)=(fun i : Leg (Fin 2) (Fin 2) => ((donorPCAddress i.1.1,donorPCAddress i.1.2),i.2)) := rfl

theorem ordinary_lifted_address (a b : Basis) : liftedAddress (orbitPC a b)=Scaled.Order.orbitPCE a b := rfl

theorem diagonal_lifted_address (a : Basis) : liftedAddress (fun c => ((a,a),c))=Scaled.Order.diagonalPCE a := rfl

theorem donor_lifted_address : liftedAddress donorPCAddress=Scaled.Order.diagonalPCE 97 := rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
