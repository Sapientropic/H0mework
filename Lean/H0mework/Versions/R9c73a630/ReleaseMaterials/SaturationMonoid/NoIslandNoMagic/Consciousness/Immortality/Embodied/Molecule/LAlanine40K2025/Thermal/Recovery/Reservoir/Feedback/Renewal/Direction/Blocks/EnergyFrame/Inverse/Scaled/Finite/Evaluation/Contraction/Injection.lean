import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Frames

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source
noncomputable section

def ordinaryInjection (i : (Fin 2 × Fin 2) × Fin 2) : OrdinaryFull := (.inl (i.1,1),i.2)
def diagonalInjection (i : Fin 2 × Fin 2) : DiagonalFull := (.inl (i.1,1),i.2)
def donorInjection (i : Fin 2 × Fin 2) : DonorFull := ((i.1,1),i.2)

theorem ordinary_donor_injection (a b : Basis) (distinct : a ≠ b) (i : (Fin 2 × Fin 2) × Fin 2) :
    ordinaryFullEquiv a b distinct (ordinaryInjection i)=
      insertDonor s(a,b) (Scaled.Order.offDiagonalPCEEquiv a b distinct i) := rfl

theorem diagonal_donor_injection (a : Basis) (different : a ≠ 97) (i : Fin 2 × Fin 2) :
    diagonalFullEquiv a different (diagonalInjection i)=insertDonor s(a,a) (Scaled.Order.diagonalPCEEquiv a i) := rfl

theorem donor_donor_injection (i : Fin 2 × Fin 2) :
    donorFullEquiv (donorInjection i)=insertDonor s((97 : Basis),97) (Scaled.Order.diagonalPCEEquiv 97 i) := rfl

theorem ordinary_pointer_injection (a b : Basis) (distinct : a ≠ b) (i : OrdinaryFull) :
    ordinaryPointerEquiv a b distinct (Sum.inl i)=insertPointer s(a,b) (ordinaryFullEquiv a b distinct i) := rfl

theorem diagonal_pointer_injection (a : Basis) (different : a ≠ 97) (i : DiagonalFull) :
    diagonalPointerEquiv a different (Sum.inl i)=insertPointer s(a,a) (diagonalFullEquiv a different i) := rfl

theorem donor_pointer_injection (i : DonorFull) :
    donorPointerEquiv (Sum.inl i)=insertPointer s((97 : Basis),97) (donorFullEquiv i) := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
