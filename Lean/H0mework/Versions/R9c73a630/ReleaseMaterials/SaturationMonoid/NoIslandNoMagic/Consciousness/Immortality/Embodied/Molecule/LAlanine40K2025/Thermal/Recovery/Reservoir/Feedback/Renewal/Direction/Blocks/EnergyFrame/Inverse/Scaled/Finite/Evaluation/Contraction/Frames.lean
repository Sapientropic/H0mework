import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.PairFiber

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open Propagation.Interface Load.Source
noncomputable section

abbrev OrdinaryFull := ((((Fin 2 × Fin 2) × Fin 2) ⊕ ((Fin 2 × Fin 2) × Fin 2)) × Fin 2)
abbrev DiagonalFull := (((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) × Fin 2)
abbrev DonorFull := (Fin 2 × Fin 2) × Fin 2

def fullFiberEquiv (k : Sym2 Basis) :
    PairFiber.Sector pcOrbit k (pcOrbit Supply.donorIndex) × Fin 2 ≃ FullFiber k where
  toFun p := ⟨(p.1.val,p.2),p.1.property⟩
  invFun p := (⟨p.val.1,p.property⟩,p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

def pointerFiberEquiv (k : Sym2 Basis) : FullFiber k ⊕ FullFiber k ≃ PointerFiber k where
  toFun
    | .inl p => ⟨.inl p.val,p.property⟩
    | .inr p => ⟨.inr p.val,p.property⟩
  invFun
    | ⟨.inl p,h⟩ => .inl ⟨p,h⟩
    | ⟨.inr p,h⟩ => .inr ⟨p,h⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨p,h⟩; cases p <;> rfl

theorem ordinary_ne_donor (a b : Basis) (distinct : a ≠ b) : s(a,b)≠pcOrbit Supply.donorIndex := by
  intro same
  change s(a,b)=s((97 : Basis),97) at same
  rcases Sym2.eq_iff.mp same with h | h <;> exact distinct (h.1.trans h.2.symm)

theorem diagonal_ne_donor (a : Basis) (different : a ≠ 97) : s(a,a)≠pcOrbit Supply.donorIndex := by
  intro same
  change s(a,a)=s((97 : Basis),97) at same
  rcases Sym2.eq_iff.mp same with h | h <;> exact different h.1

def ordinaryFullEquiv (a b : Basis) (distinct : a ≠ b) : OrdinaryFull ≃ FullFiber s(a,b) :=
  let pair := Equiv.prodCongr (offDiagonalEquiv a b distinct) (diagonalEquiv (97 : Basis))
  (Equiv.prodCongr (Equiv.sumCongr pair pair) (Equiv.refl (Fin 2))).trans
    ((Equiv.prodCongr (PairFiber.offDiagonal pcOrbit s(a,b) (pcOrbit Supply.donorIndex)
      (ordinary_ne_donor a b distinct)) (Equiv.refl (Fin 2))).trans (fullFiberEquiv s(a,b)))

def diagonalFullEquiv (a : Basis) (different : a ≠ 97) : DiagonalFull ≃ FullFiber s(a,a) :=
  let pair := Equiv.prodCongr (diagonalEquiv a) (diagonalEquiv (97 : Basis))
  (Equiv.prodCongr (Equiv.sumCongr pair pair) (Equiv.refl (Fin 2))).trans
    ((Equiv.prodCongr (PairFiber.offDiagonal pcOrbit s(a,a) (pcOrbit Supply.donorIndex)
      (diagonal_ne_donor a different)) (Equiv.refl (Fin 2))).trans (fullFiberEquiv s(a,a)))

def donorFullEquiv : DonorFull ≃ FullFiber s((97 : Basis),97) :=
  (Equiv.prodCongr (Equiv.prodCongr (diagonalEquiv (97 : Basis)) (diagonalEquiv (97 : Basis)))
    (Equiv.refl (Fin 2))).trans
      ((Equiv.prodCongr (PairFiber.diagonal pcOrbit s((97 : Basis),97)) (Equiv.refl (Fin 2))).trans
        (fullFiberEquiv s((97 : Basis),97)))

def ordinaryPointerEquiv (a b : Basis) (distinct : a ≠ b) :
    OrdinaryFull ⊕ OrdinaryFull ≃ PointerFiber s(a,b) :=
  (Equiv.sumCongr (ordinaryFullEquiv a b distinct) (ordinaryFullEquiv a b distinct)).trans (pointerFiberEquiv s(a,b))

def diagonalPointerEquiv (a : Basis) (different : a ≠ 97) :
    DiagonalFull ⊕ DiagonalFull ≃ PointerFiber s(a,a) :=
  (Equiv.sumCongr (diagonalFullEquiv a different) (diagonalFullEquiv a different)).trans (pointerFiberEquiv s(a,a))

def donorPointerEquiv : DonorFull ⊕ DonorFull ≃ PointerFiber s((97 : Basis),97) :=
  (Equiv.sumCongr donorFullEquiv donorFullEquiv).trans (pointerFiberEquiv s((97 : Basis),97))

theorem source_full_dimensions : Fintype.card OrdinaryFull=32 ∧ Fintype.card DiagonalFull=16 ∧ Fintype.card DonorFull=8 := by
  norm_num [OrdinaryFull,DiagonalFull,DonorFull]

theorem source_pointer_dimensions : Fintype.card (OrdinaryFull ⊕ OrdinaryFull)=64 ∧
    Fintype.card (DiagonalFull ⊕ DiagonalFull)=32 ∧ Fintype.card (DonorFull ⊕ DonorFull)=16 := by
  norm_num [OrdinaryFull,DiagonalFull,DonorFull]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
