import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Addresses

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

variable {α β : Type*}

private theorem source_pc_kept : Preserves pcOrbit (qvalue computedPCQ) := by
  rw [computedPCQ_value]
  exact pc_preserves

private theorem source_load_kept : Preserves pceOrbit (qvalue computedLoadQ) := by
  rw [computedLoadQ_value]
  exact load_preserves

theorem source_supply_role (f : α → PairController) (g : β → PairController)
    (k l : Sym2 Basis) (different : k ≠ l) (fk : ∀ i, pcOrbit (f i)=k) (gl : ∀ i, pcOrbit (g i)=l) :
    Spec.supply.submatrix (roleAddress f g) (roleAddress f g)=
      roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (computedPCQ.submatrix f f) (computedPCQ.submatrix g g)) freeEnvironmentQ) := by
  rw [supply_entries_exact]
  exact mixing_role_restriction f g k l different fk gl computedPCQ freeEnvironmentQ
    SquareRoot.Full.cosine SquareRoot.Full.sine source_pc_kept

theorem source_weak_role (f : α → PairController) (g : β → PairController)
    (k l : Sym2 Basis) (different : k ≠ l) (fk : ∀ i, pcOrbit (f i)=k) (gl : ∀ i, pcOrbit (g i)=l) :
    Spec.weak.submatrix (roleAddress f g) (roleAddress f g)=
      roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
        (qkron (qkron (computedPCQ.submatrix f f) (computedPCQ.submatrix g g)) freeEnvironmentQ) := by
  rw [weak_entries_exact]
  exact mixing_role_restriction f g k l different fk gl computedPCQ freeEnvironmentQ
    SquareRoot.Full.sine SquareRoot.Full.cosine source_pc_kept

theorem source_load_role (f : α → PairController) (g : β → PairController)
    (k l : Sym2 Basis) (different : k ≠ l) (fk : ∀ i, pcOrbit (f i)=k) (gl : ∀ i, pcOrbit (g i)=l) :
    Spec.load.submatrix (roleAddress f g) (roleAddress f g)=
      roleBlocksQ
        (bodyLiftQ (computedLoadQ.submatrix (liftedAddress f) (liftedAddress f))
          (computedPCQ.submatrix g g))
        (donorLiftQ (computedLoadQ.submatrix (liftedAddress g) (liftedAddress g))
          (computedPCQ.submatrix f f)) := by
  rw [Spec.load]
  exact local_role_restriction f g k l different fk gl computedLoadQ computedPCQ source_load_kept

theorem ordinary_supply_restriction (a b : Basis) (ordered : a < b) :
    Spec.supply.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ) := by
  rw [ordinary_full_address]
  rw [source_supply_role (orbitPC a b) donorPCAddress s(a,b)
    (pcOrbit Supply.donorIndex) (ordinary_ne_donor a b ordered.ne)
    (ordinary_PC_label a b ordered.ne) donorPC_label]
  have donor : computedPCQ.submatrix donorPCAddress donorPCAddress=oneDiagonalQ 97 :=
    diagonal_pc_one_restriction 97
  rw [ordinary_pc_one_restriction,donor]

theorem ordinary_weak_restriction (a b : Basis) (ordered : a < b) :
    Spec.weak.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
        (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ) := by
  rw [ordinary_full_address]
  rw [source_weak_role (orbitPC a b) donorPCAddress s(a,b)
    (pcOrbit Supply.donorIndex) (ordinary_ne_donor a b ordered.ne)
    (ordinary_PC_label a b ordered.ne) donorPC_label]
  have donor : computedPCQ.submatrix donorPCAddress donorPCAddress=oneDiagonalQ 97 :=
    diagonal_pc_one_restriction 97
  rw [ordinary_pc_one_restriction,donor]

theorem diagonal_supply_restriction (a : Basis) (different : a ≠ 97) :
    Spec.supply.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val)=
      roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ) := by
  rw [diagonal_full_address]
  rw [source_supply_role (fun c => ((a,a),c)) donorPCAddress s(a,a)
    (pcOrbit Supply.donorIndex) (diagonal_ne_donor a different)
    (fun _ => rfl) donorPC_label]
  have donor : computedPCQ.submatrix donorPCAddress donorPCAddress=oneDiagonalQ 97 :=
    diagonal_pc_one_restriction 97
  rw [diagonal_pc_one_restriction,donor]

theorem diagonal_weak_restriction (a : Basis) (different : a ≠ 97) :
    Spec.weak.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val)=
      roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
        (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ) := by
  rw [diagonal_full_address]
  rw [source_weak_role (fun c => ((a,a),c)) donorPCAddress s(a,a)
    (pcOrbit Supply.donorIndex) (diagonal_ne_donor a different)
    (fun _ => rfl) donorPC_label]
  have donor : computedPCQ.submatrix donorPCAddress donorPCAddress=oneDiagonalQ 97 :=
    diagonal_pc_one_restriction 97
  rw [diagonal_pc_one_restriction,donor]

theorem ordinary_load_source (a b : Basis) (ordered : a < b) :
    Spec.load.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      roleBlocksQ
        (bodyLiftQ (ordinaryLoadQ a b ordered) (oneDiagonalQ 97))
        (donorLiftQ (diagonalLoadQ 97) (onePCQ a b ordered)) := by
  rw [ordinary_full_address]
  rw [source_load_role (orbitPC a b) donorPCAddress s(a,b)
    (pcOrbit Supply.donorIndex) (ordinary_ne_donor a b ordered.ne)
    (ordinary_PC_label a b ordered.ne) donorPC_label]
  have donorPC : computedPCQ.submatrix donorPCAddress donorPCAddress=oneDiagonalQ 97 :=
    diagonal_pc_one_restriction 97
  have donorLoad : computedLoadQ.submatrix (liftedAddress donorPCAddress)
      (liftedAddress donorPCAddress)=diagonalLoadQ 97 := diagonal_load_restriction 97
  rw [ordinary_lifted_address,ordinary_load_restriction,donorLoad,ordinary_pc_one_restriction,donorPC]

theorem diagonal_load_source (a : Basis) (different : a ≠ 97) :
    Spec.load.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val)=
      roleBlocksQ
        (bodyLiftQ (diagonalLoadQ a) (oneDiagonalQ 97))
        (donorLiftQ (diagonalLoadQ 97) (oneDiagonalQ a)) := by
  rw [diagonal_full_address]
  rw [source_load_role (fun c => ((a,a),c)) donorPCAddress s(a,a)
    (pcOrbit Supply.donorIndex) (diagonal_ne_donor a different)
    (fun _ => rfl) donorPC_label]
  have donorPC : computedPCQ.submatrix donorPCAddress donorPCAddress=oneDiagonalQ 97 :=
    diagonal_pc_one_restriction 97
  have donorLoad : computedLoadQ.submatrix (liftedAddress donorPCAddress)
      (liftedAddress donorPCAddress)=diagonalLoadQ 97 := diagonal_load_restriction 97
  rw [diagonal_lifted_address,diagonal_load_restriction,donorLoad,diagonal_pc_one_restriction,donorPC]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
