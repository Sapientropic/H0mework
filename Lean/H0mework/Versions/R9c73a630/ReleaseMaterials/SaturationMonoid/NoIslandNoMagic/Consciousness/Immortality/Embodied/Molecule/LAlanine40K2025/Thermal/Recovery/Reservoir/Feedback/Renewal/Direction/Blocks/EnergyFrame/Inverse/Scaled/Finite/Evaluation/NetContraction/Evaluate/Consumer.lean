import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Channels

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

theorem ordinary_local_supply_value (a b : Basis) (ordered : a < b) :
    (NetContraction.localSupply s(a,b)).submatrix (ordinaryFullEquiv a b ordered.ne)
      (ordinaryFullEquiv a b ordered.ne)=
      qvalue (roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ)) := by
  rw [← ordinary_supply_restriction,qvalue_submatrix,Spec.supply_value]
  rfl

theorem diagonal_local_supply_value (a : Basis) (different : a ≠ 97) :
    (NetContraction.localSupply s(a,a)).submatrix (diagonalFullEquiv a different)
      (diagonalFullEquiv a different)=
      qvalue (roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ)) := by
  rw [← diagonal_supply_restriction,qvalue_submatrix,Spec.supply_value]
  rfl

theorem ordinary_weak_value (a b : Basis) (ordered : a < b) :
    PCExecution.weak.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      qvalue (roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
        (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ)) := by
  rw [← ordinary_weak_restriction,qvalue_submatrix,Spec.weak_value]

theorem diagonal_weak_value (a : Basis) (different : a ≠ 97) :
    PCExecution.weak.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val)=
      qvalue (roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
        (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ)) := by
  rw [← diagonal_weak_restriction,qvalue_submatrix,Spec.weak_value]

theorem ordinary_load_value (a b : Basis) (ordered : a < b) :
    LoadExecution.load.submatrix (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
      (fun i => (ordinaryFullEquiv a b ordered.ne i).val)=
      qvalue (roleBlocksQ
        (bodyLiftQ (ordinaryLoadQ a b ordered) (oneDiagonalQ 97))
        (donorLiftQ (diagonalLoadQ 97) (onePCQ a b ordered))) := by
  rw [← ordinary_load_source,qvalue_submatrix,Spec.load_value]

theorem diagonal_load_value (a : Basis) (different : a ≠ 97) :
    LoadExecution.load.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val)=
      qvalue (roleBlocksQ
        (bodyLiftQ (diagonalLoadQ a) (oneDiagonalQ 97))
        (donorLiftQ (diagonalLoadQ 97) (oneDiagonalQ a))) := by
  rw [← diagonal_load_source,qvalue_submatrix,Spec.load_value]

theorem ordinary_source_columns (a b : Basis) (ordered : a < b) :
    NetContraction.sourceColumns s(a,b) (ordinaryFullEquiv a b ordered.ne) ordinaryInjection =
      ((NetContraction.localPointer s(a,b)).submatrix
        (NetContraction.coordinatePointer s(a,b) (ordinaryFullEquiv a b ordered.ne))
        (NetContraction.coordinatePointer s(a,b) (ordinaryFullEquiv a b ordered.ne))).submatrix id Sum.inl *
      (qvalue (roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (onePCQ a b ordered) (oneDiagonalQ 97)) freeEnvironmentQ))).submatrix id ordinaryInjection := by
  unfold NetContraction.sourceColumns
  rw [ordinary_local_supply_value]

theorem diagonal_source_columns (a : Basis) (different : a ≠ 97) :
    NetContraction.sourceColumns s(a,a) (diagonalFullEquiv a different) diagonalInjection =
      ((NetContraction.localPointer s(a,a)).submatrix
        (NetContraction.coordinatePointer s(a,a) (diagonalFullEquiv a different))
        (NetContraction.coordinatePointer s(a,a) (diagonalFullEquiv a different))).submatrix id Sum.inl *
      (qvalue (roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
        (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ))).submatrix id diagonalInjection := by
  unfold NetContraction.sourceColumns
  rw [diagonal_local_supply_value]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
