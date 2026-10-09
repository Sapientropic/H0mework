import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformPointer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Source
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceOrdinarySupplyInt (a b : Basis) (ordered : a < b) :
    MatrixInt OrdinaryFull OrdinaryFull := quantize (ordinarySupplyQ a b ordered)

def sourceOrdinaryPointerColumnsInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) OrdinaryFull :=
  submatrix (sourceOrdinaryPointerInt a b ordered) id Sum.inl

def sourceOrdinarySupplyChargedInt (a b : Basis) (ordered : a < b) :
    MatrixInt OrdinaryFull LoadPrimitive.NativeIndex :=
  submatrix (sourceOrdinarySupplyInt a b ordered) id ordinaryInjection

def sourceOrdinaryColumnsInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex :=
  multiply (sourceOrdinaryPointerColumnsInt a b ordered)
    (sourceOrdinarySupplyChargedInt a b ordered)

theorem source_ordinary_pointer_address_injective (a b : Basis)
    (ordered : a < b) : Function.Injective (ordinaryPointerAddress a b ordered) := by
  intro i j h
  apply (coordinatePointer (s(a,b)) (ordinaryFullEquiv a b ordered.ne)).injective
  exact Subtype.val_injective h

theorem source_ordinary_pointer_columns_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue ((ordinaryPointerQ a b ordered).submatrix id Sum.inl)‖ ≤
      (2001/1000 : ℝ) := by
  rw [qvalue_submatrix,← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value]
  change ‖PCExecution.pointer.submatrix (ordinaryPointerAddress a b ordered)
    (fun j => ordinaryPointerAddress a b ordered (.inl j))‖ ≤ _
  have left := source_ordinary_pointer_address_injective a b ordered
  have right : Function.Injective
      (fun j : OrdinaryFull => ordinaryPointerAddress a b ordered (.inl j)) := by
    intro i j h
    exact Sum.inl_injective (left h)
  exact (submatrix_norm_le PCExecution.pointer _ _ left right).trans
    source_pointer_norm_sharp

theorem source_ordinary_supply_charged_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue ((ordinarySupplyQ a b ordered).submatrix id ordinaryInjection)‖ ≤
      (2001/1000 : ℝ) := by
  rw [qvalue_submatrix,ordinary_supply_value]
  change ‖PCExecution.supply.submatrix
    (fun i => (ordinaryFullEquiv a b ordered.ne i).val)
    (fun j => (ordinaryFullEquiv a b ordered.ne (ordinaryInjection j)).val)‖ ≤ _
  have left : Function.Injective
      (fun i : OrdinaryFull => (ordinaryFullEquiv a b ordered.ne i).val) := by
    intro i j h
    apply (ordinaryFullEquiv a b ordered.ne).injective
    exact Subtype.val_injective h
  have right : Function.Injective
      (fun j : LoadPrimitive.NativeIndex =>
        (ordinaryFullEquiv a b ordered.ne (ordinaryInjection j)).val) := by
    intro i j h
    exact source_ordinary_injection_injective (left h)
  exact (submatrix_norm_le PCExecution.supply _ _ left right).trans
    source_supply_norm_sharp

theorem source_first_columns_same :
    sourceOrdinaryColumnsInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstColumnsInt := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
