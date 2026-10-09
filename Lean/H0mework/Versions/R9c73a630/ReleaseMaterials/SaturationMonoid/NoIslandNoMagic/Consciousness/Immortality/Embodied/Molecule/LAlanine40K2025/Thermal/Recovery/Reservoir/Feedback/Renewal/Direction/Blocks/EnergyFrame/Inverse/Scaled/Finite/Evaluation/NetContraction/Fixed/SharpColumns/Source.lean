import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Embedding
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPulses.Consumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
theorem source_first_pointer_address_injective :
    Function.Injective (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide)) := by
  intro i j h
  apply (coordinatePointer (s((0 : Basis),1))
    (ordinaryFullEquiv (0 : Basis) 1 (by decide))).injective
  apply Subtype.val_injective
  exact h

theorem source_ordinary_injection_injective : Function.Injective ordinaryInjection := by
  intro i j h
  rcases i with ⟨p,e⟩
  rcases j with ⟨q,f⟩
  simp only [ordinaryInjection,Prod.mk.injEq,Sum.inl.injEq] at h
  rcases h with ⟨⟨hp,_⟩,he⟩
  exact Prod.ext hp he

theorem source_first_pointer_columns_norm_sharp :
    ‖qvalue ((ordinaryPointerQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id Sum.inl)‖ ≤ (2001/1000 : ℝ) := by
  rw [qvalue_submatrix,← ordinary_pointer_source,qvalue_submatrix,Spec.pointer_value]
  change ‖PCExecution.pointer.submatrix
    (ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide))
    (fun j => ordinaryPointerAddress (0 : Basis) (1 : Basis) (by decide) (.inl j))‖ ≤ _
  have left := source_first_pointer_address_injective
  have right : Function.Injective
      (fun j : OrdinaryFull => ordinaryPointerAddress (0 : Basis) (1 : Basis)
        (by decide) (.inl j)) := by
    intro i j h
    exact Sum.inl_injective (left h)
  exact (submatrix_norm_le PCExecution.pointer _ _ left right).trans
    source_pointer_norm_sharp

theorem source_first_supply_charged_norm_sharp :
    ‖qvalue ((ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)).submatrix
      id ordinaryInjection)‖ ≤ (2001/1000 : ℝ) := by
  rw [qvalue_submatrix,ordinary_supply_value]
  change ‖PCExecution.supply.submatrix
    (fun i => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide) i).val)
    (fun j => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide)
      (ordinaryInjection j)).val)‖ ≤ _
  have left : Function.Injective
      (fun i : OrdinaryFull => (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide) i).val) := by
    intro i j h
    apply (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide)).injective
    exact Subtype.val_injective h
  have right : Function.Injective
      (fun j : LoadPrimitive.NativeIndex =>
        (ordinaryFullEquiv (0 : Basis) (1 : Basis) (by decide)
          (ordinaryInjection j)).val) := by
    intro i j h
    exact source_ordinary_injection_injective (left h)
  exact (submatrix_norm_le PCExecution.supply _ _ left right).trans
    source_supply_norm_sharp
end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
