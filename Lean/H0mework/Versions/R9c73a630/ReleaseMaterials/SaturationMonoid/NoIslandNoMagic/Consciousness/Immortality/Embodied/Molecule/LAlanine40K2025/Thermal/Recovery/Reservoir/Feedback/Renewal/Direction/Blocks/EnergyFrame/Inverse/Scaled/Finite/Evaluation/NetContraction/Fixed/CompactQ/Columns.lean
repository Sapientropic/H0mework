import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.BlockProgram
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Compact

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Powered.Dynamics
open scoped Matrix BigOperators
noncomputable section
variable {β δ : Type*} [Fintype δ]

def sourceColumnsQ (k : Sym2 Basis) (full : δ ≃ FullFiber k) (insert : β → δ) :
    MatrixQ (δ ⊕ δ) β :=
  let p := coordinatePointer k full
  qmultiply
    ((pointerBlockQ k).submatrix p (fun i => p (.inl i)))
    ((supplyBlockQ k).submatrix full (fun i => full (insert i)))

theorem source_columns_value (k : Sym2 Basis) (full : δ ≃ FullFiber k) (insert : β → δ) :
    qvalue (sourceColumnsQ k full insert)=sourceColumns k full insert := by
  simp only [sourceColumnsQ,qvalue_multiply,qvalue_submatrix,
    pointerBlockQ_value,supplyBlockQ_value]
  rfl

def coordinateLoadQ (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    MatrixQ (δ ⊕ δ) (δ ⊕ δ) :=
  (Spec.pointerLoad).submatrix (Subtype.val ∘ coordinatePointer k full)
    (Subtype.val ∘ coordinatePointer k full)

def coordinateSupplyQ (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    MatrixQ (δ ⊕ δ) (δ ⊕ δ) :=
  (Spec.pointerSupply).submatrix (Subtype.val ∘ coordinatePointer k full)
    (Subtype.val ∘ coordinatePointer k full)

def coordinateWeakQ (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    MatrixQ (δ ⊕ δ) (δ ⊕ δ) :=
  (Spec.pointerWeak).submatrix (Subtype.val ∘ coordinatePointer k full)
    (Subtype.val ∘ coordinatePointer k full)

def coordinatePCQ (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    MatrixQ (δ ⊕ δ) (δ ⊕ δ) :=
  (Spec.pcObservable).submatrix (Subtype.val ∘ coordinatePointer k full)
    (Subtype.val ∘ coordinatePointer k full)

omit [Fintype δ] in
theorem coordinate_load_value (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    qvalue (coordinateLoadQ k full)=coordinateLoad k full := by
  rw [coordinateLoadQ,qvalue_submatrix,Spec.pointerLoad_value]
  rfl

omit [Fintype δ] in
theorem coordinate_supply_value (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    qvalue (coordinateSupplyQ k full)=coordinateSupply k full := by
  rw [coordinateSupplyQ,qvalue_submatrix,Spec.pointerSupply_value]
  rfl

omit [Fintype δ] in
theorem coordinate_weak_value (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    qvalue (coordinateWeakQ k full)=coordinateWeak k full := by
  rw [coordinateWeakQ,qvalue_submatrix,Spec.pointerWeak_value]
  rfl

omit [Fintype δ] in
theorem coordinate_pc_value (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    qvalue (coordinatePCQ k full)=(localPC k).submatrix (coordinatePointer k full)
      (coordinatePointer k full) := by
  rw [coordinatePCQ,qvalue_submatrix,Spec.pcObservable_value]
  rfl

variable [Fintype β]

def entranceColumnsQ (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) : MatrixQ (δ ⊕ δ) β :=
  qmultiply (sourceColumnsQ k full insert)
    ((receivedBlockQ k).submatrix body body)

theorem entrance_columns_value (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) :
    qvalue (entranceColumnsQ k body full insert)=entranceColumns k body full insert := by
  rw [entranceColumnsQ,qvalue_multiply,source_columns_value,qvalue_submatrix,receivedBlockQ_value]
  rfl

def nineColumnsQ (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) : MatrixQ (δ ⊕ δ) β :=
  qmultiply (coordinateLoadQ k full)
    (qmultiply (coordinateSupplyQ k full)
      (qmultiply (coordinateSupplyQ k full) (entranceColumnsQ k body full insert)))

theorem nine_columns_value (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) :
    qvalue (nineColumnsQ k body full insert)=nineColumns k body full insert := by
  simp only [nineColumnsQ,qvalue_multiply,coordinate_load_value,
    coordinate_supply_value,entrance_columns_value]
  rfl

def elevenColumnsQ (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) : MatrixQ (δ ⊕ δ) β :=
  qmultiply (coordinateLoadQ k full)
    (qmultiply (coordinateWeakQ k full) (nineColumnsQ k body full insert))

theorem eleven_columns_value (k : Sym2 Basis) (body : β ≃ BodyFiber k)
    (full : δ ≃ FullFiber k) (insert : β → δ) :
    qvalue (elevenColumnsQ k body full insert)=elevenColumns k body full insert := by
  simp only [elevenColumnsQ,qvalue_multiply,coordinate_load_value,
    coordinate_weak_value,nine_columns_value]
  rfl


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
