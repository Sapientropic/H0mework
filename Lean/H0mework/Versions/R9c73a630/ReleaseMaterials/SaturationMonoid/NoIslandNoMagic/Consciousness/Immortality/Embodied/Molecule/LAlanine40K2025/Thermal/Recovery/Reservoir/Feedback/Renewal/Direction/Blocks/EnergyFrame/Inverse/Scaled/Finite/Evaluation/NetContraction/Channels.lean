import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.PulseFactors
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Injection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
variable {β δ : Type*} [Fintype β] [Fintype δ]

def sourceColumns (k : Sym2 Basis) (e : δ ≃ FullFiber k) (insert : β → δ) : Matrix (δ ⊕ δ) β ℂ :=
  let p := coordinatePointer k e
  let root := (localPointer k).submatrix p p
  let supply := (localSupply k).submatrix e e
  root.submatrix id Sum.inl*supply.submatrix id insert

def entranceColumns (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    Matrix (δ ⊕ δ) β ℂ := sourceColumns k full insert*(localReceivedWord k).submatrix body body

def nineColumns (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    Matrix (δ ⊕ δ) β ℂ :=
  coordinateLoad k full*(coordinateSupply k full*(coordinateSupply k full*entranceColumns k body full insert))

def elevenColumns (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    Matrix (δ ⊕ δ) β ℂ :=
  coordinateLoad k full*(coordinateWeak k full*nineColumns k body full insert)

private theorem nine_columns_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    (localNine k).submatrix (coordinatePointer k full) (coordinatePointer k full)*entranceColumns k body full insert=
      nineColumns k body full insert := by
  rw [coordinate_nine]
  simp only [nineColumns,Matrix.mul_assoc]

private theorem eleven_columns_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    (localEleven k).submatrix (coordinatePointer k full) (coordinatePointer k full)*entranceColumns k body full insert=
      elevenColumns k body full insert := by
  rw [coordinate_eleven]
  simp only [Matrix.mul_assoc,nine_columns_exact]
  rfl

def channelNet (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) : Matrix β β ℂ :=
  let p := coordinatePointer k full
  let pc := (localPC k).submatrix p p
  let nine := nineColumns k body full insert
  let eleven := elevenColumns k body full insert
  eleven.conjTranspose*pc*eleven-nine.conjTranspose*pc*nine

def channelEnergy (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) : ℝ :=
  Collision.energy (channelNet k body full insert) ((localBodyInput k).submatrix body body)

omit [Fintype β] in
theorem source_columns_exact (k : Sym2 Basis) (full : δ ≃ FullFiber k) (insert : β → δ) :
    coordinateReadout k full insert=(sourceColumns k full insert).conjTranspose*coordinateNet k full*sourceColumns k full insert := by
  unfold coordinateReadout coordinateRootNet sourceColumns
  rw [column_pullback,column_pullback]
  exact rectangular_pullback _ _ _

theorem entrance_columns_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    star ((localReceivedWord k).submatrix body body)*coordinateReadout k full insert*((localReceivedWord k).submatrix body body)=
      (entranceColumns k body full insert).conjTranspose*coordinateNet k full*entranceColumns k body full insert := by
  rw [source_columns_exact]
  exact rectangular_pullback _ _ _

theorem channel_net_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    (entranceColumns k body full insert).conjTranspose*coordinateNet k full*entranceColumns k body full insert=
      channelNet k body full insert := by
  unfold coordinateNet
  rw [rectangular_net,nine_columns_exact,eleven_columns_exact]
  rfl

theorem channel_energy_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) :
    coordinateEnergy k body full insert=channelEnergy k body full insert := by
  unfold coordinateEnergy coordinateBody
  rw [input_pullback,entrance_columns_exact,channel_net_exact]
  rfl

theorem original_channel_energy (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) :
    programEnergy k=channelEnergy k body full insert :=
  (coordinate_energy_exact k body full insert incidence).trans (channel_energy_exact k body full insert)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
