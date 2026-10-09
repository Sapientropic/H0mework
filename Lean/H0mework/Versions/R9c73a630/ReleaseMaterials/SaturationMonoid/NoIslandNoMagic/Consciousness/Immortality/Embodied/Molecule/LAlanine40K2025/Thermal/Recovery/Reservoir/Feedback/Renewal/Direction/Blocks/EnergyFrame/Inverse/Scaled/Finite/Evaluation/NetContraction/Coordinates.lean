import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Injection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
variable {β δ : Type*} [Fintype β] [Fintype δ]

def coordinatePointer (k : Sym2 Basis) (e : δ ≃ FullFiber k) : δ ⊕ δ ≃ PointerFiber k :=
  (Equiv.sumCongr e e).trans (pointerFiberEquiv k)

def coordinateNet (k : Sym2 Basis) (e : δ ≃ FullFiber k) : Matrix (δ ⊕ δ) (δ ⊕ δ) ℂ :=
  let p := coordinatePointer k e
  let pc := (localPC k).submatrix p p
  let nine := (localNine k).submatrix p p
  let eleven := (localEleven k).submatrix p p
  star eleven*pc*eleven-star nine*pc*nine

def coordinateRootNet (k : Sym2 Basis) (e : δ ≃ FullFiber k) : Matrix (δ ⊕ δ) (δ ⊕ δ) ℂ :=
  let p := coordinatePointer k e
  let root := (localPointer k).submatrix p p
  star root*coordinateNet k e*root

def coordinateReadout (k : Sym2 Basis) (e : δ ≃ FullFiber k) (insert : β → δ) : Matrix β β ℂ :=
  let supply := (localSupply k).submatrix e e
  (star supply*(coordinateRootNet k e).submatrix Sum.inl Sum.inl*supply).submatrix insert insert

def coordinateBody (k : Sym2 Basis) (e : β ≃ BodyFiber k) : Matrix β β ℂ :=
  let word := (localReceivedWord k).submatrix e e
  word*(localBodyInput k).submatrix e e*star word

private theorem reindex_pullback {ι ν : Type*} [Fintype ι] [Fintype ν] (e : ν ≃ ι) (A O : Matrix ι ι ℂ) :
    (star A*O*A).submatrix e e=star (A.submatrix e e)*O.submatrix e e*A.submatrix e e := by
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,← Matrix.submatrix_mul_equiv _ _ e e e]
  rfl

private theorem reindex_forward {ι ν : Type*} [Fintype ι] [Fintype ν] (e : ν ≃ ι) (A O : Matrix ι ι ℂ) :
    (A*O*star A).submatrix e e=A.submatrix e e*O.submatrix e e*star (A.submatrix e e) := by
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,← Matrix.submatrix_mul_equiv _ _ e e e]
  rfl

theorem coordinate_net_exact (k : Sym2 Basis) (e : δ ≃ FullFiber k) :
    (localNet k).submatrix (coordinatePointer k e) (coordinatePointer k e)=coordinateNet k e := by
  rw [localNet,Matrix.submatrix_sub]
  simp only [Pi.sub_apply]
  rw [reindex_pullback,reindex_pullback]
  rfl

theorem coordinate_root_net_exact (k : Sym2 Basis) (e : δ ≃ FullFiber k) :
    (localRootNet k).submatrix (coordinatePointer k e) (coordinatePointer k e)=coordinateRootNet k e := by
  rw [localRootNet,reindex_pullback,coordinate_net_exact]
  rfl

omit [Fintype δ] in
theorem coordinate_corner_exact (k : Sym2 Basis) (e : δ ≃ FullFiber k) (A : Matrix (PointerFiber k) (PointerFiber k) ℂ) :
    (A.submatrix (insertPointer k) (insertPointer k)).submatrix e e=
      (A.submatrix (coordinatePointer k e) (coordinatePointer k e)).submatrix Sum.inl Sum.inl := rfl

private theorem reindex_injection {ι η ν σ : Type*} (M : Matrix ι ι ℂ)
    (inject : η → ι) (body : σ → η) (full : ν → ι) (insert : σ → ν)
    (incidence : ∀ i, full (insert i)=inject (body i)) :
    (M.submatrix inject inject).submatrix body body=(M.submatrix full full).submatrix insert insert := by
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [incidence i,incidence j]

omit [Fintype β] in
theorem coordinate_readout_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) :
    (localReadout k).submatrix body body=coordinateReadout k full insert := by
  have same : (localReadout k).submatrix body body=
      ((star (localSupply k)*(localRootNet k).submatrix (insertPointer k) (insertPointer k)*localSupply k).submatrix
        full full).submatrix insert insert :=
    reindex_injection _ (insertDonor k) body full insert incidence

  rw [same,reindex_pullback,coordinate_corner_exact,coordinate_root_net_exact]
  rfl

theorem coordinate_body_exact (k : Sym2 Basis) (e : β ≃ BodyFiber k) :
    (localBody k).submatrix e e=coordinateBody k e :=
  reindex_forward e (localReceivedWord k) (localBodyInput k)

def coordinateEnergy (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k) (insert : β → δ) : ℝ :=
  Collision.energy (coordinateReadout k full insert) (coordinateBody k body)

theorem coordinate_energy_exact (k : Sym2 Basis) (body : β ≃ BodyFiber k) (full : δ ≃ FullFiber k)
    (insert : β → δ) (incidence : ∀ i, full (insert i)=insertDonor k (body i)) :
    programEnergy k=coordinateEnergy k body full insert := by
  rw [programEnergy,← Input.reindex_energy body,coordinate_readout_exact k body full insert incidence,coordinate_body_exact]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
