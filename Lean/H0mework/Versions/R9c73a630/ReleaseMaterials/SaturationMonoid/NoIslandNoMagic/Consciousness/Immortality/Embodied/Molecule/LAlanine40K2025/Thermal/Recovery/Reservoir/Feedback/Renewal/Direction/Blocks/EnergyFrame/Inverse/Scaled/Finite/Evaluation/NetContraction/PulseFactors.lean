import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Columns
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Injection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
variable {δ : Type*} [Fintype δ]

def coordinateLoad (k : Sym2 Basis) (full : δ ≃ FullFiber k) : Matrix (δ ⊕ δ) (δ ⊕ δ) ℂ :=
  let p := coordinatePointer k full
  (restrict Sectors.pointerOrbit (donorSector k) LoadExecution.pointerLoad).submatrix p p

def coordinateSupply (k : Sym2 Basis) (full : δ ≃ FullFiber k) : Matrix (δ ⊕ δ) (δ ⊕ δ) ℂ :=
  let p := coordinatePointer k full
  (restrict Sectors.pointerOrbit (donorSector k) LoadExecution.pointerSupply).submatrix p p

def coordinateWeak (k : Sym2 Basis) (full : δ ≃ FullFiber k) : Matrix (δ ⊕ δ) (δ ⊕ δ) ℂ :=
  let p := coordinatePointer k full
  (restrict Sectors.pointerOrbit (donorSector k) LoadExecution.pointerWeak).submatrix p p

theorem coordinate_nine (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    (localNine k).submatrix (coordinatePointer k full) (coordinatePointer k full)=
      coordinateLoad k full*coordinateSupply k full*coordinateSupply k full := by
  unfold localNine LoadExecution.nine
  rw [restrict_mul (preserves_mul pointer_load_preserves pointer_supply_preserves),restrict_mul pointer_load_preserves]
  rw [← Matrix.submatrix_mul_equiv _ _ (coordinatePointer k full) (coordinatePointer k full) (coordinatePointer k full),
    ← Matrix.submatrix_mul_equiv _ _ (coordinatePointer k full) (coordinatePointer k full) (coordinatePointer k full)]
  rfl

theorem coordinate_eleven (k : Sym2 Basis) (full : δ ≃ FullFiber k) :
    (localEleven k).submatrix (coordinatePointer k full) (coordinatePointer k full)=
      coordinateLoad k full*coordinateWeak k full*(localNine k).submatrix (coordinatePointer k full) (coordinatePointer k full) := by
  unfold localEleven LoadExecution.eleven
  rw [restrict_mul (preserves_mul pointer_load_preserves pointer_weak_preserves),restrict_mul pointer_load_preserves]
  rw [← Matrix.submatrix_mul_equiv _ _ (coordinatePointer k full) (coordinatePointer k full) (coordinatePointer k full),
    ← Matrix.submatrix_mul_equiv _ _ (coordinatePointer k full) (coordinatePointer k full) (coordinatePointer k full)]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
