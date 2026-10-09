import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Small
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Observable

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem sorted_source (a b : Basis) (ordered : a ≤ b) :
    Sym2.sortEquiv s(a,b)=⟨(a,b),ordered⟩ := Sym2.sortEquiv.apply_symm_apply ⟨(a,b),ordered⟩

attribute [local irreducible] Primitive.ordinaryFiberMaterial Primitive.diagonalFiberMaterial
  Primitive.allOrdinary Primitive.allDiagonal LoadPrimitive.ordinaryFiber LoadPrimitive.diagonalFiber
  LoadPrimitive.allOrdinary LoadDiagonal.allDiagonal

private def orderedPC (p : {p : Basis × Basis // p.1 ≤ p.2}) : Primitive.FiberMaterial s(p.val.1,p.val.2) := by
  by_cases same : p.val.1=p.val.2
  · rw [← same]
    exact Primitive.diagonalFiberMaterial p.val.1 (Primitive.allDiagonal p.val.1)
  · exact Primitive.ordinaryFiberMaterial p.val.1 p.val.2 same
      (Primitive.allOrdinary p.val.1 p.val.2 (lt_of_le_of_ne p.property same))

private def orderedLoad (p : {p : Basis × Basis // p.1 ≤ p.2}) : LoadPrimitive.FiberMaterial s(p.val.1,p.val.2) := by
  by_cases same : p.val.1=p.val.2
  · rw [← same]
    exact LoadPrimitive.diagonalFiber p.val.1 (LoadDiagonal.allDiagonal p.val.1)
  · exact LoadPrimitive.ordinaryFiber p.val.1 p.val.2 same
      (LoadPrimitive.allOrdinary p.val.1 p.val.2 (lt_of_le_of_ne p.property same))

private theorem dependent_congr {α : Sort*} {P : α → Sort*} (f : ∀ a, P a) {a b : α} (same : a=b) : HEq (f a) (f b) := by
  cases same
  rfl

theorem pc_family_ordinary (a b : Basis) (ordered : a < b) :
    Primitive.sourcePCFamily s(a,b)=Primitive.ordinaryFiberMaterial a b ordered.ne (Primitive.allOrdinary a b ordered) := by
  apply eq_of_heq
  apply (eqRec_heq _ _).trans
  change HEq (orderedPC (Sym2.sortEquiv s(a,b))) _
  apply (dependent_congr orderedPC (sorted_source a b ordered.le)).trans
  simp only [orderedPC,dif_neg ordered.ne,heq_eq_eq]

theorem pc_family_diagonal (a : Basis) :
    Primitive.sourcePCFamily s(a,a)=Primitive.diagonalFiberMaterial a (Primitive.allDiagonal a) := by
  apply eq_of_heq
  apply (eqRec_heq _ _).trans
  change HEq (orderedPC (Sym2.sortEquiv s(a,a))) _
  apply (dependent_congr orderedPC (sorted_source a a le_rfl)).trans
  simp [orderedPC]

theorem load_family_ordinary (a b : Basis) (ordered : a < b) :
    LoadPrimitive.sourceLoadFamily s(a,b)=LoadPrimitive.ordinaryFiber a b ordered.ne (LoadPrimitive.allOrdinary a b ordered) := by
  apply eq_of_heq
  apply (eqRec_heq _ _).trans
  change HEq (orderedLoad (Sym2.sortEquiv s(a,b))) _
  apply (dependent_congr orderedLoad (sorted_source a b ordered.le)).trans
  simp only [orderedLoad,dif_neg ordered.ne,heq_eq_eq]

theorem load_family_diagonal (a : Basis) :
    LoadPrimitive.sourceLoadFamily s(a,a)=LoadPrimitive.diagonalFiber a (LoadDiagonal.allDiagonal a) := by
  apply eq_of_heq
  apply (eqRec_heq _ _).trans
  change HEq (orderedLoad (Sym2.sortEquiv s(a,a))) _
  apply (dependent_congr orderedLoad (sorted_source a a le_rfl)).trans
  simp [orderedLoad]

private theorem cancel_frame {ι κ : Type*} (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    (M.submatrix e.symm e.symm).submatrix e e=M := by
  ext i j
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]

attribute [local semireducible] Primitive.ordinaryFiberMaterial Primitive.diagonalFiberMaterial
  LoadPrimitive.ordinaryFiber LoadPrimitive.diagonalFiber

theorem pc_one_ordinary (a b : Basis) (ordered : a < b) :
    Primitive.computedPC.submatrix (orbitPC a b) (orbitPC a b)=
      Primitive.materialPCOne a b (Primitive.allOrdinary a b ordered) := by
  change (restrict pcOrbit s(a,b) Primitive.computedPC).submatrix (offDiagonalEquiv a b ordered.ne)
    (offDiagonalEquiv a b ordered.ne)=_
  rw [Primitive.computedPC,assemble_restriction,pc_family_ordinary a b ordered]
  exact cancel_frame _ _

theorem pc_two_ordinary (a b : Basis) (ordered : a < b) :
    Primitive.computedParentPC.submatrix (orbitPC a b) (orbitPC a b)=
      Primitive.materialPCTwo a b (Primitive.allOrdinary a b ordered) := by
  change (restrict pcOrbit s(a,b) Primitive.computedParentPC).submatrix (offDiagonalEquiv a b ordered.ne)
    (offDiagonalEquiv a b ordered.ne)=_
  rw [Primitive.computedParentPC,assemble_restriction,pc_family_ordinary a b ordered]
  exact cancel_frame _ _

theorem pc_three_ordinary (a b : Basis) (ordered : a < b) :
    Primitive.computedRecoveryPC.submatrix (orbitPC a b) (orbitPC a b)=
      Primitive.materialRecoveryPC a b (Primitive.allOrdinary a b ordered) := by
  change (restrict pcOrbit s(a,b) Primitive.computedRecoveryPC).submatrix (offDiagonalEquiv a b ordered.ne)
    (offDiagonalEquiv a b ordered.ne)=_
  rw [Primitive.computedRecoveryPC,assemble_restriction,pc_family_ordinary a b ordered]
  exact cancel_frame _ _

theorem load_ordinary (a b : Basis) (ordered : a < b) :
    LoadPrimitive.computedLoad.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=
      LoadPrimitive.numericLoad a b (LoadPrimitive.allOrdinary a b ordered) := by
  change (restrict pceOrbit s(a,b) LoadPrimitive.computedLoad).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)
    (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne)=_
  rw [LoadPrimitive.computedLoad,assemble_restriction,load_family_ordinary a b ordered]
  exact cancel_frame _ _

theorem pc_one_diagonal (a : Basis) :
    Primitive.computedPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))=
      Primitive.diagonalMaterialOne a (Primitive.allDiagonal a) := by
  change (restrict pcOrbit s(a,a) Primitive.computedPC).submatrix (diagonalEquiv a) (diagonalEquiv a)=_
  rw [Primitive.computedPC,assemble_restriction,pc_family_diagonal]
  exact cancel_frame _ _

theorem pc_two_diagonal (a : Basis) :
    Primitive.computedParentPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))=
      Primitive.diagonalMaterialTwo a (Primitive.allDiagonal a) := by
  change (restrict pcOrbit s(a,a) Primitive.computedParentPC).submatrix (diagonalEquiv a) (diagonalEquiv a)=_
  rw [Primitive.computedParentPC,assemble_restriction,pc_family_diagonal]
  exact cancel_frame _ _

theorem pc_three_diagonal (a : Basis) :
    Primitive.computedRecoveryPC.submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c))=
      Primitive.diagonalMaterialThree a (Primitive.allDiagonal a) := by
  change (restrict pcOrbit s(a,a) Primitive.computedRecoveryPC).submatrix (diagonalEquiv a) (diagonalEquiv a)=_
  rw [Primitive.computedRecoveryPC,assemble_restriction,pc_family_diagonal]
  exact cancel_frame _ _

theorem load_diagonal (a : Basis) :
    LoadPrimitive.computedLoad.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=
      LoadDiagonal.numericLoad a (LoadDiagonal.allDiagonal a) := by
  change (restrict pceOrbit s(a,a) LoadPrimitive.computedLoad).submatrix (Scaled.Order.diagonalPCEEquiv a)
    (Scaled.Order.diagonalPCEEquiv a)=_
  rw [LoadPrimitive.computedLoad,assemble_restriction,load_family_diagonal]
  exact cancel_frame _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
