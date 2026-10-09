import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.WholePC
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Load
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Roots

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction
open scoped Matrix

structure LoadedFamilyQ (k : Sym2 Basis) where
  load : MatrixQ (BodyFiber k) (BodyFiber k)
  root : MatrixQ (BodyFiber k) (BodyFiber k)
  complement : MatrixQ (BodyFiber k) (BodyFiber k)
  load_source : qvalue load=restrict pceOrbit k LoadPrimitive.computedLoad
  root_source : qvalue root=restrict pceOrbit k SquareRoot.Full.sourceRoot
  complement_source : qvalue complement=restrict pceOrbit k SquareRoot.Full.sourceComplement

theorem restore_Q {α : Type*} (k : Sym2 Basis) (e : α ≃ BodyFiber k) (f : α → PairController × Fin 2)
    (Q : MatrixQ α α) (A : LoadedJoint) (source : qvalue Q=A.submatrix f f) (incidence : ∀ i, (e i).val=f i) :
    qvalue (Q.submatrix e.symm e.symm)=restrict pceOrbit k A := by
  rw [qvalue_submatrix,source]
  ext i j
  simp only [Matrix.submatrix_apply,restrict]
  rw [← incidence (e.symm i),← incidence (e.symm j),Equiv.apply_symm_apply,Equiv.apply_symm_apply]

noncomputable def ordinaryLoadedFamilyQ (a b : Basis) (ordered : a < b) : LoadedFamilyQ s(a,b) where
  load := (ordinaryLoadQ a b ordered).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).symm (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).symm
  root := (rootOrdinaryQ a b ordered).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).symm (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).symm
  complement := (complementOrdinaryQ a b ordered).submatrix (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).symm (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).symm
  load_source := restore_Q _ _ _ _ _ (ordinaryLoadQ_value a b ordered) (fun _ => rfl)
  root_source := restore_Q _ _ _ _ _ (rootOrdinaryQ_value a b ordered) (fun _ => rfl)
  complement_source := restore_Q _ _ _ _ _ (complementOrdinaryQ_value a b ordered) (fun _ => rfl)

noncomputable def diagonalLoadedFamilyQ (a : Fin 97) : LoadedFamilyQ s(a.castSucc,a.castSucc) where
  load := (diagonalLoadQ a.castSucc).submatrix (Scaled.Order.diagonalPCEEquiv a.castSucc).symm (Scaled.Order.diagonalPCEEquiv a.castSucc).symm
  root := (rootDiagonalQ a).submatrix (Scaled.Order.diagonalPCEEquiv a.castSucc).symm (Scaled.Order.diagonalPCEEquiv a.castSucc).symm
  complement := (complementDiagonalQ a).submatrix (Scaled.Order.diagonalPCEEquiv a.castSucc).symm (Scaled.Order.diagonalPCEEquiv a.castSucc).symm
  load_source := restore_Q _ _ _ _ _ (diagonalLoadQ_value a.castSucc) (fun _ => rfl)
  root_source := restore_Q _ _ _ _ _ (rootDiagonalQ_value a) (fun _ => rfl)
  complement_source := restore_Q _ _ _ _ _ (complementDiagonalQ_value a) (fun _ => rfl)

noncomputable def donorLoadedFamilyQ : LoadedFamilyQ s((97 : Basis),97) where
  load := (diagonalLoadQ 97).submatrix (Scaled.Order.diagonalPCEEquiv 97).symm (Scaled.Order.diagonalPCEEquiv 97).symm
  root := rootDonorQ.submatrix (Scaled.Order.diagonalPCEEquiv 97).symm (Scaled.Order.diagonalPCEEquiv 97).symm
  complement := complementDonorQ.submatrix (Scaled.Order.diagonalPCEEquiv 97).symm (Scaled.Order.diagonalPCEEquiv 97).symm
  load_source := restore_Q _ _ _ _ _ (diagonalLoadQ_value 97) (fun _ => rfl)
  root_source := restore_Q _ _ _ _ _ rootDonorQ_value (fun _ => rfl)
  complement_source := restore_Q _ _ _ _ _ complementDonorQ_value (fun _ => rfl)

noncomputable def diagonalLoadedAtQ (a : Basis) : LoadedFamilyQ s(a,a) := by
  by_cases same : a=97
  · subst a
    exact donorLoadedFamilyQ
  · have range : a.val < 97 := by
      have size := a.isLt
      have different : a.val ≠ 97 := fun h => same (Fin.ext h)
      omega
    let i : Fin 97 := ⟨a.val,range⟩
    have same : i.castSucc=a := Fin.ext rfl
    rw [← same]
    exact diagonalLoadedFamilyQ i

noncomputable def loadedFamilyQ (k : Sym2 Basis) : LoadedFamilyQ k := by
  let p := Sym2.sortEquiv k
  have same : s(p.val.1,p.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  have material : LoadedFamilyQ s(p.val.1,p.val.2) := by
    by_cases eq : p.val.1=p.val.2
    · rw [← eq]
      exact diagonalLoadedAtQ p.val.1
    · exact ordinaryLoadedFamilyQ p.val.1 p.val.2 (lt_of_le_of_ne p.property eq)
  exact same ▸ material

noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem assemble_original (A : LoadedJoint) (kept : Preserves pceOrbit A) :
    SquareRoot.Full.assemble pceOrbit (fun k => restrict pceOrbit k A)=A := by
  have same : regroupStarEquiv pceOrbit A=blockEmbedding pceOrbit (fun k => restrict pceOrbit k A) := regroup_eq_blocks kept
  unfold SquareRoot.Full.assemble
  rw [← same,StarAlgEquiv.symm_apply_apply]

def computedLoadQ : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := assembleQ pceOrbit (fun k => (loadedFamilyQ k).load)

theorem computedLoadQ_value : qvalue computedLoadQ=LoadPrimitive.computedLoad := by
  rw [computedLoadQ,qvalue_assemble]
  have source := congrArg (SquareRoot.Full.assemble pceOrbit) (funext (fun k => (loadedFamilyQ k).load_source))
  exact source.trans (assemble_original _ load_preserves)

def computedRootQ : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := assembleQ pceOrbit (fun k => (loadedFamilyQ k).root)

theorem computedRootQ_value : qvalue computedRootQ=SquareRoot.Full.sourceRoot := by
  rw [computedRootQ,qvalue_assemble]
  have source := congrArg (SquareRoot.Full.assemble pceOrbit) (funext (fun k => (loadedFamilyQ k).root_source))
  exact source.trans (assemble_original _ finite_root_preserves)

def computedComplementQ : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := assembleQ pceOrbit (fun k => (loadedFamilyQ k).complement)

theorem computedComplementQ_value : qvalue computedComplementQ=SquareRoot.Full.sourceComplement := by
  rw [computedComplementQ,qvalue_assemble]
  have source := congrArg (SquareRoot.Full.assemble pceOrbit) (funext (fun k => (loadedFamilyQ k).complement_source))
  exact source.trans (assemble_original _ finite_complement_preserves)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
