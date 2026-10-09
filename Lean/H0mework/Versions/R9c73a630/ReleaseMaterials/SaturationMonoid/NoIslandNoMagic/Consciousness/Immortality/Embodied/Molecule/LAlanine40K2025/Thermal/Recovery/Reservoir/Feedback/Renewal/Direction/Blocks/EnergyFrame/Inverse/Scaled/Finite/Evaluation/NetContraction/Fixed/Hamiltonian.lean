import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.WholeLoaded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Propagation.Producer Load.Source Contraction
open scoped Matrix

def packedHQ (x y : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  let s := x+y
  let d := (x-y)/2
  !![s,d,1,-d; d,s+2,d,1; 1,d,s,-d; -d,1,-d,s+2]

theorem packedHQ_value (x y : ℚ) : qvalue (qreal (packedHQ x y))=packedHpc (x : ℝ) (y : ℝ) := by
  rw [qvalue_real]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [packedHQ,packedHpc]

def ordinaryHQ (a b : Basis) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  (qreal (packedHQ (Diagonal.energy a) (Diagonal.energy b))).submatrix finProdFinEquiv finProdFinEquiv

theorem ordinaryHQ_value (a b : Basis) (distinct : a ≠ b) :
    qvalue (ordinaryHQ a b)=(sourcePCH E).submatrix (orbitPC a b) (orbitPC a b) := by
  rw [ordinaryHQ,qvalue_submatrix,packedHQ_value,Primitive.recorded_energy_original,Primitive.recorded_energy_original]
  exact (Scaled.Order.numeric_hpc_block a b distinct).symm

def diagonalHQ (a : Basis) : MatrixQ (Fin 2) (Fin 2) :=
  diagonalQ ![(2*Diagonal.energy a+1,0),(2*Diagonal.energy a+3,0)]

theorem diagonalHQ_value (a : Basis) :
    qvalue (diagonalHQ a)=(sourcePCH E).submatrix (fun c => ((a,a),c)) (fun c => ((a,a),c)) := by
  have c : (Diagonal.energy a : ℂ)=(Donor.calculatedEnergy a : ℂ) := by exact_mod_cast Primitive.recorded_energy_original a
  have h : qvalue (diagonalHQ a)=diagonalHpc (Donor.calculatedEnergy a) := by
    rw [diagonalHQ,diagonalQ_value]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [diagonalHpc,Scalar.value,c]
  exact h.trans (Scaled.Order.numeric_diagonal_PC a).symm

theorem restore_pc_Q {α : Type*} (k : Sym2 Basis) (e : α ≃ Primitive.PCFiber k) (f : α → PairController)
    (Q : MatrixQ α α) (A : Matrix PairController PairController ℂ) (source : qvalue Q=A.submatrix f f) (incidence : ∀ i, (e i).val=f i) :
    qvalue (Q.submatrix e.symm e.symm)=restrict pcOrbit k A := by
  rw [qvalue_submatrix,source]
  ext i j
  simp only [Matrix.submatrix_apply,restrict]
  rw [← incidence (e.symm i),← incidence (e.symm j),Equiv.apply_symm_apply,Equiv.apply_symm_apply]

structure HamiltonianFamilyQ (k : Sym2 Basis) where
  matrix : MatrixQ (Primitive.PCFiber k) (Primitive.PCFiber k)
  source : qvalue matrix=restrict pcOrbit k (sourcePCH E)

def ordinaryHFamilyQ (a b : Basis) (ordered : a < b) : HamiltonianFamilyQ s(a,b) where
  matrix := (ordinaryHQ a b).submatrix (offDiagonalEquiv a b ordered.ne).symm (offDiagonalEquiv a b ordered.ne).symm
  source := restore_pc_Q _ _ _ _ _ (ordinaryHQ_value a b ordered.ne) (fun _ => rfl)

def diagonalHFamilyQ (a : Basis) : HamiltonianFamilyQ s(a,a) where
  matrix := (diagonalHQ a).submatrix (diagonalEquiv a).symm (diagonalEquiv a).symm
  source := restore_pc_Q _ _ _ _ _ (diagonalHQ_value a) (fun _ => rfl)

def hamiltonianFamilyQ (k : Sym2 Basis) : HamiltonianFamilyQ k := by
  let p := Sym2.sortEquiv k
  have same : s(p.val.1,p.val.2)=k := Sym2.sortEquiv.symm_apply_apply k
  have material : HamiltonianFamilyQ s(p.val.1,p.val.2) := by
    by_cases eq : p.val.1=p.val.2
    · rw [← eq]
      exact diagonalHFamilyQ p.val.1
    · exact ordinaryHFamilyQ p.val.1 p.val.2 (lt_of_le_of_ne p.property eq)
  exact same ▸ material

def hamiltonianQ : MatrixQ PairController PairController := assembleQ pcOrbit (fun k => (hamiltonianFamilyQ k).matrix)

noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem hamiltonianQ_value : qvalue hamiltonianQ=sourcePCH E := by
  rw [hamiltonianQ,qvalue_assemble]
  have source := congrArg (SquareRoot.Full.assemble pcOrbit) (funext (fun k => (hamiltonianFamilyQ k).source))
  have same : regroupStarEquiv pcOrbit (sourcePCH E)=blockEmbedding pcOrbit (fun k => restrict pcOrbit k (sourcePCH E)) :=
    regroup_eq_blocks numeric_pc_preserves
  have complete : SquareRoot.Full.assemble pcOrbit (fun k => restrict pcOrbit k (sourcePCH E))=sourcePCH E := by
    unfold SquareRoot.Full.assemble
    rw [← same,StarAlgEquiv.symm_apply_apply]
  exact source.trans complete

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
