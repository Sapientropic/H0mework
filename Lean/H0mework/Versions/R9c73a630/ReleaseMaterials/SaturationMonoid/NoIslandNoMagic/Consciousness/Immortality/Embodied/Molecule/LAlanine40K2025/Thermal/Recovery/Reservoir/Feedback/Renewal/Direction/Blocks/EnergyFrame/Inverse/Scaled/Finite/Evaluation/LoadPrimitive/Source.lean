import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Basis

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

def packed (x y : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  (Scaled.Order.smallLoaded x y).submatrix flatten.symm flatten.symm

def sharedHamiltonian (x y : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let s : ℂ := x+y
  let d : ℂ := x-y
  !![s+1,0,d,0,0,0,0,0;
     0,s+1,1,0,0,0,0,0;
     d,1,s+1,0,0,0,0,0;
     0,0,0,s+5,0,0,0,0;
     0,0,0,0,s-1,0,0,0;
     0,0,0,0,0,s+3,0,d;
     0,0,0,0,0,0,s+3,1;
     0,0,0,0,0,d,1,s+3]

def packedEntries (x y : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let s : ℂ := x+y
  let d : ℂ := (x-y)/2
  !![s,0,d,0,1,0,-d,0;
     0,s+2,1,d,0,1,0,-d;
     d,1,s+2,0,d,0,1,0;
     0,d,0,s+4,0,d,0,1;
     1,0,d,0,s,0,-d,0;
     0,1,0,d,0,s+2,1,-d;
     -d,0,1,0,-d,1,s+2,0;
     0,-d,0,1,0,-d,0,s+4]

private theorem native_row0 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((0,0),0) j=(packedEntries x y) (flatten ((0,0),0)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]

private theorem native_row1 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((0,0),1) j=(packedEntries x y) (flatten ((0,0),1)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]

private theorem native_row2 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((0,1),0) j=(packedEntries x y) (flatten ((0,1),0)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]

private theorem native_row3 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((0,1),1) j=(packedEntries x y) (flatten ((0,1),1)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]
  all_goals ring

private theorem native_row4 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((1,0),0) j=(packedEntries x y) (flatten ((1,0),0)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]

private theorem native_row5 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((1,0),1) j=(packedEntries x y) (flatten ((1,0),1)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]

private theorem native_row6 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((1,1),0) j=(packedEntries x y) (flatten ((1,1),0)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]

private theorem native_row7 (x y : ℝ) (j : NativeIndex) :
    Scaled.Order.smallLoaded x y ((1,1),1) j=(packedEntries x y) (flatten ((1,1),1)) (flatten j) := by
  rcases j with ⟨⟨p,d⟩,f⟩
  fin_cases p <;> fin_cases d <;> fin_cases f <;>
    norm_num [packedEntries,flatten,Scaled.Order.smallLoaded,Scaled.Order.smallExchange,
      Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,Powered.Dynamics.controllerHamiltonian,
      scalarHpc,packedHpc,controllerEnvironmentExchange,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix,Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,
      finProdFinEquiv,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div]
  all_goals ring

theorem native_entries (x y : ℝ) :
    Scaled.Order.smallLoaded x y=(packedEntries x y).submatrix flatten flatten := by
  ext ⟨⟨o,c⟩,e⟩ j
  fin_cases o <;> fin_cases c <;> fin_cases e
  · exact native_row0 x y j
  · exact native_row1 x y j
  · exact native_row2 x y j
  · exact native_row3 x y j
  · exact native_row4 x y j
  · exact native_row5 x y j
  · exact native_row6 x y j
  · exact native_row7 x y j

theorem packed_entries (x y : ℝ) : packed x y=packedEntries x y := by
  unfold packed
  rw [native_entries,Matrix.submatrix_submatrix]
  simp only [Equiv.apply_symm_apply,Function.comp_def]
  rfl

theorem original_load_basis (x y : ℝ) : packed x y*basis=basis*sharedHamiltonian x y := by
  rw [packed_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [packedEntries,basis,castMatrix,basisQ,sharedHamiltonian,Matrix.mul_apply,Fin.sum_univ_succ]
  all_goals ring

theorem original_load_shared (x y : ℝ) : packed x y=basis*sharedHamiltonian x y*inverse := by
  rw [← original_load_basis,Matrix.mul_assoc,basis_right,Matrix.mul_one]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
