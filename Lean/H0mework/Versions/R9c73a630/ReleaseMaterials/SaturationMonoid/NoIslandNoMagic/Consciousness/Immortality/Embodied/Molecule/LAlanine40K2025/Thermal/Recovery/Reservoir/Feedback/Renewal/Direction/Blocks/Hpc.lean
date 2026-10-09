import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Source

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem swap_entry (p q : Basis × Basis) :
    (swapOperator : JointMatrix Basis) p q = if (p.2,p.1) = q then 1 else 0 := by
  have entry := swap_mul_apply (1 : JointMatrix Basis) p.1 p.2 q.1 q.2
  rw [Matrix.mul_one] at entry
  simpa only [Matrix.one_apply] using entry

theorem difference_diagonal_entry (d : Basis → ℂ) (p q : Basis × Basis) :
    Powered.Source.difference (Matrix.diagonal d) p q =
      if p = q then d p.1 - d p.2 else 0 := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d'⟩
  by_cases left : a = c <;> by_cases right : b = d' <;>
    simp [Powered.Source.difference, Matrix.kronecker, Matrix.diagonal,
      left, right]

theorem raising_entry (d : Basis → ℂ) (p q : Basis × Basis) :
    Powered.Source.raising (Matrix.diagonal d) p q = (1/2 : ℂ) *
      ((if p = q then d p.1 - d p.2 else 0) +
       (if (p.2,p.1) = q then d p.2 - d p.1 else 0)) := by
  change (1/2 : ℂ) * (Powered.Source.difference (Matrix.diagonal d) p q +
    ((swapOperator : JointMatrix Basis) * Powered.Source.difference (Matrix.diagonal d)) p q) = _
  rw [swap_mul_apply, difference_diagonal_entry, difference_diagonal_entry]

def orbitPC (a b : Basis) (p : Fin 2 × Fin 2) : PairController :=
  ((if p.1 = 0 then (a,b) else (b,a)),p.2)

def packedHpc (x y : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s := (x+y : ℝ)
  let d := (x-y : ℝ)/2
  ![![(s : ℂ), d, 1, -d], ![d, s+2, d, 1],
    ![1, d, s, -d], ![-d, 1, -d, s+2]]

def scalarHpc (x y : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (packedHpc x y).submatrix finProdFinEquiv finProdFinEquiv

theorem hpc_scalar_block (energies : Basis → ℝ) (a b : Basis) (distinct : a ≠ b) :
    (Powered.Dynamics.totalHamiltonian
      (Dynamics.pairH (Matrix.diagonal (fun i => (energies i : ℂ))) 1) 2
      (Powered.Source.interaction (Matrix.diagonal (fun i => (energies i : ℂ))))).submatrix
        (orbitPC a b) (orbitPC a b) = scalarHpc (energies a) (energies b) := by
  ext ⟨p,c⟩ ⟨q,d⟩
  simp only [Matrix.submatrix_apply, Powered.Dynamics.totalHamiltonian,
    Powered.Dynamics.bareHamiltonian, Dynamics.pairH, Dynamics.freePairH, jointHamiltonian,
    Powered.Source.interaction, Powered.Source.transfer, Matrix.add_apply,
    Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, raising_entry, Matrix.one_apply]
  fin_cases p <;> fin_cases c <;> fin_cases q <;> fin_cases d <;>
    simp [Powered.Source.lowering, Powered.Dynamics.controllerHamiltonian,
      orbitPC, Matrix.single, Matrix.diagonal, swap_entry, smul_eq_mul,
      scalarHpc, packedHpc, Matrix.submatrix, finProdFinEquiv, distinct, Ne.symm distinct, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_div] <;> ring

theorem original_hpc_scalar_block (a b : Basis) (distinct : a ≠ b) :
    Powered.Producer.poweredTotalHamiltonian.submatrix (orbitPC a b) (orbitPC a b) =
      scalarHpc (Preparation.sourceEnergies a) (Preparation.sourceEnergies b) :=
  hpc_scalar_block Preparation.sourceEnergies a b distinct

def diagonalHpc (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2*(x : ℂ)+1, 0; 0, 2*(x : ℂ)+3]

theorem hpc_diagonal_block (energies : Basis → ℝ) (a : Basis) :
    (Powered.Dynamics.totalHamiltonian
      (Dynamics.pairH (Matrix.diagonal (fun i => (energies i : ℂ))) 1) 2
      (Powered.Source.interaction (Matrix.diagonal (fun i => (energies i : ℂ))))).submatrix
        (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c)) = diagonalHpc (energies a) := by
  ext c d
  simp only [Matrix.submatrix_apply, Powered.Dynamics.totalHamiltonian,
    Powered.Dynamics.bareHamiltonian, Dynamics.pairH, Dynamics.freePairH, jointHamiltonian,
    Powered.Source.interaction, Powered.Source.transfer, Matrix.add_apply,
    Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, raising_entry, Matrix.one_apply]
  fin_cases c <;> fin_cases d <;>
    simp [Powered.Source.lowering, Powered.Dynamics.controllerHamiltonian,
      Matrix.single, Matrix.diagonal, swap_entry, smul_eq_mul, diagonalHpc] <;> ring

theorem original_hpc_diagonal_block (a : Basis) :
    Powered.Producer.poweredTotalHamiltonian.submatrix
      (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c)) =
        diagonalHpc (Preparation.sourceEnergies a) :=
  hpc_diagonal_block Preparation.sourceEnergies a

theorem packed_resolvent (x y : ℝ) (lambda : ℂ) :
    (packedHpc x y - lambda • 1).det =
      ((x : ℂ)+y-1-lambda) * ((x : ℂ)+y+3-lambda) *
        (2*(x : ℂ)+1-lambda) * (2*(y : ℂ)+1-lambda) := by
  let s : ℂ := x + y
  let d : ℂ := ((x-y : ℝ)/2 : ℝ)
  have shifted : packedHpc x y - lambda • 1 =
      !![s-lambda, d, 1, -d;
         d, s+2-lambda, d, 1;
         1, d, s-lambda, -d;
         -d, 1, -d, s+2-lambda] := by
    ext i j
    change packedHpc x y i j - lambda * (if i = j then 1 else 0) = _
    fin_cases i <;> fin_cases j <;> simp [packedHpc, s, d]
  rw [shifted, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  simp only [s, d]
  push_cast
  ring

theorem scalar_resolvent (x y : ℝ) (lambda : ℂ) :
    (scalarHpc x y - lambda • 1).det =
      ((x : ℂ)+y-1-lambda) * ((x : ℂ)+y+3-lambda) *
        (2*(x : ℂ)+1-lambda) * (2*(y : ℂ)+1-lambda) := by
  have equality : scalarHpc x y - lambda • 1 =
      (packedHpc x y - lambda • 1).submatrix finProdFinEquiv finProdFinEquiv := by
    ext p q
    change packedHpc x y (finProdFinEquiv p) (finProdFinEquiv q) -
      lambda * (if p = q then 1 else 0) =
      packedHpc x y (finProdFinEquiv p) (finProdFinEquiv q) -
      lambda * (if finProdFinEquiv p = finProdFinEquiv q then 1 else 0)
    by_cases same : p = q
    · simp only [if_pos same, if_pos (congrArg finProdFinEquiv same)]
    · simp only [if_neg same, if_neg (fun equal => same (finProdFinEquiv.injective equal))]
  rw [equality, Matrix.det_submatrix_equiv_self]
  exact packed_resolvent x y lambda

theorem diagonal_resolvent (x : ℝ) (lambda : ℂ) :
    (diagonalHpc x - lambda • 1).det =
      (2*(x : ℂ)+1-lambda)*(2*(x : ℂ)+3-lambda) := by
  rw [Matrix.det_fin_two]
  change (2*(x : ℂ)+1-lambda*1)*(2*(x : ℂ)+3-lambda*1) - (0-lambda*0)*(0-lambda*0) = _
  ring


def offDiagonalEquiv (a b : Basis) (distinct : a ≠ b) :
    (Fin 2 × Fin 2) ≃ {p : PairController // pcOrbit p = s(a,b)} where
  toFun p := ⟨orbitPC a b p, by
    rcases p with ⟨o,c⟩
    fin_cases o <;> simp [orbitPC, pcOrbit, pairOrbit, Sym2.eq_swap]⟩
  invFun p := (if p.val.1 = (a,b) then 0 else 1, p.val.2)
  left_inv p := by
    rcases p with ⟨o,c⟩
    fin_cases o <;> simp [orbitPC, distinct, Ne.symm distinct]
  right_inv p := by
    apply Subtype.ext
    have orientation : p.val.1 = (a,b) ∨ p.val.1 = (b,a) :=
      Sym2.mk_eq_mk_iff.mp p.property
    change (if (if p.val.1 = (a,b) then (0 : Fin 2) else 1) = 0 then (a,b) else (b,a), p.val.2) =
      (p.val.1,p.val.2)
    rcases orientation with left | right
    · simp [left]
    · simp [right, distinct, Ne.symm distinct]

def diagonalEquiv (a : Basis) : Fin 2 ≃ {p : PairController // pcOrbit p = s(a,a)} where
  toFun c := ⟨((a,a),c),rfl⟩
  invFun p := p.val.2
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    have orientation : p.val.1 = (a,a) := by
      have equal : p.val.1 = (a,a) ∨ p.val.1 = (a,a) := Sym2.mk_eq_mk_iff.mp p.property
      exact equal.elim id id
    exact Prod.ext orientation.symm rfl

theorem original_offDiagonal_resolvent (a b : Basis) (distinct : a ≠ b) (lambda : ℂ) :
    (restrict pcOrbit s(a,b) Powered.Producer.poweredTotalHamiltonian - lambda • 1).det =
      ((Preparation.sourceEnergies a : ℂ)+Preparation.sourceEnergies b-1-lambda) *
      ((Preparation.sourceEnergies a : ℂ)+Preparation.sourceEnergies b+3-lambda) *
      (2*(Preparation.sourceEnergies a : ℂ)+1-lambda) *
      (2*(Preparation.sourceEnergies b : ℂ)+1-lambda) := by
  rw [← Matrix.det_submatrix_equiv_self (offDiagonalEquiv a b distinct)]
  simp only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
    Matrix.submatrix_one_equiv]
  change (Powered.Producer.poweredTotalHamiltonian.submatrix (orbitPC a b) (orbitPC a b) - lambda • 1).det = _
  rw [original_hpc_scalar_block a b distinct, scalar_resolvent]

theorem original_diagonal_resolvent (a : Basis) (lambda : ℂ) :
    (restrict pcOrbit s(a,a) Powered.Producer.poweredTotalHamiltonian - lambda • 1).det =
      (2*(Preparation.sourceEnergies a : ℂ)+1-lambda)*
      (2*(Preparation.sourceEnergies a : ℂ)+3-lambda) := by
  rw [← Matrix.det_submatrix_equiv_self (diagonalEquiv a)]
  simp only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
    Matrix.submatrix_one_equiv]
  change (Powered.Producer.poweredTotalHamiltonian.submatrix
    (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c)) - lambda • 1).det = _
  rw [original_hpc_diagonal_block, diagonal_resolvent]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
