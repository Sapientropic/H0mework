import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Splice
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.LocalFlows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.Algebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix BigOperators
noncomputable section

abbrev RawIndex := Fin 1 ⊕ (Fin 2 ⊕ Fin 1)

def pack : RawIndex ≃ Fin 4 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)).trans finSumFinEquiv

def toNative : RawIndex ≃ Fin 2 × Fin 2 := pack.trans (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm

def raw (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) : Matrix RawIndex RawIndex ℂ :=
  Matrix.fromBlocks (Matrix.scalar (Fin 1) a) 0 0 (Matrix.fromBlocks M 0 0 (Matrix.scalar (Fin 1) b))

theorem raw_polynomial (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (n : Nat) :
    Phase.polynomial (raw M a b) n=raw (Phase.polynomial M n)
      (Primitive.scalarPolynomial a n) (Primitive.scalarPolynomial b n) := by
  simp only [raw,LoadPrimitive.join_polynomial,LoadPrimitive.scalar_polynomial]

theorem raw_smul (z : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    z • raw M a b=raw (z • M) (z*a) (z*b) := by
  have scalar (c : ℂ) : z • Matrix.scalar (Fin 1) c=Matrix.scalar (Fin 1) (z*c) := by
    change z • (Matrix.scalarAlgHom (Fin 1) ℂ) c=(Matrix.scalarAlgHom (Fin 1) ℂ) (z • c)
    exact (map_smul _ _ _).symm
  simp only [raw,Matrix.fromBlocks_smul,smul_zero,scalar]

theorem native_source (x : ℝ) :
    (Scaled.Order.diagonalLoaded x).submatrix toNative toNative=
      raw (middleH (2*(x : ℂ)+3)) (2*(x : ℂ)+1) (2*(x : ℂ)+5) := by
  ext i j
  rcases i with (i | (i | i)) <;> rcases j with (j | (j | j)) <;> fin_cases i <;> fin_cases j <;>
    norm_num [Scaled.Order.diagonalLoaded,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
      Powered.Dynamics.controllerHamiltonian,diagonalHpc,controllerEnvironmentExchange,
      raw,middleH,Matrix.fromBlocks,Matrix.scalar_apply,Matrix.submatrix,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Matrix.diagonal_apply,Matrix.single,toNative,pack,finSumFinEquiv,finProdFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Fin.divNat,Fin.modNat]
  all_goals ring

theorem original_hamiltonian (x : ℝ) : Scaled.Order.diagonalLoaded x=
    (raw (middleH (2*(x : ℂ)+3)) (2*(x : ℂ)+1) (2*(x : ℂ)+5)).submatrix toNative.symm toNative.symm := by
  have h := congrArg (fun A : Matrix RawIndex RawIndex ℂ => A.submatrix toNative.symm toNative.symm) (native_source x)
  simp only [Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply] at h
  exact h

def rawValue (x time : ℝ) : Matrix RawIndex RawIndex ℂ :=
  let z : ℂ := (time : ℂ)*(-Complex.I)
  raw (middle (LoadPrimitive.coefficientPolynomial (2*(x : ℂ)+3) 0 z 14))
    (Primitive.scalarPolynomial (z*(2*(x : ℂ)+1)) 14)
    (Primitive.scalarPolynomial (z*(2*(x : ℂ)+5)) 14)

def valueMatrix (x time : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (rawValue x time).submatrix toNative.symm toNative.symm

theorem raw_flow_values (x time : ℝ) :
    Phase.flowPolynomial (raw (middleH (2*(x : ℂ)+3)) (2*(x : ℂ)+1) (2*(x : ℂ)+5)) time=rawValue x time := by
  have scalar (M : Matrix RawIndex RawIndex ℂ) : time • (-Complex.I • M)=((time : ℂ)*(-Complex.I)) • M := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,mul_assoc]
  unfold Phase.flowPolynomial
  rw [scalar,raw_smul,raw_polynomial,middle_polynomial]
  rfl

theorem original_native_values (x time : ℝ) : Phase.flowPolynomial (Scaled.Order.diagonalLoaded x) time=valueMatrix x time := by
  rw [original_hamiltonian,← Primitive.flow_reindex,raw_flow_values]
  rfl

theorem original_load_values (a : Basis) :
    Actions.loadPolynomial.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)=
      valueMatrix (Donor.calculatedEnergy a) (nativeClockStep : ℝ) := by
  unfold Actions.loadPolynomial
  rw [Primitive.diagonal_load_original]
  exact original_native_values _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
