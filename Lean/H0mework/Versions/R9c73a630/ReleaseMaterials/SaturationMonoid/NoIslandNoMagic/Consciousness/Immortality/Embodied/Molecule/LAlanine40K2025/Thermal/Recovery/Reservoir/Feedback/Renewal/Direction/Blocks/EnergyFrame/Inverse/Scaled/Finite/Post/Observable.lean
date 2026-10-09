import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Pointer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def pcLift (H : Matrix PairController PairController ℂ) : Current.FullJoint :=
  Matrix.kronecker (Matrix.kronecker H (1 : Matrix PairController PairController ℂ)) (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem pc_lift_covariance (U : Matrix.unitaryGroup PairController ℂ) (H : Matrix PairController PairController ℂ) :
    Quantum.conjugation (spectatorFrame (Quantum.localUnitary U U)) (pcLift H)=pcLift (Quantum.conjugation U H) := by
  rw [pcLift,spectator_conjugation]
  change Matrix.kronecker (Quantum.localConjugation U U (Matrix.kronecker H (1 : Matrix PairController PairController ℂ)))
    (1 : Matrix (Fin 2) (Fin 2) ℂ)=_
  rw [Quantum.localConjugation_tensor]
  have one : Quantum.conjugation U (1 : Matrix PairController PairController ℂ)=1 := map_one (Unitary.conjStarAlgAut ℂ _ U)
  rw [one]
  rfl

theorem pc_lift_norm (H : Matrix PairController PairController ℂ) : ‖pcLift H‖ ≤ ‖H‖ :=
  (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController × PairController) (κ := Fin 2)) _).trans
    (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := PairController)) H)

theorem diagonal_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Quantum.conjugation (blockUnitary U U) (pointerDiagonal A)=pointerDiagonal (Quantum.conjugation U A) := by
  change (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*Matrix.fromBlocks A 0 0 A*
    star (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)=_
  rw [blockUnitary_conjugation_blocks]
  simp [pointerDiagonal,Quantum.conjugation_apply]

theorem diagonal_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖pointerDiagonal A‖ ≤ ‖A‖ := NonUnitalStarAlgHom.norm_apply_le pointerDiagonal A

def finitePCObservable : PointerJoint := pointerDiagonal (pcLift (sourcePCH E))
def calculatedPCObservable : PointerJoint := Quantum.conjugation pointerFrame Sectors.pointerPCObservable

theorem actual_PC_observable_coordinates : calculatedPCObservable=
    pointerDiagonal (pcLift (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian)) := by
  change Quantum.conjugation (blockUnitary Supply.installedFullFrame Supply.installedFullFrame)
    (pointerDiagonal (pcLift Powered.Producer.poweredTotalHamiltonian))=_
  rw [diagonal_conjugation]
  exact congrArg pointerDiagonal (pc_lift_covariance installedPCFrame Powered.Producer.poweredTotalHamiltonian)

theorem finite_PC_observable_error : ‖calculatedPCObservable-finitePCObservable‖ ≤ (126/10^12 : ℝ) := by
  rw [actual_PC_observable_coordinates,finitePCObservable,← map_sub]
  have delta : pcLift (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian)-pcLift (sourcePCH E)=
      pcLift (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian-sourcePCH E) := by
    ext i j
    simp only [pcLift,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  apply (diagonal_norm_le _).trans
  rw [delta]
  exact (pc_lift_norm _).trans actual_powered_Hamiltonian_error

theorem finite_PC_observable_norm : ‖finitePCObservable‖ ≤ 89 :=
  (diagonal_norm_le _).trans ((pc_lift_norm _).trans numeric_PC_norm)

theorem finite_PC_observable_hermitian : finitePCObservable.IsHermitian :=
  Prepared.doubled_hermitian _ (Prepared.tensor_hermitian _ _
    (Prepared.tensor_hermitian _ _ numeric_PC_hermitian (by simp)) (by simp))

theorem calculated_PC_observable_hermitian : calculatedPCObservable.IsHermitian :=
  Prepared.conjugation_hermitian pointerFrame _ Prepared.pointer_PC_hermitian

theorem calculated_PC_observable_norm : ‖calculatedPCObservable‖ ≤ 90 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub calculatedPCObservable finitePCObservable 0
  simp only [sub_zero] at triangle
  linarith [finite_PC_observable_error,finite_PC_observable_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
