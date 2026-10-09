import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Hamiltonian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] actualUnitary Preparation.sourceEnergyFrame

theorem pair_source_covariant {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) :
    Quantum.localConjugation U U (pairHamiltonian H) = pairHamiltonian (Quantum.conjugation U H) := by
  have identity : Quantum.conjugation U (1 : Matrix ι ι ℂ) = 1 := map_one (Unitary.conjStarAlgAut ℂ _ U)
  simp only [pairHamiltonian,Thermal.Dynamics.pairH,Thermal.Dynamics.freePairH,jointHamiltonian,
    map_add,map_smul,Quantum.localConjugation_tensor,identity,shared_conjugation_swap]

theorem controller_tensor_covariant {ι : Type*} [Fintype ι] [DecidableEq ι]
  (U : Matrix.unitaryGroup ι ℂ) (B : Matrix (ι × ι) (ι × ι) ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) :
    Unitary.conjStarAlgAut ℂ _ (controllerFrame U) (Matrix.kronecker B C) =
      Matrix.kronecker (Quantum.localConjugation U U B) C := by
  rw [Unitary.conjStarAlgAut_apply]
  change Matrix.kronecker (Quantum.localUnitary U U : JointMatrix ι) (1 : Matrix (Fin 2) (Fin 2) ℂ)*
    Matrix.kronecker B C*star (Matrix.kronecker (Quantum.localUnitary U U : JointMatrix ι) (1 : Matrix (Fin 2) (Fin 2) ℂ)) = _
  simp only [Matrix.star_eq_conjTranspose,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one]
  rfl

theorem bare_source_covariant {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) :
    Quantum.conjugation (controllerFrame U) (bareHamiltonian (pairHamiltonian H) 2) =
      bareHamiltonian (pairHamiltonian (Quantum.conjugation U H)) 2 := by
  change Unitary.conjStarAlgAut ℂ _ (controllerFrame U) _ = _
  simp only [bareHamiltonian,map_add]
  simp only [controller_tensor_covariant,pair_source_covariant]
  have identity : Quantum.localConjugation U U (1 : JointMatrix ι) = 1 :=
    map_one (Unitary.conjStarAlgAut ℂ (JointMatrix ι) (Quantum.localUnitary U U))
  exact congrArg (fun X : JointMatrix ι => Matrix.kronecker (pairHamiltonian (Quantum.conjugation U H))
    (1 : Matrix (Fin 2) (Fin 2) ℂ)+Matrix.kronecker X (Powered.Dynamics.controllerHamiltonian 2)) identity

theorem PC_source_covariant (U : Matrix.unitaryGroup Basis ℂ) (H : Matrix Basis Basis ℂ) :
    Quantum.conjugation (controllerFrame U) (sourcePCH H) = sourcePCH (Quantum.conjugation U H) := by
  unfold sourcePCH totalHamiltonian
  change Unitary.conjStarAlgAut ℂ _ (controllerFrame U) _ = _
  rw [map_add]
  exact congrArg₂ (·+·) (bare_source_covariant U H) (shared_conjugation_interaction U H)

theorem original_powered_source : Powered.Producer.poweredTotalHamiltonian = sourcePCH Thermal.Source.energyHamiltonian := rfl

def originalToCalculated : Matrix.unitaryGroup Basis ℂ := star actualUnitary*Preparation.sourceEnergyFrame

theorem same_source_Hamiltonian :
    Quantum.conjugation originalToCalculated Thermal.Source.energyHamiltonian = transformedOriginal := by
  rw [← Powered.Source.sourceHamiltonian_in_shared_frame]
  simp only [Quantum.conjugation_apply,originalToCalculated,Submonoid.coe_mul,Unitary.coe_star,star_mul,star_star,
    transformedOriginal,A]
  have first : (Preparation.sourceEnergyFrame : Matrix Basis Basis ℂ)*star (Preparation.sourceEnergyFrame : Matrix Basis Basis ℂ) = 1 :=
    (Unitary.mem_iff.mp Preparation.sourceEnergyFrame.property).2
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc (Preparation.sourceEnergyFrame : Matrix Basis Basis ℂ)
    (star (Preparation.sourceEnergyFrame : Matrix Basis Basis ℂ)),first,Matrix.one_mul]

/-- This bound starts at the unchanged installed Hpc and reaches the original numeric block Hamiltonian. -/
theorem actual_powered_Hamiltonian_error :
    ‖Quantum.conjugation (controllerFrame originalToCalculated) Powered.Producer.poweredTotalHamiltonian-
      sourcePCH E‖ ≤ (126/10^12 : ℝ) := by
  rw [original_powered_source,PC_source_covariant,same_source_Hamiltonian]
  exact actual_source_PC_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
