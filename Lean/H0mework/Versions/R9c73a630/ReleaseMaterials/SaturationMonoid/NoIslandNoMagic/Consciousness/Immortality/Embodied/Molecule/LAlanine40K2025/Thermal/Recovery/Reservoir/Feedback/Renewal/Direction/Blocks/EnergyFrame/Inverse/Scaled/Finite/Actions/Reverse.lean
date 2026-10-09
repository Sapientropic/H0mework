import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Free
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Receiver
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.LoadFlow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Propagation.Interface Propagation.Producer Powered.Source Powered.Dynamics Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def reversePCH (H : Matrix Basis Basis ℂ) : Matrix PairController PairController ℂ :=
  totalHamiltonian (pairHamiltonian H) 2 (-interaction H)

theorem reverse_PC_covariant (U : Matrix.unitaryGroup Basis ℂ) (H : Matrix Basis Basis ℂ) :
    Quantum.conjugation (controllerFrame U) (reversePCH H)=reversePCH (Quantum.conjugation U H) := by
  unfold reversePCH totalHamiltonian
  rw [map_add,map_neg]
  exact congrArg₂ (·+·) (bare_source_covariant U H) (congrArg Neg.neg (shared_conjugation_interaction U H))

theorem reverse_PC_perturbation (H K : Matrix Basis Basis ℂ) :
    ‖reversePCH H-reversePCH K‖ ≤ 6*‖H-K‖ := by
  have split : reversePCH H-reversePCH K=
      Matrix.kronecker (pairHamiltonian H-pairHamiltonian K) (1 : Matrix (Fin 2) (Fin 2) ℂ)-
        (interaction H-interaction K) := by
    ext i j
    simp only [reversePCH,totalHamiltonian,bareHamiltonian,Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,
      Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  rw [split]
  have tensor : ‖Matrix.kronecker (pairHamiltonian H-pairHamiltonian K) (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      ‖pairHamiltonian H-pairHamiltonian K‖ := NonUnitalStarAlgHom.norm_apply_le tensorLeft _
  have sum := norm_sub_le (Matrix.kronecker (pairHamiltonian H-pairHamiltonian K) (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (interaction H-interaction K)
  linarith [pair_source_perturbation H K,source_interaction_perturbation H K]

theorem numeric_reverse_hermitian : (reversePCH E).IsHermitian :=
  totalHamiltonian_hermitian _ _ _ (pairHamiltonian_hermitian _ actual_diagonal_hermitian) (interaction_hermitian E).neg

theorem numeric_reverse_norm : ‖reversePCH E‖ ≤ 89 := by
  have t := norm_add_le (bareHamiltonian (pairHamiltonian E) 2) (-interaction E)
  rw [norm_neg] at t
  exact t.trans (by linarith [numeric_bare_PC_norm,numeric_interaction_norm])

theorem original_reverse_matrix (t : ℝ) :
    (Load.Recovery.Control.minimalPCUnitary t : Matrix PairController PairController ℂ)=
      hamiltonianFlow (reversePCH Thermal.Source.energyHamiltonian) t :=
  original_controller_flow _ _ _ _ _ _

theorem original_reverse_H_error :
    ‖Quantum.conjugation installedPCFrame (reversePCH Thermal.Source.energyHamiltonian)-reversePCH E‖ ≤ (126/10^12 : ℝ) := by
  rw [installedPCFrame,reverse_PC_covariant,same_source_Hamiltonian]
  exact (reverse_PC_perturbation transformedOriginal E).trans (by
    have h := actual_source_diagonal_error
    change ‖transformedOriginal-E‖ ≤ (21/10^12 : ℝ) at h
    linarith)

theorem original_reverse_flow_error (t : ℝ) :
    ‖Quantum.conjugation installedPCFrame (Load.Recovery.Control.minimalPCUnitary t : Matrix PairController PairController ℂ)-
      hamiltonianFlow (reversePCH E) t‖ ≤ |t| *(126/10^12 : ℝ) := by
  rw [original_reverse_matrix,flow_conjugation]
  have hermitian : (reversePCH Thermal.Source.energyHamiltonian).IsHermitian :=
    totalHamiltonian_hermitian _ _ _ Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian.neg
  have actual := Prepared.conjugation_hermitian installedPCFrame (reversePCH Thermal.Source.energyHamiltonian) hermitian
  exact (hamiltonian_flow_error _ _ actual numeric_reverse_hermitian t).trans
    (mul_le_mul_of_nonneg_left original_reverse_H_error (abs_nonneg t))

def recoveryPCPolynomial : Matrix PairController PairController ℂ := Phase.flowPolynomial (reversePCH E) (3*(nativeClockStep : ℝ))

theorem original_recovery_PC_polynomial_error :
    ‖Quantum.conjugation installedPCFrame
        (Load.Recovery.Control.minimalPCUnitary (3*(nativeClockStep : ℝ)) : Matrix PairController PairController ℂ)-
      recoveryPCPolynomial‖ ≤ (166/10^15 : ℝ) := by
  have poly := Phase.source_short_flow_error (reversePCH E) (3*(nativeClockStep : ℝ))
    (numeric_reverse_norm.trans (by norm_num)) (by rw [abs_of_nonneg (mul_nonneg (by norm_num) Phase.clock_positive.le)]; linarith [Phase.clock_positive])
  have actual := original_reverse_flow_error (3*(nativeClockStep : ℝ))
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedPCFrame (Load.Recovery.Control.minimalPCUnitary (3*(nativeClockStep : ℝ)) : Matrix PairController PairController ℂ))
    (hamiltonianFlow (reversePCH E) (3*(nativeClockStep : ℝ))) recoveryPCPolynomial
  have bounded := actual.trans (show |3*(nativeClockStep : ℝ)| * (126/10^12 : ℝ) ≤ (165/10^15 : ℝ) by rw [nativeClockStep_exact]; norm_num)
  change ‖hamiltonianFlow (reversePCH E) (3*(nativeClockStep : ℝ))-recoveryPCPolynomial‖ ≤ _ at poly
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
