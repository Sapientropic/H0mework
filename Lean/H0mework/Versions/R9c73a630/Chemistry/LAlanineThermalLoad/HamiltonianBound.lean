import H0mework.Chemistry.LAlanineThermalLoad.SquaredMagnitudeBound
import H0mework.Chemistry.LAlanineThermalLoad.OperatorNorm
import H0mework.Chemistry.LAlanineThermalLoad.EnergyNorm
import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.GeneratedControllerEnvironment

/-! # The complete source Hamiltonian pays its finite norm bound -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace StrictThermal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourceHamiltonian_norm_le_forty :
    ‖Propagation.Interface.activeMatrix Propagation.Source.electronicSource‖ ≤ 40 := by
  apply matrix_norm_le_of_entrySquares _ 40 (by norm_num)
  have bound : (sourceSquaredMagnitude : ℝ) ≤ 1600 * (1000000000000000 : ℝ) ^ 2 :=
    by exact_mod_cast sourceSquaredMagnitude_bound
  have entries :
      (∑ i : Propagation.Interface.Basis, ∑ j : Propagation.Interface.Basis,
        ‖Propagation.Interface.activeMatrix Propagation.Source.electronicSource i j‖ ^ 2) =
        (sourceSquaredMagnitude : ℝ) / (1000000000000000 : ℝ) ^ 2 := by
    simp only [sourceSquaredMagnitude, Int.cast_sum, Int.cast_pow, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    norm_num [Propagation.Interface.activeMatrix, norm_div, Complex.norm_intCast, div_pow]
  rw [entries]
  norm_num at bound ⊢
  linarith


theorem sourceEnergyHamiltonian_norm_le : ‖Thermal.Source.energyHamiltonian‖ ≤ 40 := by
  rw [← Powered.Source.sourceHamiltonian_in_shared_frame]
  change ‖Unitary.conjStarAlgAut ℂ _ (star Preparation.sourceEnergyFrame)
    (Propagation.Interface.activeMatrix Propagation.Source.electronicSource)‖ ≤ 40
  rw [conjugation_norm]
  exact sourceHamiltonian_norm_le_forty

theorem sourceDifference_norm_le : ‖Powered.Source.difference Thermal.Source.energyHamiltonian‖ ≤ 80 := by
  unfold Powered.Source.difference
  calc
    _ ≤ ‖Matrix.kronecker Thermal.Source.energyHamiltonian 1‖ +
        ‖Matrix.kronecker 1 Thermal.Source.energyHamiltonian‖ := norm_sub_le _ _
    _ ≤ ‖Thermal.Source.energyHamiltonian‖ + ‖Thermal.Source.energyHamiltonian‖ :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le (tensorLeft) _)
        (NonUnitalStarAlgHom.norm_apply_le (tensorRight) _)
    _ ≤ 80 := by linarith [sourceEnergyHamiltonian_norm_le]

theorem swap_norm [Nonempty ι] : ‖(Collision.swapOperator : Collision.JointMatrix ι)‖ = 1 := by
  have unitary : (Collision.swapOperator : Collision.JointMatrix ι) ∈ unitary _ := by
    rw [Unitary.mem_iff]
    change Collision.swapOperatorᴴ * Collision.swapOperator = 1 ∧
      Collision.swapOperator * Collision.swapOperatorᴴ = 1
    simp only [Collision.swap_adjoint, Collision.swap_squared, and_self]
  exact CStarRing.norm_coe_unitary ⟨_, unitary⟩

theorem sourceRaising_norm_le : ‖Powered.Source.raising Thermal.Source.energyHamiltonian‖ ≤ 80 := by
  unfold Powered.Source.raising
  rw [norm_smul]
  have product : ‖(Collision.swapOperator : Collision.JointMatrix Propagation.Interface.Basis) *
      Powered.Source.difference Thermal.Source.energyHamiltonian‖ ≤ 80 := by
    calc
      _ ≤ ‖(Collision.swapOperator : Collision.JointMatrix Propagation.Interface.Basis)‖ *
          ‖Powered.Source.difference Thermal.Source.energyHamiltonian‖ := norm_mul_le _ _
      _ ≤ 80 := by rw [swap_norm, one_mul]; exact sourceDifference_norm_le
  have sumBound := norm_add_le (Powered.Source.difference Thermal.Source.energyHamiltonian)
    (Collision.swapOperator * Powered.Source.difference Thermal.Source.energyHamiltonian)
  norm_num
  linarith [sourceDifference_norm_le]

theorem controllerHamiltonian_norm_le : ‖controllerHamiltonian 2‖ ≤ 2 := by
  rw [controllerHamiltonian, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by intro i; fin_cases i <;> norm_num)

theorem sourceLowering_norm_le : ‖Powered.Source.lowering‖ ≤ 1 := by
  apply matrix_norm_le_of_entrySquares _ 1 (by norm_num)
  norm_num [Powered.Source.lowering, Fin.sum_univ_two, Matrix.single_apply]

theorem sourceInteraction_norm_le : ‖Powered.Source.sourceInteraction‖ ≤ 160 := by
  have transfer : ‖Powered.Source.transfer Thermal.Source.energyHamiltonian‖ ≤ 80 := by
    apply (kronecker_norm_le _ _).trans
    nlinarith [sourceRaising_norm_le, sourceLowering_norm_le,
      norm_nonneg (Powered.Source.raising Thermal.Source.energyHamiltonian)]
  change ‖Powered.Source.transfer Thermal.Source.energyHamiltonian +
    (Powered.Source.transfer Thermal.Source.energyHamiltonian)ᴴ‖ ≤ 160
  have sumBound := norm_add_le (Powered.Source.transfer Thermal.Source.energyHamiltonian)
    (Powered.Source.transfer Thermal.Source.energyHamiltonian)ᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at sumBound
  linarith

theorem sourcePairHamiltonian_norm_le : ‖Work.Drive.fieldBaseline‖ ≤ 81 := by
  have freeBound : ‖Thermal.Dynamics.freePairH Thermal.Source.energyHamiltonian‖ ≤ 80 := by
    apply (norm_add_le _ _).trans
    have left := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (κ := Propagation.Interface.Basis))
      Thermal.Source.energyHamiltonian
    have right := NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := Propagation.Interface.Basis))
      Thermal.Source.energyHamiltonian
    change ‖Matrix.kronecker Thermal.Source.energyHamiltonian 1‖ ≤ _ at left
    change ‖Matrix.kronecker 1 Thermal.Source.energyHamiltonian‖ ≤ _ at right
    linarith [sourceEnergyHamiltonian_norm_le]
  change ‖Thermal.Dynamics.freePairH Thermal.Source.energyHamiltonian +
    (1 : ℂ) • Collision.swapOperator‖ ≤ 81
  rw [one_smul]
  have sumBound := norm_add_le (Thermal.Dynamics.freePairH Thermal.Source.energyHamiltonian)
    (Collision.swapOperator : Collision.JointMatrix Propagation.Interface.Basis)
  rw [swap_norm] at sumBound
  linarith

theorem poweredTotalHamiltonian_norm_le : ‖Powered.Producer.poweredTotalHamiltonian‖ ≤ 243 := by
  have bare : ‖bareHamiltonian Work.Drive.fieldBaseline 2‖ ≤ 83 := by
    apply (norm_add_le _ _).trans
    have left := NonUnitalStarAlgHom.norm_apply_le (tensorLeft (κ := Fin 2)) Work.Drive.fieldBaseline
    have right := NonUnitalStarAlgHom.norm_apply_le
      (tensorRight (ι := Propagation.Interface.Basis × Propagation.Interface.Basis))
      (controllerHamiltonian 2)
    change ‖Matrix.kronecker Work.Drive.fieldBaseline 1‖ ≤ _ at left
    change ‖Matrix.kronecker 1 (controllerHamiltonian 2)‖ ≤ _ at right
    linarith [sourcePairHamiltonian_norm_le, controllerHamiltonian_norm_le]
  exact (norm_add_le _ _).trans (by linarith [sourceInteraction_norm_le])

end StrictThermal

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
