import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Free
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.LoadFlow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Propagation.Producer Powered.Dynamics Load.Source Load.Producer Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def loadPolynomial : LoadedJoint := Phase.flowPolynomial numericLoadHamiltonian (nativeClockStep : ℝ)
def parentPCPolynomial : Matrix PairController PairController ℂ := Phase.flowPolynomial (sourcePCH E) (2*(nativeClockStep : ℝ))
def recoveryEnvironmentPolynomial : Matrix (Fin 2) (Fin 2) ℂ :=
  Phase.flowPolynomial (controllerHamiltonian 2) (3*(nativeClockStep : ℝ))

theorem numeric_load_norm : ‖numericLoadHamiltonian‖ ≤ 92 := by
  have bare := norm_add_le (Matrix.kronecker (sourcePCH E) (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (Matrix.kronecker (1 : Matrix PairController PairController ℂ) (controllerHamiltonian 2))
  have left : ‖Matrix.kronecker (sourcePCH E) (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ‖sourcePCH E‖ :=
    NonUnitalStarAlgHom.norm_apply_le tensorLeft _
  have right : ‖Matrix.kronecker (1 : Matrix PairController PairController ℂ) (controllerHamiltonian 2)‖ ≤ ‖controllerHamiltonian 2‖ :=
    NonUnitalStarAlgHom.norm_apply_le tensorRight _
  change ‖bareHamiltonian (sourcePCH E) 2‖ ≤ _ at bare
  have sum := norm_add_le (bareHamiltonian (sourcePCH E) 2) loadInteraction
  exact sum.trans (by linarith [numeric_PC_norm,controllerHamiltonian_norm_le,loadInteraction_norm_le_one])

theorem original_load_polynomial_error :
    ‖Quantum.conjugation installedLoadFrame (loadUnitary (nativeClockStep : ℝ) : LoadedJoint)-loadPolynomial‖ ≤ (56/10^15 : ℝ) := by
  have poly := Phase.source_short_flow_error numericLoadHamiltonian (nativeClockStep : ℝ)
    (numeric_load_norm.trans (by norm_num)) (by rw [abs_of_pos Phase.clock_positive]; linarith [Phase.clock_positive])
  have actual := actual_load_action_error (nativeClockStep : ℝ)
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedLoadFrame (loadUnitary (nativeClockStep : ℝ) : LoadedJoint))
    (hamiltonianFlow numericLoadHamiltonian (nativeClockStep : ℝ)) loadPolynomial
  have bounded := actual.trans (show |(nativeClockStep : ℝ)| * (126/10^12 : ℝ) ≤ (55/10^15 : ℝ) by rw [nativeClockStep_exact]; norm_num)
  change ‖hamiltonianFlow numericLoadHamiltonian (nativeClockStep : ℝ)-loadPolynomial‖ ≤ _ at poly
  linarith

theorem original_parent_matrix : (loadParentUnitary : Matrix PairController PairController ℂ)=
    hamiltonianFlow Powered.Producer.poweredTotalHamiltonian (2*(nativeClockStep : ℝ)) :=
  original_controller_flow _ _ _ _ _ _

theorem original_parent_PC_polynomial_error :
    ‖Quantum.conjugation installedPCFrame (loadParentUnitary : Matrix PairController PairController ℂ)-parentPCPolynomial‖ ≤ (111/10^15 : ℝ) := by
  rw [original_parent_matrix]
  have poly := Phase.source_short_flow_error (sourcePCH E) (2*(nativeClockStep : ℝ))
    (numeric_PC_norm.trans (by norm_num)) (by rw [abs_of_nonneg (mul_nonneg (by norm_num) Phase.clock_positive.le)]; linarith [Phase.clock_positive])
  have actual := actual_PC_flow_error (2*(nativeClockStep : ℝ))
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedPCFrame (hamiltonianFlow Powered.Producer.poweredTotalHamiltonian (2*(nativeClockStep : ℝ))))
    (hamiltonianFlow (sourcePCH E) (2*(nativeClockStep : ℝ))) parentPCPolynomial
  have bounded := actual.trans (show |2*(nativeClockStep : ℝ)| * (126/10^12 : ℝ) ≤ (110/10^15 : ℝ) by rw [nativeClockStep_exact]; norm_num)
  change ‖hamiltonianFlow (sourcePCH E) (2*(nativeClockStep : ℝ))-parentPCPolynomial‖ ≤ _ at poly
  linarith

theorem original_recovery_environment_polynomial_error :
    ‖(Load.Recovery.Control.environmentUnitary (3*(nativeClockStep : ℝ)) : Matrix (Fin 2) (Fin 2) ℂ)-
      recoveryEnvironmentPolynomial‖ ≤ (1/10^18 : ℝ) :=
  Phase.source_short_flow_error (controllerHamiltonian 2) _ (controllerHamiltonian_norm_le.trans (by norm_num))
    (by rw [abs_of_nonneg (mul_nonneg (by norm_num) Phase.clock_positive.le)]; linarith [Phase.clock_positive])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
