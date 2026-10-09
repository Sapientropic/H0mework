import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.RawCoordinates
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Long

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def systemTime : ℝ := (nativeClockStep : ℝ)+(Preparation.collisionCurrentTime : ℝ)

theorem system_time_bound : |systemTime| ≤ 2 := by
  rw [systemTime,nativeClockStep_exact,Preparation.collisionCurrentTime_exact]
  norm_num

theorem raw_field_hermitian : rawFieldHamiltonian.IsHermitian := by
  have p := Matrix.isHermitian_mul_mul_conjTranspose (star Q) (Propagation.Dynamics.activeMatrix_hermitian Work.Drive.fieldOffSource)
  simpa only [rawFieldHamiltonian,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using p

theorem calculated_field_norm : ‖calculatedFieldHamiltonian‖ ≤ 41 := by
  rw [calculated_field_original]
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (star actualUnitary)) (Propagation.Interface.activeMatrix Work.Drive.fieldOffSource)
  change ‖Quantum.conjugation (star actualUnitary) _‖=_ at same
  rw [same]
  exact original_field_off_norm

theorem raw_field_norm : ‖rawFieldHamiltonian‖ ≤ 42 := by
  have t := norm_sub_le_norm_sub_add_norm_sub rawFieldHamiltonian calculatedFieldHamiltonian 0
  simp only [sub_zero] at t
  have d := raw_field_hamiltonian_error
  rw [norm_sub_rev] at d
  linarith [calculated_field_norm]

def activePolynomial : SystemMatrix Basis := Phase.longFlowPolynomial E systemTime
def fieldPolynomial : SystemMatrix Basis := Phase.flowPolynomial rawFieldHamiltonian (nativeClockStep : ℝ)

theorem active_polynomial_error : ‖hamiltonianFlow transformedOriginal systemTime-activePolynomial‖ ≤ (5/10^11 : ℝ) := by
  have t := norm_sub_le_norm_sub_add_norm_sub (hamiltonianFlow transformedOriginal systemTime)
    (hamiltonianFlow E systemTime) activePolynomial
  have first := hamiltonian_flow_error transformedOriginal E transformed_hermitian actual_diagonal_hermitian systemTime
  have source : ‖transformedOriginal-E‖ ≤ (21/10^12 : ℝ) := actual_source_diagonal_error
  have firstBound : ‖hamiltonianFlow transformedOriginal systemTime-hamiltonianFlow E systemTime‖ ≤ (42/10^12 : ℝ) :=
    first.trans (by nlinarith [mul_le_mul system_time_bound source (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)])
  have last := Phase.long_flow_polynomial_error E actual_diagonal_hermitian systemTime (diagonal_norm.trans (by norm_num)) system_time_bound
  change ‖hamiltonianFlow E systemTime-activePolynomial‖ ≤ _ at last
  linarith

theorem field_polynomial_error : ‖hamiltonianFlow calculatedFieldHamiltonian (nativeClockStep : ℝ)-fieldPolynomial‖ ≤ (2/10^14 : ℝ) := by
  have t := norm_sub_le_norm_sub_add_norm_sub (hamiltonianFlow calculatedFieldHamiltonian (nativeClockStep : ℝ))
    (hamiltonianFlow rawFieldHamiltonian (nativeClockStep : ℝ)) fieldPolynomial
  have first := hamiltonian_flow_error calculatedFieldHamiltonian rawFieldHamiltonian calculated_field_hermitian raw_field_hermitian (nativeClockStep : ℝ)
  have firstBound : ‖hamiltonianFlow calculatedFieldHamiltonian (nativeClockStep : ℝ)-hamiltonianFlow rawFieldHamiltonian (nativeClockStep : ℝ)‖ ≤ (15/10^15 : ℝ) := by
    apply first.trans
    apply (mul_le_mul_of_nonneg_left raw_field_hamiltonian_error (abs_nonneg _)).trans
    rw [nativeClockStep_exact]
    norm_num
  have last := Phase.source_short_flow_error rawFieldHamiltonian (nativeClockStep : ℝ) (raw_field_norm.trans (by norm_num))
    (by rw [abs_of_pos Phase.clock_positive]; linarith [Phase.clock_positive])
  change ‖hamiltonianFlow rawFieldHamiltonian (nativeClockStep : ℝ)-fieldPolynomial‖ ≤ _ at last
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
