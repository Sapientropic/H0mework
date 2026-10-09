import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Coordinates
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.StateNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision Propagation.Interface Propagation.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] actualUnitary Preparation.sourceEnergyFrame baseSystem
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem raw_conjugation_error (U : Matrix.unitaryGroup ι ℂ) (V A : Matrix ι ι ℂ) :
    ‖Quantum.conjugation U A-V*A*star V‖ ≤ (1+‖V‖)*‖A‖*‖(U : Matrix ι ι ℂ)-V‖ := by
  have split : Quantum.conjugation U A-V*A*star V=
      ((U : Matrix ι ι ℂ)-V)*A*star (U : Matrix ι ι ℂ)+V*A*star ((U : Matrix ι ι ℂ)-V) := by
    rw [Quantum.conjugation_apply,star_sub]
    noncomm_ring
  rw [split]
  calc
    _ ≤ ‖((U : Matrix ι ι ℂ)-V)*A*star (U : Matrix ι ι ℂ)‖+‖V*A*star ((U : Matrix ι ι ℂ)-V)‖ := norm_add_le _ _
    _ ≤ ‖(U : Matrix ι ι ℂ)-V‖*‖A‖+‖V‖*‖A‖*‖(U : Matrix ι ι ℂ)-V‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.property)]
      apply add_le_add (norm_mul_le _ _)
      calc
        _ ≤ ‖V*A‖*‖star ((U : Matrix ι ι ℂ)-V)‖ := norm_mul_le _ _
        _ ≤ (‖V‖*‖A‖)*‖star ((U : Matrix ι ι ℂ)-V)‖ := by gcongr; exact norm_mul_le _ _
        _ = _ := by rw [norm_star]
    _ = _ := by ring

theorem original_coordinates_cancel (B : SystemMatrix Basis) :
    Quantum.conjugation originalToCalculated (Preparation.energyCoordinates B)=Quantum.conjugation (star actualUnitary) B := by
  rw [← Powered.Source.sourceCoordinates_as_conjugation,Environment.conjugation_comp]
  have same : originalToCalculated*star Preparation.sourceEnergyFrame=star actualUnitary := by
    simp only [originalToCalculated,mul_assoc,Unitary.mul_star_self,mul_one]
  rw [same]

theorem calculated_field_original : calculatedFieldHamiltonian=Quantum.conjugation (star actualUnitary) (activeMatrix Work.Drive.fieldOffSource) :=
  original_coordinates_cancel _

def rawBaseSystem : SystemMatrix Basis := star Q*baseSystem*Q
def rawFieldHamiltonian : SystemMatrix Basis := star Q*(activeMatrix Work.Drive.fieldOffSource)*Q

theorem raw_frame_norm : ‖Q‖ ≤ 1+(3/10^13 : ℝ) := by
  calc
    _ = ‖(Q-(actualUnitary : SystemMatrix Basis))+(actualUnitary : SystemMatrix Basis)‖ := by rw [sub_add_cancel]
    _ ≤ ‖Q-(actualUnitary : SystemMatrix Basis)‖+‖(actualUnitary : SystemMatrix Basis)‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_sub_rev,CStarRing.norm_coe_unitary]; linarith [actual_unitary_error]

theorem source_coordinate_matrix_error (B : SystemMatrix Basis) :
    ‖Quantum.conjugation (star actualUnitary) B-star Q*B*Q‖ ≤ (7/10^13 : ℝ)*‖B‖ := by
  have paid := raw_conjugation_error (star actualUnitary) (star Q) B
  simp only [star_star,norm_star,Unitary.coe_star,← star_sub] at paid
  calc
    _ ≤ (1+‖Q‖)*‖B‖*‖(actualUnitary : SystemMatrix Basis)-Q‖ := by simpa only [norm_star] using paid
    _ ≤ (1+(1+(3/10^13 : ℝ)))*‖B‖*(3/10^13 : ℝ) := by gcongr; exact raw_frame_norm; exact actual_unitary_error
    _ ≤ _ := by nlinarith [norm_nonneg B]

theorem raw_base_system_error : ‖calculatedBaseSystem-rawBaseSystem‖ ≤ (7/10^13 : ℝ) := by
  have normBound : ‖baseSystem‖ ≤ 1 := state_norm_le_one baseSystem base_system_lawful.1 base_system_lawful.2
  exact (source_coordinate_matrix_error baseSystem).trans (by nlinarith)

theorem original_field_off_norm : ‖activeMatrix Work.Drive.fieldOffSource‖ ≤ 41 := by
  have split : activeMatrix Work.Drive.fieldOffSource=activeMatrix electronicSource-Recovery.SourcePrimitive.sourceFieldDelta := by
    rw [← Recovery.SourcePrimitive.source_field_delta_eq]
    abel
  rw [split]
  exact (norm_sub_le _ _).trans (by linarith [Load.Producer.StrictThermal.sourceHamiltonian_norm_le_forty,Recovery.SourcePrimitive.sourceFieldDelta_norm_le_fifth])

theorem raw_field_hamiltonian_error : ‖calculatedFieldHamiltonian-rawFieldHamiltonian‖ ≤ (3/10^11 : ℝ) := by
  rw [calculated_field_original]
  exact (source_coordinate_matrix_error _).trans (by nlinarith [original_field_off_norm])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
