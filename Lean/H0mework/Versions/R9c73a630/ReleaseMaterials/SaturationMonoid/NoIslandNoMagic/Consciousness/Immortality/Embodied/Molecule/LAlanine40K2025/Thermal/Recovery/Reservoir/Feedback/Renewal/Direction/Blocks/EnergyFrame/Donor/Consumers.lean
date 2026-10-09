import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Tensor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Propagation.Interface Load.Source Load.Producer.StrictThermal Powered.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] originalToCalculated actualTopState originalTopProjector calculatedTopProjector
  Spectral.Projection.excitedIndex Source.donor installedPCFrame

def calculatedDonor : Matrix PairController PairController ℂ :=
  Spectrum.basisPure ((calculatedTop,calculatedTop),(1 : Fin 2))

theorem original_donor_tensor : Source.donor =
    Matrix.kronecker (Matrix.kronecker originalTopProjector originalTopProjector)
      (Spectrum.basisPure (1 : Fin 2)) := by
  rw [Spectral.Projection.actual_donor]
  unfold originalTopProjector
  rw [basis_tensor,basis_tensor]
  unfold Spectral.Projection.excitedIndex originalTop
  rfl

theorem actual_donor_calculated : Quantum.conjugation installedPCFrame Source.donor =
    Matrix.kronecker (Matrix.kronecker actualTopState actualTopState) (Spectrum.basisPure (1 : Fin 2)) := by
  rw [original_donor_tensor]
  unfold installedPCFrame
  change Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) (controllerFrame originalToCalculated) _ = _
  rw [controller_tensor_covariant,Quantum.localConjugation_tensor]
  unfold actualTopState
  rfl

theorem actual_top_state_norm : ‖actualTopState‖ ≤ 1 := by
  have norm : ‖actualTopState‖ = ‖originalTopProjector‖ := by
    unfold actualTopState
    exact StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix Basis Basis ℂ) originalToCalculated) originalTopProjector
  rw [norm]
  exact original_top_projector_norm

theorem actual_donor_error :
    ‖Quantum.conjugation installedPCFrame Source.donor-calculatedDonor‖ ≤ (1/10^9 : ℝ) := by
  rw [actual_donor_calculated]
  have numerical : calculatedDonor =
      Matrix.kronecker (Matrix.kronecker calculatedTopProjector calculatedTopProjector)
        (Spectrum.basisPure (1 : Fin 2)) := by
    unfold calculatedDonor calculatedTopProjector
    rw [basis_tensor,basis_tensor]
  rw [numerical]
  have split : Matrix.kronecker (Matrix.kronecker actualTopState actualTopState) (Spectrum.basisPure (1 : Fin 2))-
      Matrix.kronecker (Matrix.kronecker calculatedTopProjector calculatedTopProjector) (Spectrum.basisPure (1 : Fin 2)) =
    Matrix.kronecker (Matrix.kronecker actualTopState actualTopState-
      Matrix.kronecker calculatedTopProjector calculatedTopProjector) (Spectrum.basisPure (1 : Fin 2)) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [split]
  have paired := paired_state_error actualTopState calculatedTopProjector actual_top_state_norm (by unfold calculatedTopProjector; exact basis_projector_norm calculatedTop)
  have bounded := kronecker_norm_le
    (Matrix.kronecker actualTopState actualTopState-Matrix.kronecker calculatedTopProjector calculatedTopProjector)
    (Spectrum.basisPure (1 : Fin 2))
  have controller := mul_le_mul_of_nonneg_left (basis_projector_norm (1 : Fin 2))
    (norm_nonneg (Matrix.kronecker actualTopState actualTopState-Matrix.kronecker calculatedTopProjector calculatedTopProjector))
  exact bounded.trans (by nlinarith [controller,actual_top_projection_error])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
