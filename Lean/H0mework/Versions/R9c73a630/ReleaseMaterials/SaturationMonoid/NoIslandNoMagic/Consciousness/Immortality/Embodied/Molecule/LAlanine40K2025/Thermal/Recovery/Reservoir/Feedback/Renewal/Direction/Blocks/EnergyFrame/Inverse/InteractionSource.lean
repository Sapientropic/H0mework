import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Interaction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem original_interaction_top (e f : Fin 2) :
    BodyKernel.slice loadInteraction e f Spectral.Projection.excitedIndex Spectral.Projection.excitedIndex=0 := by
  simp [BodyKernel.slice,Spectral.Projection.excitedIndex,loadInteraction,controllerEnvironmentExchange,
    Matrix.kronecker,Matrix.single]

theorem original_interaction_compression (e f : Fin 2) :
    (BodyKernel.slice loadInteraction e f*Source.donor).trace=0 := by
  rw [Spectral.Projection.actual_donor,BasisInverse.trace_basis]
  exact original_interaction_top e f

theorem original_interaction_sandwich (e f : Fin 2) :
    Source.donor*BodyKernel.slice loadInteraction e f*Source.donor=0 := by
  rw [Spectral.Projection.actual_donor,Donor.basis_projector_sandwich,original_interaction_top,zero_smul]

theorem original_interaction_inverse (e f : Fin 2) :
    inverse Source.donor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle)
      (BodyKernel.slice loadInteraction e f) =
    ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ • BodyKernel.slice loadInteraction e f+
      (((Real.cos BasisInverse.actualAngle : ℂ)^2+Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle)⁻¹-
        ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹) • (Source.donor*BodyKernel.slice loadInteraction e f)+
      (((Real.cos BasisInverse.actualAngle : ℂ)^2-Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle)⁻¹-
        ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹) • (BodyKernel.slice loadInteraction e f*Source.donor) :=
  inverse_zero_compression _ _ _ _ (original_interaction_sandwich e f) (original_interaction_compression e f)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
