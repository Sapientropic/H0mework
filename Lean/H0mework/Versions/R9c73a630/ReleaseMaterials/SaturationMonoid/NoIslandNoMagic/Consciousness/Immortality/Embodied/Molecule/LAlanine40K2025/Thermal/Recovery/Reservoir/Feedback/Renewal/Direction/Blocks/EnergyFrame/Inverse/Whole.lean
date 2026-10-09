import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.InteractionSource

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def sourceProjector : LoadedJoint := Matrix.kronecker Source.donor (1 : Matrix (Fin 2) (Fin 2) ℂ)
def plusCoefficient : ℂ := ((Real.cos BasisInverse.actualAngle : ℂ)^2+
  Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle)⁻¹-((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹
def minusCoefficient : ℂ := ((Real.cos BasisInverse.actualAngle : ℂ)^2-
  Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle)⁻¹-((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹

def sourceInteractionInverse : LoadedJoint :=
  ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ • loadInteraction+
    plusCoefficient • (sourceProjector*loadInteraction)+minusCoefficient • (loadInteraction*sourceProjector)

theorem original_interaction_body : bodyInverse Source.donor (Real.cos BasisInverse.actualAngle)
    (Real.sin BasisInverse.actualAngle) loadInteraction = sourceInteractionInverse := by
  ext i j
  have h := congrArg (fun M : Matrix PairController PairController ℂ => M i.1 j.1)
    (original_interaction_inverse i.2 j.2)
  change inverse Source.donor _ _ _ i.1 j.1 = _
  rw [h]
  simp only [sourceInteractionInverse,plusCoefficient,minusCoefficient,Matrix.add_apply,Matrix.smul_apply]
  rw [sourceProjector,BodyKernel.left_tensor_mul,BodyKernel.mul_left_tensor]
  simp only [Matrix.mul_apply,BodyKernel.slice,Matrix.submatrix_apply]

theorem original_whole_body : bodyInverse Source.donor (Real.cos BasisInverse.actualAngle)
    (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian = sourceFreeInverse+sourceInteractionInverse := by
  have split : loadTotalHamiltonian=originalFreeHamiltonian+loadInteraction := rfl
  have linear : bodyInverse Source.donor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle)
      (originalFreeHamiltonian+loadInteraction) =
    bodyInverse Source.donor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) originalFreeHamiltonian+
    bodyInverse Source.donor (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) loadInteraction := by
    ext i j
    exact congrArg (fun M : Matrix PairController PairController ℂ => M i.1 j.1)
      (inverse_add Source.donor _ _ (BodyKernel.slice originalFreeHamiltonian i.2 j.2) (BodyKernel.slice loadInteraction i.2 j.2))
  rw [split,linear,original_free_inverse_formula,original_interaction_body]

theorem original_output_whole : Measurement.sourceOutputObservable loadTotalHamiltonian =
    Quantum.conjugation BodyKernel.bodyFree (sourceFreeInverse+sourceInteractionInverse) := by
  rw [BasisInverse.original_inverse_formula,BasisInverse.actualOutput,original_inverse_with_donor,original_whole_body]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
