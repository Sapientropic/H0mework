import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Free

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Source.donor originalFreeHamiltonian

def sourceEnvironmentRead : Matrix (Fin 2) (Fin 2) ℂ :=
  (donorEnergy : ℂ) • 1+Powered.Dynamics.controllerHamiltonian 2

def sourceFreeInverse : LoadedJoint :=
  ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ •
    (originalFreeHamiltonian-(Real.sin BasisInverse.actualAngle : ℂ)^2 •
      Matrix.kronecker (1 : Matrix PairController PairController ℂ) sourceEnvironmentRead)

theorem source_donor_idempotent : Source.donor*Source.donor=Source.donor := by
  rw [Spectral.Projection.actual_donor]
  ext i j
  simp [Spectrum.basisPure,Matrix.diagonal_apply]
  aesop

theorem original_free_inverse_formula : bodyInverse Source.donor
    (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle) originalFreeHamiltonian = sourceFreeInverse := by
  ext i j
  have exactSlice := inverse_eigenpart Source.donor (BodyKernel.slice originalFreeHamiltonian i.2 j.2)
    (Real.cos BasisInverse.actualAngle) (Real.sin BasisInverse.actualAngle)
    ((donorEnergy : ℂ)*(if i.2=j.2 then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 i.2 j.2)
    source_donor_idempotent Source.donor_trace (free_slice_left i.2 j.2) (free_slice_right i.2 j.2)
    (Real.cos_sq_add_sin_sq _) BodyKernel.source_cos_nonzero
  have entry := congrArg (fun M : Matrix PairController PairController ℂ => M i.1 j.1) exactSlice
  change inverse Source.donor _ _ _ i.1 j.1 = _
  rw [entry]
  simp only [sourceFreeInverse,sourceEnvironmentRead,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.add_apply,smul_eq_mul,Matrix.one_apply,
    BodyKernel.slice,Matrix.submatrix_apply]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
