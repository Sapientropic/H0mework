import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Formula

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def bodyInverse (P : Matrix ι ι ℂ) (c s : ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ := fun i j => inverse P c s (BodyKernel.slice O i.2 j.2) i.1 j.1

omit [Fintype κ] [DecidableEq κ] in
theorem basis_body_inverse (t : ι) (c s : ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    bodyInverse (Spectrum.basisPure t) c s O = BasisInverse.bodyInverse t c s O := by
  ext i j
  exact congrArg (fun M : Matrix ι ι ℂ => M i.1 j.1) (basis_inverse t c s (BodyKernel.slice O i.2 j.2))

omit [Fintype κ] [DecidableEq κ] in
theorem body_slice (P : Matrix ι ι ℂ) (c s : ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) (e f : κ) :
    BodyKernel.slice (bodyInverse P c s O) e f = inverse P c s (BodyKernel.slice O e f) := rfl

theorem body_inverse_covariant (U : Matrix.unitaryGroup ι ℂ) (P : Matrix ι ι ℂ)
    (c s : ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) :
    Quantum.conjugation (spectatorFrame (κ := κ) U) (bodyInverse P c s O) =
      bodyInverse (Quantum.conjugation U P) c s (Quantum.conjugation (spectatorFrame (κ := κ) U) O) := by
  have slice (M : Matrix (ι × κ) (ι × κ) ℂ) (e f : κ) :
      BodyKernel.slice (Quantum.conjugation (spectatorFrame (κ := κ) U) M) e f =
        Quantum.conjugation U (BodyKernel.slice M e f) := BodyKernel.slice_local_conjugation U M e f
  ext i j
  have h := slice (bodyInverse P c s O) i.2 j.2
  rw [body_slice,inverse_covariant,← slice O i.2 j.2] at h
  exact congrArg (fun M : Matrix ι ι ℂ => M i.1 j.1) h

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
