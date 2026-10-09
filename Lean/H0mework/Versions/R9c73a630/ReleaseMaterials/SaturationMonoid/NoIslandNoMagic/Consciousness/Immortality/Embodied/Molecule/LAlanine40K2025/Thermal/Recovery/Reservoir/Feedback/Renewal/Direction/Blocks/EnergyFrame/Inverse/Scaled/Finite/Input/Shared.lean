import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Factorization

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem shared_partial_swap (U : Matrix.unitaryGroup ι ℂ) (c s : ℝ) :
    Quantum.localConjugation U U (partialSwap c s : JointMatrix ι)=partialSwap c s := by
  have one : Quantum.localConjugation U U (1 : JointMatrix ι)=1 := map_one (Unitary.conjStarAlgAut ℂ _ (Quantum.localUnitary U U))
  simp only [partialSwap,map_sub,map_smul,one,Powered.Source.shared_conjugation_swap]

theorem shared_joint_next (U : Matrix.unitaryGroup ι ℂ) (rho tau : SystemMatrix ι) (c s : ℝ) :
    Quantum.localConjugation U U (jointNext rho tau c s)=
      jointNext (Quantum.conjugation U rho) (Quantum.conjugation U tau) c s := by
  let phi := Unitary.conjStarAlgAut ℂ (JointMatrix ι) (Quantum.localUnitary U U)
  have swap : phi (partialSwap c s)=partialSwap c s := shared_partial_swap U c s
  have tensor : phi (Matrix.kronecker rho tau)=Matrix.kronecker (Quantum.conjugation U rho) (Quantum.conjugation U tau) :=
    Quantum.localConjugation_tensor U U rho tau
  change phi (partialSwap c s*Matrix.kronecker rho tau*(partialSwap c s)ᴴ)=_
  rw [← Matrix.star_eq_conjTranspose,map_mul,map_mul,map_star,swap,tensor]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
