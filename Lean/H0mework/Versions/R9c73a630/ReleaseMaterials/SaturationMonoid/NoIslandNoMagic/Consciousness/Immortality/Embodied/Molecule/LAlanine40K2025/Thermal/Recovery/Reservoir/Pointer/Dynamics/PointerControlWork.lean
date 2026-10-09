import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerCapacity
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Source.PreparationEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open Collision Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

attribute [local irreducible] sourceHamiltonian sourceUnitary

theorem matrix_generator_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (time : ℝ) :
    Commute H (NormedSpace.exp (time • (-Complex.I • H))) :=
  (((Commute.refl H).smul_right (-Complex.I)).smul_right time).exp_right

theorem sourceUnitary_commutes : Commute sourceHamiltonian (sourceUnitary : PointerJoint) := by
  have commutes := matrix_generator_commutes sourceHamiltonian (nativeClockStep : ℝ)
  rw [sourceHamiltonian_generates] at commutes
  exact commutes

theorem sourceControl_conserves (rho : PointerJoint) :
    energy sourceHamiltonian (Quantum.conjugation sourceUnitary rho) = energy sourceHamiltonian rho := by
  simpa only [Quantum.conjugation_apply] using
    Recovery.PreparationEnergy.commuting_energy sourceHamiltonian rho sourceUnitary sourceUnitary_commutes

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem block_energy_split (H : Matrix ι ι ℂ) (gap : ℝ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    energy (Matrix.fromBlocks H 0 0 (H + (gap : ℂ) • 1)) joint =
      energy H (bodyRead joint) + gap * oneRead joint := by
  have block : Matrix.fromBlocks H 0 0 (H + (gap : ℂ) • 1) * joint =
      Matrix.fromBlocks (H * joint.toBlocks₁₁) (H * joint.toBlocks₁₂)
        ((H + (gap : ℂ) • 1) * joint.toBlocks₂₁) ((H + (gap : ℂ) • 1) * joint.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks joint]
    rw [Matrix.fromBlocks_multiply]
    simp
  unfold energy
  rw [block, trace_fromBlocks]
  simp only [bodyRead, oneRead, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring
end Generic

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
