import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerLoadPulse

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Readout

open Collision
open scoped Matrix ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem controlled_body_response (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    bodyRead (Quantum.conjugation (blockUnitary U V) joint) =
      Quantum.conjugation U joint.toBlocks₁₁ + Quantum.conjugation V joint.toBlocks₂₂ := by
  simp only [Quantum.conjugation_apply, bodyRead, blockUnitary_conjugation_diagonal_left,
    blockUnitary_conjugation_diagonal_right]

theorem controlled_expectation_sum (O : Matrix ι ι ℂ) (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    energy O (bodyRead (Quantum.conjugation (blockUnitary U V) joint)) =
      energy O (Quantum.conjugation U joint.toBlocks₁₁) +
        energy O (Quantum.conjugation V joint.toBlocks₂₂) := by
  rw [controlled_body_response]
  exact Load.Producer.HeatProbability.energy_add_right _ _ _

theorem controlled_zero_read (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    zeroRead (Quantum.conjugation (blockUnitary U V) joint) = zeroRead joint :=
  blockUnitary_preserves_zeroRead U V joint

theorem controlled_one_read (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    oneRead (Quantum.conjugation (blockUnitary U V) joint) = oneRead joint :=
  blockUnitary_preserves_oneRead U V joint

theorem controlled_cross_block (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (Quantum.conjugation (blockUnitary U V) joint).toBlocks₁₂ =
      (U : Matrix ι ι ℂ) * joint.toBlocks₁₂ * star (V : Matrix ι ι ℂ) := by
  rw [Quantum.conjugation_apply, blockUnitary_conjugation_blocks, Matrix.toBlocks_fromBlocks₁₂]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Readout
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
