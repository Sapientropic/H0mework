import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerElectronic
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerRealizationNorm

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def phaseTarget : Matrix Basis Basis ℂ :=
  Unitary.conjStarAlgAut ℂ _ (JointNext.Math.frozenUnitary Source.hamiltonian sourceHamiltonian_hermitian
    (Continuation.duration : ℝ)) Source.currentRealized

theorem actual_duration_bound : |(Continuation.duration : ℝ)| < (432 : ℝ) / 10 ^ 6 :=
  JointNext.Producer.actual_duration_bound

theorem source_geometric_displacement : ‖realizedInputTarget - phaseTarget‖ < (1650 : ℝ) / 10 ^ 12 := by
  have bound := HeldForce.Producer.conjugation_displacement
    (ElectronicFrame.Polar.matrix Source.crossMatrix) phaseTarget
    (ElectronicFrame.Polar.matrix_mem_unitary _ sourceCross_close)
  change ‖realizedInputTarget - phaseTarget‖ ≤ _ at bound
  have phaseNorm : ‖phaseTarget‖ = ‖Source.currentRealized‖ := StarAlgEquiv.norm_map _ _
  rw [phaseNorm] at bound
  have close := geometric_unitary_close
  have input := realized_input_norm
  have product : 2 * ‖ElectronicFrame.Polar.matrix Source.crossMatrix - 1‖ * ‖Source.currentRealized‖ <
      2 * ((75 : ℝ) / 10 ^ 12) * 11 := by gcongr
  exact bound.trans_lt (by norm_num at product ⊢; exact product)

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
