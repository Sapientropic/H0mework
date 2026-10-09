import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Leakage
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Projection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] originalToCalculated originalTop originalTopProjector calculatedTop calculatedTopProjector

def actualTopState : Matrix Basis Basis ℂ := Quantum.conjugation originalToCalculated originalTopProjector

theorem actual_top_state_positive : actualTopState.PosSemidef :=
  Quantum.conjugation_posSemidef _ _ (by unfold originalTopProjector; exact Spectrum.basisPure_positive originalTop)

theorem actual_top_state_trace : actualTopState.trace = 1 :=
  (Quantum.conjugation_trace _ _).trans (by unfold originalTopProjector; exact Spectrum.basisPure_trace originalTop)

theorem actual_top_state_idempotent : actualTopState*actualTopState = actualTopState := by
  have original : originalTopProjector*originalTopProjector = originalTopProjector := by
    unfold originalTopProjector
    ext i j
    simp [Spectrum.basisPure,Matrix.diagonal_apply]
    aesop
  have h := map_mul (Unitary.conjStarAlgAut ℂ (Matrix Basis Basis ℂ) originalToCalculated)
    originalTopProjector originalTopProjector
  change Quantum.conjugation originalToCalculated (originalTopProjector*originalTopProjector) =
    actualTopState*actualTopState at h
  rw [original] at h
  exact h.symm

theorem actual_top_complement_error : ‖(1-calculatedTopProjector)*actualTopState‖ ≤ (21/10^11 : ℝ) := by
  have identity : (1-calculatedTopProjector)*actualTopState =
      leakage*star (originalToCalculated : Matrix Basis Basis ℂ) := by
    simp only [actualTopState,Quantum.conjugation_apply,leakage,Matrix.mul_assoc]
  rw [identity]
  have normalized : ‖leakage*star (originalToCalculated : Matrix Basis Basis ℂ)‖ = ‖leakage‖ :=
    CStarRing.norm_mul_coe_unitary leakage (star originalToCalculated)
  rw [normalized]
  exact actual_source_leakage

theorem actual_top_projection_error : ‖actualTopState-calculatedTopProjector‖ ≤ (5/10^10 : ℝ) := by
  have bound := rank_one_projection_error actualTopState actual_top_state_positive.isHermitian
    actual_top_state_idempotent actual_top_state_trace calculatedTop
  rw [← calculatedTopProjector] at bound
  have paid := actual_top_complement_error
  have nonnegative := norm_nonneg ((1-calculatedTopProjector)*actualTopState)
  have squared := pow_le_pow_left₀ nonnegative paid 2
  norm_num [Fintype.card_fin] at bound
  nlinarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
