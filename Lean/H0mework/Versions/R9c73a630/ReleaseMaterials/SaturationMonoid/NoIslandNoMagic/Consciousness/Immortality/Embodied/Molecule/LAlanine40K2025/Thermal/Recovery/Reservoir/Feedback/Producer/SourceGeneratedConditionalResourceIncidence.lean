import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Dynamics.ConditionalReservoirSupply
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedPointerFeedback

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource

open Collision Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState

section Phase
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitPhase_conjugation (z : unitary ℂ) (U : Matrix.unitaryGroup ι ℂ) (rho : Matrix ι ι ℂ) :
    Quantum.conjugation (z • U) rho = Quantum.conjugation U rho := by
  change (((z : ℂ) • (U : Matrix ι ι ℂ)) * rho * star ((z : ℂ) • (U : Matrix ι ι ℂ))) = _
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Unitary.star_mul_self_of_mem z.property, one_smul]
  rfl

theorem controlled_block_left (U V : Matrix.unitaryGroup ι ℂ)
    (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (Quantum.conjugation (blockUnitary U V) rho).toBlocks₁₁ =
      Quantum.conjugation U rho.toBlocks₁₁ := by
  simp only [Quantum.conjugation_apply, blockUnitary_conjugation_diagonal_left]

theorem controlled_block_right (U V : Matrix.unitaryGroup ι ℂ)
    (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (Quantum.conjugation (blockUnitary U V) rho).toBlocks₂₂ =
      Quantum.conjugation V rho.toBlocks₂₂ := by
  simp only [Quantum.conjugation_apply, blockUnitary_conjugation_diagonal_right]

omit [DecidableEq ι] in
theorem right_block_mass (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    rho.toBlocks₂₂.trace.re = oneRead rho := rfl
end Phase

def loadBlock (current : Live.State) : Current.FullJoint := current.joint.toBlocks₁₁
def suppliedBlock (current : Live.State) : Current.FullJoint := current.joint.toBlocks₂₂

theorem loadBlock_positive (current : Live.State) : (loadBlock current).PosSemidef :=
  current.positive.submatrix Sum.inl
theorem suppliedBlock_positive (current : Live.State) : (suppliedBlock current).PosSemidef :=
  current.positive.submatrix Sum.inr

theorem body_blocks (current : Live.State) :
    bodyRead current.joint = loadBlock current + suppliedBlock current := rfl

theorem suppliedBlock_mass (current : Live.State) :
    (suppliedBlock current).trace.re = oneRead current.joint := right_block_mass current.joint

private theorem complement_strict (p q : ℝ) (hp : 0 < p ∧ p < 1) (total : p + q = 1) :
    0 < q ∧ q < 1 := by constructor <;> linarith

theorem source_one_strict : 0 < oneRead sourceTarget ∧ oneRead sourceTarget < 1 :=
  complement_strict _ _ sourceTarget_strict sourceTarget_binary.2.2

theorem loadBlock_next (current : Live.State) :
    loadBlock (respondNext current) =
      Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (loadBlock current) := by
  unfold loadBlock
  rw [respondNext_joint]
  exact controlled_block_left (Current.loadPulse (nativeClockStep : ℝ))
    (freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ)) current.joint

theorem suppliedBlock_next (current : Live.State) :
    suppliedBlock (respondNext current) =
      Quantum.conjugation (Current.pulse (nativeClockStep : ℝ)) (suppliedBlock current) := by
  unfold suppliedBlock
  rw [respondNext_joint]
  change (Quantum.conjugation (blockUnitary (Current.loadPulse (nativeClockStep : ℝ))
    (freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ))) current.joint).toBlocks₂₂ = _
  rw [controlled_block_right]
  exact unitPhase_conjugation (freePhase (nativeClockStep : ℝ))
    (Current.pulse (nativeClockStep : ℝ)) current.joint.toBlocks₂₂

theorem received_mass_strict :
    0 < (suppliedBlock receivedState).trace.re ∧ (suppliedBlock receivedState).trace.re < 1 := by
  rw [suppliedBlock_mass, receivedState_joint]
  exact source_one_strict

theorem suppliedBlock_not_full_current :
    ¬ ∃ state : Current.State, state.joint = suppliedBlock receivedState := by
  rintro ⟨state, same⟩
  have normalized := state.normalized
  rw [same] at normalized
  have mass := congrArg Complex.re normalized
  norm_num at mass
  linarith [received_mass_strict.2]

theorem received_supply_paid :
    pcEnergyOf (suppliedBlock firstState) - pcEnergyOf (suppliedBlock receivedState) ≤
      donorRemainingOf (suppliedBlock receivedState) := by
  rw [firstState, suppliedBlock_next]
  exact supply_paid_from_actual_remaining _ _ (suppliedBlock_positive receivedState)

theorem received_supply_balance :
    (pcEnergyOf (suppliedBlock firstState) - pcEnergyOf (suppliedBlock receivedState)) +
      (donorEnergyOf (suppliedBlock firstState) - donorEnergyOf (suppliedBlock receivedState)) = 0 := by
  rw [firstState, suppliedBlock_next]
  exact supply_energy_balance _ _

theorem received_supply_environment :
    environmentEnergyOf (suppliedBlock firstState) = environmentEnergyOf (suppliedBlock receivedState) := by
  rw [firstState, suppliedBlock_next]
  exact supply_environment_energy _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
