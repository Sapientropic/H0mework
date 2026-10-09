import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Hamiltonian
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Quantum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Residual

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
open FiniteContinuation Propagation.Interface Thermal.Quantum Thermal.Collision
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
noncomputable section

theorem energy_scaled_hamiltonian {ι : Type} [Fintype ι] (H rho : Matrix ι ι ℂ) (scale : ℝ) :
    energy (scale • H) rho=scale*energy H rho := by
  simp only [energy,smul_mul_assoc,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]

theorem complete_physical_hamiltonian (current : Material) (phase : Phase) (second reserveJoule : ℝ)
    (position momentum : Configuration) (gamma : Matrix Basis Basis ℂ) (resource : PointerJoint) :
    jointHamiltonianSI current phase second reserveJoule position momentum gamma resource=
      energy quantumHamiltonianSI resource+|reserveJoule|+
        energyJoule*nuclearEnergy current phase (second/timeSecond) (unscale lengthMeter position) (unscale momentumSI momentum)+
        energy (gammaHamiltonianSI phase second) (gamma-Reentry.Source.targetRealized) := by
  rw [jointHamiltonianSI,FiniteContinuation.jointHamiltonian,quantumHamiltonianSI,energy_scaled_hamiltonian,
    gammaHamiltonianSI,energy_scaled_hamiltonian,FiniteActuation.electronHamiltonian,energy_scaled_hamiltonian,
    referenceElectronicEnergy,Extract.Port.kinetic,abs_div,abs_of_pos energy_positive]
  field_simp [energy_positive.ne']

theorem hamiltonian_junctions_si (current : Material) (reserveJoule : ℝ) (r p : Configuration)
    (rho : Matrix Basis Basis ℂ) (resource : PointerJoint) :
    jointHamiltonianSI current .enter segmentSeconds reserveJoule r p rho resource=
      jointHamiltonianSI current .drive 0 reserveJoule r p rho resource ∧
    jointHamiltonianSI current .drive segmentSeconds reserveJoule r p rho resource=
      jointHamiltonianSI current .leave 0 reserveJoule r p rho resource := by
  simp only [jointHamiltonianSI,segmentSeconds,mul_div_cancel_right₀ _ time_positive.ne',zero_div]
  have joins := hamiltonian_junctions current (reserveJoule/energyJoule) (unscale lengthMeter r) (unscale momentumSI p) rho resource
  exact ⟨congrArg (energyJoule*·) joins.1,congrArg (energyJoule*·) joins.2⟩

def wholeAccountJoule (current : Material) : ℝ := energyJoule*FiniteContinuation.Runtime.wholeAccount current

def workJoule (current : Material) : ℝ :=
  energyJoule*(current.body.resource.momentum-(nextMaterial current).body.resource.momentum)

theorem work_positive (current : Material) (valid : Admissible current) : 0 < workJoule current :=
  mul_pos energy_positive (sub_pos.mpr (next_receiver_decreases current valid))

theorem work_from_body (current : Material) (valid : Admissible current) :
    workJoule current=energyJoule*(((nextMaterial current).body.frame.total : ℝ)-(current.body.frame.total : ℝ)) := by
  have account := next_mechanical_account current valid
  rw [Extract.Port.kinetic,Extract.Port.kinetic,abs_of_pos (FiniteContinuation.stock_positive _ (next_admissible current valid)),
    abs_of_pos (FiniteContinuation.stock_positive current valid)] at account
  unfold workJoule
  congr 1
  linarith only [account]

theorem work_engine_residual (current : Material) (valid : Admissible current) :
    (engineHartreeJouleQ : ℝ)*(((nextMaterial current).body.frame.total : ℝ)-(current.body.frame.total : ℝ))=
      workJoule current+engineEnergyResidual*(((nextMaterial current).body.frame.total : ℝ)-(current.body.frame.total : ℝ)) := by
  rw [work_from_body current valid]
  exact energy_coordinate_residual _

theorem next_account_si (current : Material) (valid : Admissible current) :
    wholeAccountJoule (nextMaterial current)=wholeAccountJoule current :=
  congrArg (energyJoule*·) (next_whole_account current valid)

theorem history_account_si (depth : Nat) :
    type_of% (FiniteContinuation.Runtime.history_factorizes depth) ∧
    wholeAccountJoule (FiniteContinuation.Runtime.readCurrent (FiniteContinuation.Runtime.atDepth depth))=
      wholeAccountJoule initialMaterial :=
  ⟨FiniteContinuation.Runtime.history_factorizes depth,
    congrArg (energyJoule*·) (FiniteContinuation.Runtime.account_at_depth depth).2⟩

theorem original_historical_account_si (depth : Nat) :
    type_of% (FiniteContinuation.Runtime.history_factorizes depth) ∧
    type_of% (congrArg (energyJoule*·) (FiniteContinuation.Runtime.complete_historical_account depth).2) :=
  ⟨FiniteContinuation.Runtime.history_factorizes depth,
    congrArg (energyJoule*·) (FiniteContinuation.Runtime.complete_historical_account depth).2⟩

theorem uniform_stock_joule (depth : Nat) :
    0 < energyJoule*unreserved initialMaterial ∧
    energyJoule*unreserved initialMaterial <
      energyJoule*(FiniteContinuation.Runtime.readCurrent (FiniteContinuation.Runtime.atDepth depth)).body.resource.momentum :=
  ⟨mul_pos energy_positive (FiniteContinuation.Runtime.uniform_positive_stock depth).2.1,
    mul_lt_mul_of_pos_left (FiniteContinuation.Runtime.uniform_positive_stock depth).2.2 energy_positive⟩

theorem phase_stock_joule (current : Material) (valid : Admissible current) (phase : Phase) (second : ℝ)
    (lo : 0 ≤ second) (hi : second ≤ segmentSeconds) : 0 < receiverJoule current phase second :=
  mul_pos energy_positive (receiver_positive current valid phase (second/timeSecond)
    (clock_range second lo hi).1 (clock_range second lo hi).2)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork
