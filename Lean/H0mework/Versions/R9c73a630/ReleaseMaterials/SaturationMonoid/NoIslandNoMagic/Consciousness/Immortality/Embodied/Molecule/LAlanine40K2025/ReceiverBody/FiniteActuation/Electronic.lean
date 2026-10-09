import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Plateau

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
open Propagation.Interface Thermal.Collision Thermal.Quantum
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Blocks.EnergyFrame
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def electronAction (s : ℝ) : Matrix.unitaryGroup Basis ℂ :=
  ⟨hamiltonianFlow referenceElectronicHamiltonian s,
    hamiltonianFlow_unitary _ Reentry.TargetFock.hamiltonian_hermitian s⟩

def electronFlow (rho : Matrix Basis Basis ℂ) (s : ℝ) : Matrix Basis Basis ℂ :=
  conjugation (electronAction s) rho

def electronHamiltonian (rate : ℝ) : Matrix Basis Basis ℂ := rate • referenceElectronicHamiltonian

theorem electron_flow_generated (rho : Matrix Basis Basis ℂ) (s : ℝ) :
    electronFlow rho s=Extract.Port.bodyFlow referenceElectronicHamiltonian rho s := by
  rw [electronFlow,conjugation_apply]
  rfl

theorem electron_flow_zero (rho : Matrix Basis Basis ℂ) : electronFlow rho 0=rho := by
  rw [electron_flow_generated]
  simp [Extract.Port.bodyFlow,hamiltonianFlow]

theorem electron_equation (rho : Matrix Basis Basis ℂ) (clock : ℝ → ℝ) (rate t : ℝ)
    (generated : HasDerivAt clock rate t) :
    HasDerivAt (fun time => electronFlow rho (clock time))
      (-Complex.I • (electronHamiltonian rate*electronFlow rho (clock t)-
        electronFlow rho (clock t)*electronHamiltonian rate)) t := by
  simp only [electron_flow_generated]
  have dynamics := (Extract.Port.body_flow_liouville referenceElectronicHamiltonian rho
    Reentry.TargetFock.hamiltonian_hermitian (clock t)).scomp t generated
  simpa only [Function.comp_apply,electronHamiltonian,smul_mul_assoc,mul_smul_comm,← smul_sub,
    smul_comm rate (-Complex.I)] using! dynamics

theorem actual_on_electron_equation (t : ℝ) :
    HasDerivAt (fun time => electronFlow input.joint.body.realized (onTime time))
      (-Complex.I • (electronHamiltonian (onRate t)*electronFlow input.joint.body.realized (onTime t)-
        electronFlow input.joint.body.realized (onTime t)*electronHamiltonian (onRate t))) t :=
  electron_equation _ _ _ _ (on_time_derivative t)

theorem actual_off_electron_equation (t : ℝ) :
    HasDerivAt (fun time => electronFlow input.joint.body.realized (offTime time))
      (-Complex.I • (electronHamiltonian (offRate t)*electronFlow input.joint.body.realized (offTime t)-
        electronFlow input.joint.body.realized (offTime t)*electronHamiltonian (offRate t))) t :=
  electron_equation _ _ _ _ (off_time_derivative t)

theorem electron_energy (rho : Matrix Basis Basis ℂ) (s : ℝ) :
    energy referenceElectronicHamiltonian (electronFlow rho s)=energy referenceElectronicHamiltonian rho := by
  rw [electronFlow,conjugation_apply]
  exact Thermal.Recovery.PreparationEnergy.commuting_energy _ _ (electronAction s)
    (matrix_generator_commutes referenceElectronicHamiltonian s)

theorem input_realized : input.joint.body.realized=Reentry.Source.targetRealized := by
  rw [input_body]
  exact realized_path_exact duration

theorem electron_centered_energy (s : ℝ) :
    referenceElectronicEnergy (electronFlow input.joint.body.realized s)=0 := by
  have paired := electron_energy input.joint.body.realized s
  rw [input_realized] at paired
  rw [input_realized]
  unfold referenceElectronicEnergy
  simp only [energy,mul_sub,Matrix.trace_sub,Complex.sub_re]
  exact sub_eq_zero.mpr paired

theorem electron_residual_retained (s : ℝ) :
    electronFlow input.joint.body.realized s=electronFlow input.joint.body.held s+
      electronFlow input.joint.body.inheritedResidual s+electronFlow input.joint.body.newNumericalResidual s := by
  have source : input.joint.body.realized=input.joint.body.held+
      input.joint.body.inheritedResidual+input.joint.body.newNumericalResidual := by
    rw [input_body]
    exact Runtime.source_output_realization
  rw [source]
  simp only [electronFlow,map_add]

theorem electron_junctions (rho : Matrix Basis Basis ℂ) :
    electronFlow rho (onTime 0)=rho ∧ electronFlow rho (onTime duration)=rho ∧
    electronFlow rho (offTime 0)=rho ∧ electronFlow rho (offTime duration)=rho := by
  rcases ramp_endpoints with ⟨a,b,_,_,e,f,_,_⟩
  rw [a,b,e,f,electron_flow_zero]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem electronic_control_endpoints :
    electronHamiltonian (onRate 0)=referenceElectronicHamiltonian ∧
    electronHamiltonian (onRate duration)=0 ∧
    electronHamiltonian (offRate 0)=0 ∧
    electronHamiltonian (offRate duration)=referenceElectronicHamiltonian := by
  rcases ramp_endpoints with ⟨_,_,c,d,_,_,g,h⟩
  simp [electronHamiltonian,c,d,g,h]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
