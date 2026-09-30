import H0mework.Physics.LowEnergy.PacketFourier.Bounded
import H0mework.Physics.LowEnergy.PacketMomentum.Graph

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics PacketMomentum Stage9C.Material.SpinPair
noncomputable section

theorem phaseCurrentMap_continuous {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (input : FullMatterL2) :
    Continuous (fun pair : Position×ℝ => phaseCurrentMap map pair.1 pair.2 input) := by
  have movingH : Continuous (fun time => (evolve map time).hamiltonian input) := by
    have value (time : ℝ) : (evolve map time).hamiltonian input=spatialFlow 0 time (map.hamiltonian input) := by
      rw [← (evolve map time).hamiltonian_value positive,evolve_hamiltonian,map.hamiltonian_value positive]
    simp_rw [value]
    exact spatialFlow_stronglyContinuous 0 _
  have first : Continuous (fun pair : Position×ℝ => boundaryAction
      (spatialFlow 0 (-pair.2) (phaseShift pair.1 ((evolve map pair.2).hamiltonian input)))) :=
    boundaryAction.continuous.comp
      (flow_apply_continuous (fun pair : Position×ℝ => -pair.2) continuous_snd.neg _
        (phase_apply_continuous Prod.fst continuous_fst _ (movingH.comp continuous_snd)))
  let family (pair : Position×ℝ) := adjointEvolve map.boundary (-pair.2)
  have field : Continuous (fun pair => (family pair).field input) :=
    (adjointEvolve_field_continuous map.boundary input).comp continuous_snd.neg
  have load : Continuous (fun pair => (family pair).load input) :=
    (adjointEvolve_load_continuous map.boundary input).comp continuous_snd.neg
  have adjointH : Continuous (fun pair => ((family pair).shift pair.1).adjointHamiltonian input) :=
    adjointHamiltonian_continuous (fun pair => (family pair).shift pair.1) input
      (phase_apply_continuous Prod.fst continuous_fst _ field)
      (shift_load_continuous family Prod.fst input continuous_fst field load)
  change Continuous (fun pair : Position×ℝ => (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (spatialFlow 0 (-pair.2) (phaseShift pair.1 ((evolve map pair.2).hamiltonian input)))+
      adjointFlow pair.2 (((family pair).shift pair.1).adjointHamiltonian input)))
  exact (first.add (adjoint_apply_continuous Prod.snd continuous_snd _ adjointH)).const_smul
    (((lapse^2)⁻¹ : ℝ) : ℂ)

theorem phaseCurrentFilter_continuous (energy damping : ℝ) (positive : 0 < damping) (input : FullMatterL2) :
    Continuous (fun pair : Position×ℝ => phaseCurrentFilter energy damping positive pair.1 pair.2 input) :=
  (phaseCurrentMap_continuous (greenMap energy damping positive) positive input).const_smul
    ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
