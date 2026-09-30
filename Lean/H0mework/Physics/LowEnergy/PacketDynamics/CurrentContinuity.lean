import H0mework.Physics.LowEnergy.PacketDynamics.GraphContinuity
import H0mework.Physics.LowEnergy.PacketDynamics.Bounded

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen PacketNoise Stage9C.Material.SpinPair
noncomputable section

theorem currentMap_continuous {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (shift : Position) (input : FullMatterL2) :
    Continuous (fun time => currentMap map shift time input) := by
  have movingH : Continuous (fun time => (evolve map time).hamiltonian input) := by
    have value (time : ℝ) : (evolve map time).hamiltonian input=spatialFlow 0 time (map.hamiltonian input) := by
      rw [← (evolve map time).hamiltonian_value positive,evolve_hamiltonian,map.hamiltonian_value positive]
    simp_rw [value]
    exact spatialFlow_stronglyContinuous 0 _
  have first : Continuous (fun time => boundaryAction
      (spatialFlow 0 (-time) (cosineShift shift ((evolve map time).hamiltonian input)))) := by
    apply boundaryAction.continuous.comp
    apply strong_apply_continuous (fun time => spatialFlow 0 (-time))
      (fun time => 1+|time| * sourceRate 0) (by fun_prop)
      (fun time => by simpa only [abs_neg] using spatialFlow_norm 0 (-time))
      (fun field => (spatialFlow_stronglyContinuous 0 field).comp continuous_neg)
    exact (cosineShift shift).continuous.comp movingH
  let family (time : ℝ) := adjointEvolve map.boundary (-time)
  have field : Continuous (fun time => (family time).field input) :=
    (adjointEvolve_field_continuous map.boundary input).comp continuous_neg
  have load : Continuous (fun time => (family time).load input) :=
    (adjointEvolve_load_continuous map.boundary input).comp continuous_neg
  have adjointH : Continuous (fun time => ((family time).cosine shift).adjointHamiltonian input) :=
    adjointHamiltonian_family_continuous (fun time => (family time).cosine shift) input
      ((cosineShift shift).continuous.comp field) (cosine_family_load_continuous family input shift field load)
  change Continuous (fun time => (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (spatialFlow 0 (-time) (cosineShift shift ((evolve map time).hamiltonian input)))+
      adjointFlow time (((family time).cosine shift).adjointHamiltonian input)))
  exact (first.add (adjointFlow_apply_continuous _ adjointH)).const_smul (((lapse^2)⁻¹ : ℝ) : ℂ)

theorem timeCurrentFilter_continuous (energy damping : ℝ) (positive : 0 < damping)
    (shift : Position) (input : FullMatterL2) :
    Continuous (fun time => timeCurrentFilter energy damping positive shift time input) :=
  (currentMap_continuous (greenMap energy damping positive) positive shift input).const_smul
    ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
