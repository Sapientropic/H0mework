import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedConditionalResourceIncidence
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Dynamics.ConditionalLoadResourceAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource

open Collision Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

theorem response_resource_balance (current : Live.State) :
    (pcEnergyOf (bodyRead (respondNext current).joint) - pcEnergyOf (bodyRead current.joint)) +
      (donorEnergyOf (bodyRead (respondNext current).joint) - donorEnergyOf (bodyRead current.joint)) +
      (environmentEnergyOf (bodyRead (respondNext current).joint) - environmentEnergyOf (bodyRead current.joint)) +
      (boundaryEnergyOf (bodyRead (respondNext current).joint) - boundaryEnergyOf (bodyRead current.joint)) =
      responseWork current := by
  rw [responseWork_body, baseline_energy_split, baseline_energy_split]
  ring

theorem load_branch_paid (current : Live.State) :
    (pcEnergyOf (loadBlock (respondNext current)) - pcEnergyOf (loadBlock current)) +
      (environmentEnergyOf (loadBlock (respondNext current)) - environmentEnergyOf (loadBlock current)) +
      (boundaryEnergyOf (loadBlock (respondNext current)) - boundaryEnergyOf (loadBlock current)) = 0 := by
  rw [loadBlock_next]
  exact load_pce_energy_balance _ _

theorem load_branch_donor (current : Live.State) :
    donorEnergyOf (loadBlock (respondNext current)) = donorEnergyOf (loadBlock current) := by
  rw [loadBlock_next]
  exact load_donor_energy _ _

theorem supply_branch_paid (current : Live.State) :
    (pcEnergyOf (suppliedBlock (respondNext current)) - pcEnergyOf (suppliedBlock current)) +
      (donorEnergyOf (suppliedBlock (respondNext current)) - donorEnergyOf (suppliedBlock current)) = 0 := by
  rw [suppliedBlock_next]
  exact supply_energy_balance _ _

theorem supply_branch_environment (current : Live.State) :
    environmentEnergyOf (suppliedBlock (respondNext current)) = environmentEnergyOf (suppliedBlock current) := by
  rw [suppliedBlock_next]
  exact supply_environment_energy _ _

theorem response_donor_from_supply (current : Live.State) :
    donorEnergyOf (bodyRead (respondNext current).joint) - donorEnergyOf (bodyRead current.joint) =
      donorEnergyOf (suppliedBlock (respondNext current)) - donorEnergyOf (suppliedBlock current) := by
  rw [body_blocks, body_blocks, donorEnergyOf_add, donorEnergyOf_add, load_branch_donor]
  ring

theorem response_environment_from_load (current : Live.State) :
    environmentEnergyOf (bodyRead (respondNext current).joint) - environmentEnergyOf (bodyRead current.joint) =
      environmentEnergyOf (loadBlock (respondNext current)) - environmentEnergyOf (loadBlock current) := by
  rw [body_blocks, body_blocks, environmentEnergyOf_add, environmentEnergyOf_add, supply_branch_environment]
  ring

theorem responseWork_supply_boundary (current : Live.State) :
    responseWork current =
      boundaryEnergyOf (suppliedBlock (respondNext current)) - boundaryEnergyOf (suppliedBlock current) := by
  have account := response_resource_balance current
  rw [body_blocks, body_blocks, pcEnergyOf_add, pcEnergyOf_add, donorEnergyOf_add, donorEnergyOf_add,
    environmentEnergyOf_add, environmentEnergyOf_add, boundaryEnergyOf_add, boundaryEnergyOf_add] at account
  linarith [load_branch_paid current, load_branch_donor current,
    supply_branch_paid current, supply_branch_environment current]

theorem response_pc_account (current : Live.State) :
    pcEnergyOf (bodyRead (respondNext current).joint) - pcEnergyOf (bodyRead current.joint) =
      (pcEnergyOf (loadBlock (respondNext current)) - pcEnergyOf (loadBlock current)) +
        (pcEnergyOf (suppliedBlock (respondNext current)) - pcEnergyOf (suppliedBlock current)) := by
  rw [body_blocks, body_blocks, pcEnergyOf_add, pcEnergyOf_add]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
