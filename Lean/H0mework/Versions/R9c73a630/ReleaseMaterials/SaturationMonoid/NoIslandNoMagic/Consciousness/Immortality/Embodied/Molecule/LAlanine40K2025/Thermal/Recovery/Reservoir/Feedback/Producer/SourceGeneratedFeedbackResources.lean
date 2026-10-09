import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackResourceAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource

open Collision
open scoped Matrix ComplexOrder
noncomputable section

def values (current : Live.State) : ℝ × ℝ × ℝ × ℝ :=
  (pcEnergyOf (bodyRead current.joint), donorEnergyOf (bodyRead current.joint),
    environmentEnergyOf (bodyRead current.joint), boundaryEnergyOf (bodyRead current.joint))

theorem remaining_range (current : Live.State) :
    0 ≤ donorRemainingOf (suppliedBlock current) ∧ donorRemainingOf (suppliedBlock current) ≤
      (Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.firstIndex (ι := Load.Source.PairController)) -
        Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.lastIndex (ι := Load.Source.PairController))) *
      (suppliedBlock current).trace.re :=
  donor_remaining_range _ (suppliedBlock_positive current)

theorem current_total (current : Live.State) :
    Live.baselineEnergy current = pcEnergyOf (bodyRead current.joint) + donorEnergyOf (bodyRead current.joint) +
      environmentEnergyOf (bodyRead current.joint) + boundaryEnergyOf (bodyRead current.joint) +
      pointerEnergy current.joint :=
  (Live.baselineEnergy_split current).trans
    (congrArg (fun E => E + pointerEnergy current.joint) (baseline_energy_split (bodyRead current.joint)))

theorem received_pc_paid_after_load :
    (pcEnergyOf (bodyRead firstState.joint) - pcEnergyOf (bodyRead receivedState.joint)) -
      (pcEnergyOf (loadBlock firstState) - pcEnergyOf (loadBlock receivedState)) ≤
      donorRemainingOf (suppliedBlock receivedState) := by
  have split := response_pc_account receivedState
  have paid := received_supply_paid
  dsimp only [firstState] at paid ⊢
  linarith

theorem sourceGeneratedFeedbackResources :
    type_of% received_mass_strict ∧ type_of% suppliedBlock_not_full_current ∧
    type_of% (remaining_range receivedState) ∧ type_of% received_supply_paid ∧
    type_of% received_supply_balance ∧ type_of% received_supply_environment ∧
    type_of% (load_branch_paid receivedState) ∧ type_of% (load_branch_donor receivedState) ∧
    type_of% (response_resource_balance receivedState) ∧ type_of% (responseWork_supply_boundary receivedState) ∧
    type_of% received_pc_paid_after_load ∧
    type_of% (current_total receivedState) ∧ type_of% (current_total firstState) ∧
    type_of% (response_donor_from_supply receivedState) ∧ type_of% (response_environment_from_load receivedState) :=
  ⟨received_mass_strict, suppliedBlock_not_full_current, remaining_range receivedState,
    received_supply_paid, received_supply_balance, received_supply_environment, load_branch_paid receivedState,
    load_branch_donor receivedState, response_resource_balance receivedState, responseWork_supply_boundary receivedState,
    received_pc_paid_after_load, current_total receivedState, current_total firstState,
    response_donor_from_supply receivedState, response_environment_from_load receivedState⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
