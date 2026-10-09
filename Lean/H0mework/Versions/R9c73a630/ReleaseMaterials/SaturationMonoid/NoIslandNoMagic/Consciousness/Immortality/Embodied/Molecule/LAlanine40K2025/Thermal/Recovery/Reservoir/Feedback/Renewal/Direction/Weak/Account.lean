import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Work
set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak

open Collision Resource Propagation.Producer Load.Source Load.Producer.StrictThermal Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

/-! The original weak/load sequence pays switching work, donor debit, and retained memory. -/

theorem next_pointer_memory (current : Live.State) :
    oneRead (next current).joint=oneRead current.joint := by
  rw [next_joint]
  exact blockUnitary_preserves_oneRead _ _ _

theorem next_pointer_energy (current : Live.State) :
    pointerEnergy (next current).joint=pointerEnergy current.joint := by
  unfold pointerEnergy
  rw [next_pointer_memory]

theorem next_load_block (current : Live.State) :
    loadBlock (next current)=
      Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (loadBlock current) := by
  unfold loadBlock
  rw [next_joint]
  exact controlled_block_left _ _ _

theorem full_environment (time : ℝ) (rho : Current.FullJoint) :
    controllerReduce (Quantum.conjugation (fullPulse time) rho)=
      Quantum.conjugation (Load.Recovery.Control.environmentUnitary time) (controllerReduce rho) :=
  Load.Quantum.controllerReduce_local_conjugation _ _ _

theorem next_supplied_environment (current : Live.State) :
    environmentEnergyOf (suppliedBlock (next current))=environmentEnergyOf (suppliedBlock current) := by
  rw [next_block]
  unfold environmentEnergyOf
  rw [full_environment]
  simpa only [Quantum.conjugation_apply] using
    Recovery.PreparationEnergy.commuting_energy (controllerHamiltonian 2)
      (controllerReduce (suppliedBlock current)) (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))
      (Load.Recovery.Control.environmentUnitary_commutes (nativeClockStep : ℝ))

theorem next_load_balance (current : Live.State) :
    (pcEnergyOf (loadBlock (next current))-pcEnergyOf (loadBlock current))+
      (environmentEnergyOf (loadBlock (next current))-environmentEnergyOf (loadBlock current))+
      (boundaryEnergyOf (loadBlock (next current))-boundaryEnergyOf (loadBlock current))=0 := by
  rw [next_load_block]
  exact load_pce_energy_balance _ _

theorem next_load_donor (current : Live.State) :
    donorEnergyOf (loadBlock (next current))=donorEnergyOf (loadBlock current) := by
  rw [next_load_block]
  exact load_donor_energy _ _

theorem pulse_work_body (current : Live.State) :
    pulseWork current=energy Physical.baselineHamiltonian (bodyRead (next current).joint)-
      energy Physical.baselineHamiltonian (bodyRead current.joint) := by
  rw [pulse_work_actual,Live.baselineEnergy_split,Live.baselineEnergy_split,next_pointer_energy]
  ring

theorem next_resource_balance (current : Live.State) :
    (pcEnergyOf (bodyRead (next current).joint)-pcEnergyOf (bodyRead current.joint))+
      (donorEnergyOf (bodyRead (next current).joint)-donorEnergyOf (bodyRead current.joint))+
      (environmentEnergyOf (bodyRead (next current).joint)-environmentEnergyOf (bodyRead current.joint))+
      (boundaryEnergyOf (bodyRead (next current).joint)-boundaryEnergyOf (bodyRead current.joint))=
        pulseWork current := by
  rw [pulse_work_body,baseline_energy_split,baseline_energy_split]
  ring

theorem pulse_work_boundary (current : Live.State) :
    pulseWork current=boundaryEnergyOf (suppliedBlock (next current))-
      boundaryEnergyOf (suppliedBlock current) := by
  have account := next_resource_balance current
  rw [body_blocks,body_blocks,pcEnergyOf_add,pcEnergyOf_add,donorEnergyOf_add,donorEnergyOf_add,
    environmentEnergyOf_add,environmentEnergyOf_add,boundaryEnergyOf_add,boundaryEnergyOf_add] at account
  linarith only [account,next_load_balance current,next_load_donor current,
    next_pair_balance current,next_supplied_environment current]

theorem execution_resource_balance :
    (pcEnergyOf (bodyRead execution.joint)-pcEnergyOf (bodyRead origin.joint))+
      (donorEnergyOf (bodyRead execution.joint)-donorEnergyOf (bodyRead origin.joint))+
      (environmentEnergyOf (bodyRead execution.joint)-environmentEnergyOf (bodyRead origin.joint))+
      (boundaryEnergyOf (bodyRead execution.joint)-boundaryEnergyOf (bodyRead origin.joint))=
        pulseWork origin := by
  have supply := next_resource_balance origin
  change (pcEnergyOf (bodyRead target.joint)-pcEnergyOf (bodyRead origin.joint))+
    (donorEnergyOf (bodyRead target.joint)-donorEnergyOf (bodyRead origin.joint))+
    (environmentEnergyOf (bodyRead target.joint)-environmentEnergyOf (bodyRead origin.joint))+
    (boundaryEnergyOf (bodyRead target.joint)-boundaryEnergyOf (bodyRead origin.joint))=pulseWork origin at supply
  have load : (pcEnergyOf (bodyRead execution.joint)-pcEnergyOf (bodyRead target.joint))+
      (environmentEnergyOf (bodyRead execution.joint)-environmentEnergyOf (bodyRead target.joint))+
      (boundaryEnergyOf (bodyRead execution.joint)-boundaryEnergyOf (bodyRead target.joint))=0 :=
    load_execution_account target
  have donor : donorEnergyOf (bodyRead execution.joint)=donorEnergyOf (bodyRead target.joint) :=
    load_donor_total target
  linarith only [supply,load,donor]

theorem execution_complete_account :
    Live.entropyProduction execution+Live.freeEnergy execution=
      Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+
      Live.measurementWork Live.initial+responseWork receivedState+responseWork received+pulseWork origin := by
  have parent := executed_complete_account
  change Live.entropyProduction origin+Live.freeEnergy origin=_ at parent
  linarith only [parent,execution_net_account]

theorem execution_complete_debit :
    donorRemainingOf (suppliedBlock execution)+transfer+supplyTransfer received+supplyTransfer receivedState=
      donorRemainingOf (suppliedBlock receivedState) := by
  rw [execution_remaining]
  exact two_responses_paid

theorem execution_finite_budget : transfer+supplyTransfer received+supplyTransfer receivedState ≤
    donorRemainingOf (suppliedBlock receivedState) := by
  linarith only [execution_complete_debit,(remaining_range execution).1]

theorem execution_pointer_memory : oneRead execution.joint=oneRead origin.joint := by
  rw [execution,Live.loadNext_pointer_one,target,next_pointer_memory]

theorem execution_not_reset : execution.joint ≠ sourceInitial := by
  intro same
  have kept := execution_pointer_memory
  rw [same,sourceInitial,prepared_one_read] at kept
  have positive : 0 < oneRead origin.joint := by
    rw [origin,executed_pointer_memory,received,firstState,respondNext_one,receivedState_joint]
    exact sourceTarget_one_positive
  linarith only [kept,positive]

theorem next_joint_injective (left right : Live.State)
    (same : (next left).joint=(next right).joint) : left.joint=right.joint := by
  rw [next_joint,next_joint] at same
  exact (Unitary.conjStarAlgAut ℂ PointerJoint (pointerPulse (nativeClockStep : ℝ))).injective same

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
