import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Gain
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Account
open Collision Quantum Resource Propagation.Producer Load.Source
open Replenish.Registered
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def advance (input : Material) : Material :=
  { input with quantum := Live.loadNext (respondNext input.quantum) }
def output : Material := advance Replenish.material

theorem output_quantum : output.quantum=execution := rfl
theorem receiver_empty : output.momentum=0 := Replenish.receiver_empty

theorem clocks : target.localClock=15*nativeClockStep ∧ execution.localClock=16*nativeClockStep := by
  have one : target.localClock=Replenish.origin.localClock+nativeClockStep := rfl
  have two : execution.localClock=target.localClock+nativeClockStep := rfl
  rw [Replenish.origin_clock] at one
  constructor <;> linarith only [one,two]

theorem execution_joint : execution.joint=conjugation (Pointer.loadPulse (nativeClockStep : ℝ))
    (conjugation (feedbackPulse (nativeClockStep : ℝ)) Replenish.origin.joint) := by
  rw [execution,Live.loadNext_joint,target,respondNext_joint]

theorem execution_remaining : donorRemainingOf (suppliedBlock execution)+transfer=
    donorRemainingOf (suppliedBlock Replenish.origin) := execution_remaining_debit Replenish.origin

theorem full_historical_debit :
    donorRemainingOf (suppliedBlock execution)+transfer+Weak.transfer+supplyTransfer received+
      supplyTransfer receivedState=donorRemainingOf (suppliedBlock receivedState) := by
  rw [execution_remaining]
  exact Restore.Runtime.complete_debit Restore.Runtime.afterFirst

theorem execution_work :
    (Live.freeEnergy execution-Live.freeEnergy Replenish.origin)+
      (Live.entropyProduction execution-Live.entropyProduction Replenish.origin)=responseWork Replenish.origin := by
  have supply := respondNext_netAccount Replenish.origin
  have load := Live.loadNext_net_account target
  change (Live.freeEnergy target-Live.freeEnergy Replenish.origin)+
    (Live.entropyProduction target-Live.entropyProduction Replenish.origin)=_ at supply
  change (Live.freeEnergy execution-Live.freeEnergy target)+
    (Live.entropyProduction execution-Live.entropyProduction target)=0 at load
  linarith only [supply,load]

theorem full_historical_account :
    Live.freeEnergy execution+Live.entropyProduction execution=
    Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+
        Extract.pulseWork Weak.execution+responseWork Replenish.origin := by
  have inherited := Restore.Runtime.complete_account Restore.Runtime.afterFirst
  change Live.freeEnergy Replenish.origin+Live.entropyProduction Replenish.origin+
    Extract.Port.kinetic Replenish.material.momentum=_ at inherited
  rw [Replenish.receiver_empty,Extract.Port.kinetic,abs_zero,add_zero] at inherited
  linarith only [inherited,execution_work]

theorem execution_memory : oneRead execution.joint=oneRead Replenish.origin.joint := by
  rw [execution,Live.loadNext_pointer_one,target,respondNext_one]

theorem execution_balance :
    netGain+(donorEnergyOf (bodyRead execution.joint)-donorEnergyOf (bodyRead Replenish.origin.joint))+
      (environmentEnergyOf (bodyRead execution.joint)-environmentEnergyOf (bodyRead Replenish.origin.joint))+
      (boundaryEnergyOf (bodyRead execution.joint)-boundaryEnergyOf (bodyRead Replenish.origin.joint))=
        responseWork Replenish.origin := by
  have supply := response_resource_balance Replenish.origin
  change (pcEnergyOf (bodyRead target.joint)-pcEnergyOf (bodyRead Replenish.origin.joint))+
    (donorEnergyOf (bodyRead target.joint)-donorEnergyOf (bodyRead Replenish.origin.joint))+
    (environmentEnergyOf (bodyRead target.joint)-environmentEnergyOf (bodyRead Replenish.origin.joint))+
    (boundaryEnergyOf (bodyRead target.joint)-boundaryEnergyOf (bodyRead Replenish.origin.joint))=responseWork Replenish.origin at supply
  have load := load_execution_account target
  change (pcEnergyOf (bodyRead execution.joint)-pcEnergyOf (bodyRead target.joint))+
    (environmentEnergyOf (bodyRead execution.joint)-environmentEnergyOf (bodyRead target.joint))+
    (boundaryEnergyOf (bodyRead execution.joint)-boundaryEnergyOf (bodyRead target.joint))=0 at load
  have donor : donorEnergyOf (bodyRead execution.joint)=donorEnergyOf (bodyRead target.joint) := load_donor_total target
  unfold netGain
  linarith only [supply,load,donor]

theorem original_debit_strict : donorRemainingOf (suppliedBlock execution)<
    donorRemainingOf (suppliedBlock Replenish.origin) := by
  linarith only [execution_remaining,Replenish.Gain.source_transfer_positive]

theorem output_joint_changed : output.quantum.joint ≠ Replenish.origin.joint := by
  intro same
  have gain := Replenish.Gain.net_gain_positive
  change (1/2 : ℝ) < pcEnergyOf (bodyRead output.quantum.joint)-pcEnergyOf (bodyRead Replenish.origin.joint) at gain
  rw [same,sub_self] at gain
  norm_num at gain

theorem output_not_old_load : output.quantum ≠ Live.loadNext Replenish.origin := by
  intro same
  have nextClock := congrArg (fun state : Live.State => state.localClock) same
  change execution.localClock=Replenish.origin.localClock+nativeClockStep at nextClock
  rw [clocks.2,Replenish.origin_clock] at nextClock
  have positive := nativeClockStep_positive
  linarith only [nextClock,positive]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Account
